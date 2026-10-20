"""Guard mutations at the editor capture to receipt-publication boundary."""

from __future__ import annotations

import asyncio
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import threading
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "p4"))

from controller_bridge import BridgeError, ControllerBridge, attach_p5, authoritative_policy_probe, policy_feed
from lsp import EnvironmentInvalid, Proxy as RouterProxy, Workspace as RouterWorkspace
from p5lib.backend import Backend as P5Backend
from p5lib.lsp_provision import SshEndpoint, lsp_workspace_args, provision_ssh_copy


class Workspace:
    def __init__(self, root):
        self.name = "w0"
        self.root = root
        self.environment_label = "policy-a"
        self.env_overrides = {"PARALEAN_STORE": str(root / "cache")}
        self.environment = self.environment_digest()
        self.generation = 1
        self.open_documents = {}
        self.process = object()
        self.replaced = 0
        self.fenced = 0
        self.fail_start_once = False
        self.ready = asyncio.Event()
        self.ready.set()

    def environment_digest(self):
        digest = hashlib.sha256(self.environment_label.encode())
        trust = self.env_overrides.get("PARALEAN_TRUST")
        if trust:
            digest.update(Path(trust).read_bytes())
        return digest.hexdigest()

    def refresh_environment(self):
        digest = self.environment_digest()
        changed = digest != self.environment
        self.environment = digest
        return changed

    async def replace_worker(self):
        if self.fail_replace_once:
            self.fail_replace_once = False
            raise RuntimeError("injected SSH restart failure")
        self.replaced += 1
        self.generation += 1

    async def start(self):
        if self.fail_start_once:
            self.fail_start_once = False
            raise RuntimeError("injected SSH restart failure")
        self.process = object()
        self.generation += 1
        self.ready.set()

    async def fence_policy(self):
        self.fenced += 1
        self.generation += 1
        self.ready.clear()
        self.process = None

    def stop_process(self):
        self.process = None


class Proxy:
    def __init__(self, ws):
        self.mutation_lock = asyncio.Lock()
        self.workspaces = {ws.name: ws}
        self.client_writer = None
        self.initialize = None
        self.dropped = 0
        self.stopping = False

    def drop_sessions(self, ws):
        self.dropped += 1

    def debug(self, *items):
        pass


class Backend:
    def __init__(self):
        self.task = {"targets": [{"name": "P5.answer", "file": "A.lean"}]}
        self.agents = ["w0"]
        self.calls = 0
        self.before_commit = None
        self.assigned = True

    def observe_target(self, name, owner):
        return {"assigned_to_agent": self.assigned, "owner": "opaque-workspace-id", "epoch": 4}

    def publish(self, owner, root, file, targets, epoch, *, precommit_guard):
        self.calls += 1
        if self.before_commit:
            self.before_commit()
        precommit_guard()
        return {"groups": ["group-a"], "receipt": "trusted",
                "validated": {"ok": True, "group": "group-a"}}

    def validate(self, names):
        return {"ok": True, "targets": {"P5.answer": {"ok": True, "group": "group-a"}}}

    def close(self):
        pass

    def refresh_public_trust(self, agent, root):
        source = getattr(self, "trust_source", None)
        if source is not None:
            (root / "trust.json").write_bytes(Path(source).read_bytes())


class BridgeTests(unittest.IsolatedAsyncioTestCase):
    async def asyncSetUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name) / "w0"
        (self.root / "work").mkdir(parents=True)
        (self.root / "cache").mkdir()
        (self.root / "work" / "A.lean").write_text("theorem P5.answer : True := by trivial\n")
        self.ws = Workspace(self.root)
        self.uri = (self.root / "work" / "A.lean").as_uri()
        self.ws.open_documents[self.uri] = {"version": 1, "text": "theorem P5.answer : True := by trivial\n"}
        self.backend = Backend()
        self.bridge = ControllerBridge(Proxy(self.ws), self.backend)
        self.bridge.captures[("w0", self.uri)] = {
            **self.bridge._stamp(self.ws, self.uri), "packages": [{"names": ["P5.answer"]}],
            "groups": [{"names": ["P5.answer"], "group": "private-group"}]}

    async def asyncTearDown(self):
        await self.bridge.close()
        self.tmp.cleanup()

    async def test_explicit_current_capture_publishes_once(self):
        result = await self.bridge.publish(self.ws, self.uri, 1, "P5.answer", "w0", 4, policy="frozen-target")
        self.assertEqual(result["group"], "group-a")
        self.assertEqual(self.backend.calls, 1)
        self.assertFalse(self.bridge.captures)

    async def test_each_stamp_mutation_refuses_publication(self):
        mutations = [
            lambda: self.ws.open_documents[self.uri].update(version=2),
            lambda: self.ws.open_documents[self.uri].update(text="theorem P5.answer : True := by sorry\n"),
            lambda: setattr(self.ws, "generation", 2),
            lambda: setattr(self.ws, "environment_label", "policy-b"),
            lambda: self.ws.open_documents.clear(),
        ]
        for mutate in mutations:
            with self.subTest(mutate=mutate):
                original = self.ws.open_documents.get(self.uri, {}).copy()
                generation = self.ws.generation
                label = self.ws.environment_label
                mutate()
                with self.assertRaises(BridgeError):
                    await self.bridge.publish(self.ws, self.uri, 1, "P5.answer", "w0", 4, policy="frozen-target")
                self.assertEqual(self.backend.calls, 0)
                self.ws.open_documents[self.uri] = original
                self.ws.generation = generation
                self.ws.environment_label = label

    async def test_policy_and_assignment_guards(self):
        with self.assertRaises(BridgeError):
            await self.bridge.publish(self.ws, self.uri, 1, "P5.answer", "w0", 4)
        for args in [
            ("P5.answer", "w0", 3, "frozen-target"),
            ("P5.answer", "w9", 4, "frozen-target"),
            ("P5.other", "w0", 4, "frozen-target"),
            ("P5.answer", "w0", 4, "unreviewed-draft"),
        ]:
            with self.subTest(args=args), self.assertRaises(BridgeError):
                await self.bridge.publish(self.ws, self.uri, 1, *args[:3], policy=args[3])
        self.assertEqual(self.backend.calls, 0)
        self.bridge.captures[("w0", self.uri)]["packages"] = [{"names": ["Other"]}]
        with self.assertRaisesRegex(BridgeError, "does not contain"):
            await self.bridge.publish(self.ws, self.uri, 1, "P5.answer", "w0", 4, policy="frozen-target")
        self.assertEqual(self.backend.calls, 0)
        self.bridge.captures[("w0", self.uri)]["packages"] = [{"names": ["P5.answer"]}]
        self.backend.assigned = False
        with self.assertRaises(BridgeError):
            await self.bridge.publish(self.ws, self.uri, 1, "P5.answer", "w0", 4, policy="frozen-target")
        self.assertEqual(self.backend.calls, 0)

    async def test_registered_other_owner_cannot_publish_this_workspace_buffer(self):
        self.backend.agents.append("w1")
        with self.assertRaisesRegex(BridgeError, "outside the frozen task"):
            await self.bridge.publish(self.ws, self.uri, 1, "P5.answer", "w1", 4,
                                      policy="frozen-target")
        self.assertEqual(self.backend.calls, 0)

    async def test_mutation_after_validation_aborts_before_commit(self):
        self.backend.before_commit = lambda: setattr(self.ws, "generation", 2)
        with self.assertRaises(BridgeError):
            await self.bridge.publish(self.ws, self.uri, 1, "P5.answer", "w0", 4, policy="frozen-target")
        self.assertEqual(self.backend.calls, 1)
        self.assertIn(("w0", self.uri), self.bridge.captures)

    async def test_external_source_edit_after_validation_aborts_commit(self):
        source = self.root / "work" / "A.lean"
        self.backend.before_commit = lambda: source.write_text("theorem P5Lsp.one : True := by sorry\n")
        with self.assertRaisesRegex(BridgeError, "working source changed"):
            await self.bridge.publish(self.ws, self.uri, 1, "P5.answer", "w0", 4, policy="frozen-target")
        self.assertEqual(self.backend.calls, 1)

    async def test_live_policy_change_after_validation_aborts_commit(self):
        current = ["p1"]
        self.bridge.policy_probe = lambda ws: current[0]
        await self.bridge.poll_policy()
        self.bridge.captures[("w0", self.uri)] = {
            **self.bridge._stamp(self.ws, self.uri),
            "packages": [{"names": ["P5.answer"]}], "groups": []}
        self.backend.before_commit = lambda: current.__setitem__(0, "p2")
        with self.assertRaisesRegex(BridgeError, "store policy changed"):
            await self.bridge.publish(self.ws, self.uri, 1, "P5.answer", "w0", 4, policy="frozen-target")
        self.assertEqual(self.backend.calls, 1)

    async def test_capture_worker_is_private_and_restarts_on_generation_change(self):
        fake = self.root / "capture-worker"
        fake.write_text("""#!/usr/bin/env python3
import json, sys
for line in sys.stdin:
    request = json.loads(line)
    rejected = 'sorry' in request['text']
    reply = {k: request[k] for k in ('file', 'version', 'environment', 'generation')}
    if 'STAMP_BAD' in request['text']:
        reply['version'] += 1
    reply.update(registry='r', reusedCommands=0, newCommands=1,
                 capture={'packages': [] if rejected else [{'names': ['P5.answer'],
                           'group': 'private-group'}], 'groups': [],
                          'rejected': ['bad'] if rejected else []})
    sys.stdout.write(json.dumps(reply) + '\\n')
    sys.stdout.flush()
""")
        fake.chmod(0o700)
        self.bridge.capture_binary = str(fake)
        self.bridge.captures.clear()
        first = await self.bridge.capture(self.ws, self.uri, 1)
        self.assertEqual(first["packages"][0]["group"], "private-group")
        self.assertEqual(self.backend.calls, 0)
        old_worker = self.bridge.workers[("w0", self.uri)]
        self.ws.open_documents[self.uri].update(version=2, text="theorem P5.answer : True := by sorry\n")
        self.bridge.observe(self.ws, self.uri, "textDocument/didChange")
        with self.assertRaises(BridgeError):
            await self.bridge.capture(self.ws, self.uri, 2)
        self.assertFalse(self.bridge.captures)
        self.assertIs(old_worker, self.bridge.workers[("w0", self.uri)])
        self.ws.open_documents[self.uri].update(version=3, text="theorem P5.answer : True := by trivial\n")
        self.ws.generation += 1
        second = await self.bridge.capture(self.ws, self.uri, 3)
        self.assertEqual(second["generation"], 2)
        self.assertIsNot(old_worker, self.bridge.workers[("w0", self.uri)])
        self.ws.open_documents[self.uri].update(version=4, text="STAMP_BAD\n")
        with self.assertRaisesRegex(BridgeError, "mismatched stamp"):
            await self.bridge.capture(self.ws, self.uri, 4)

    async def test_policy_push_invalidates_capture_and_replaces_worker(self):
        current = ["store-policy-a"]
        self.bridge.policy_probe = lambda ws: current[0]
        self.bridge.proxy.initialize = {"method": "initialize"}
        await self.bridge.poll_policy()
        self.assertEqual(self.ws.fenced, 1)
        self.assertIsNotNone(self.ws.process)
        self.assertFalse(self.bridge.captures)
        self.bridge.captures[("w0", self.uri)] = {
            **self.bridge._stamp(self.ws, self.uri), "packages": [], "groups": []}
        current[0] = "store-policy-b"
        await self.bridge.poll_policy()
        self.assertEqual(self.ws.fenced, 2)
        self.assertIsNotNone(self.ws.process)
        self.assertFalse(self.bridge.captures)
        dropped_before_unavailable = self.bridge.proxy.dropped
        current[0] = ""
        await self.bridge.poll_policy()
        self.assertNotIn("w0", self.bridge.policy_ready)
        self.assertEqual(self.bridge.proxy.dropped, dropped_before_unavailable + 1)
        self.bridge.captures[("w0", self.uri)] = {
            **self.bridge._stamp(self.ws, self.uri),
            "packages": [{"names": ["P5.answer"]}], "groups": []}
        with self.assertRaises(BridgeError):
            await self.bridge.publish(self.ws, self.uri, 1, "P5.answer", "w0", 4, policy="frozen-target")
        self.assertEqual(self.backend.calls, 0)

    async def test_live_revocation_changes_policy_with_zero_groups(self):
        revoked = [False]

        def run(argv, **kwargs):
            if argv[1] == "policy-state":
                body = {"validators": [{"key": "a" * 64, "revoked": revoked[0]}],
                        "policies": ["policy"], "checkers": ["checker"]}
            elif argv[1] == "pull":
                body = {"stale": False, "available": 0}
            else:
                self.fail(f"unexpected authoritative query: {argv}")
            return subprocess.CompletedProcess(argv, 0, json.dumps(body), "")

        with patch("controller_bridge.subprocess.run", side_effect=run):
            before = authoritative_policy_probe(self.ws)
            revoked[0] = True
            after = authoritative_policy_probe(self.ws)
        self.assertNotEqual(before, after)

    async def test_failed_policy_restart_fails_closed_then_recovers(self):
        current = ["p1"]
        self.bridge.policy_probe = lambda ws: current[0]
        self.bridge.proxy.initialize = {"method": "initialize"}
        await self.bridge.poll_policy()
        self.bridge.proxy.dropped = 0
        self.bridge.captures[("w0", self.uri)] = {
            **self.bridge._stamp(self.ws, self.uri),
            "packages": [{"names": ["P5.answer"]}], "groups": []}
        self.ws.fail_start_once = True
        current[0] = "p2"
        feed = asyncio.create_task(policy_feed(self.bridge, interval=0.3))
        try:
            for _ in range(50):
                if self.bridge.proxy.dropped:
                    break
                await asyncio.sleep(0.01)
            self.assertGreaterEqual(self.bridge.proxy.dropped, 2)
            self.assertNotIn("w0", self.bridge.policy_ready)
            self.assertEqual(self.bridge.policy_ids["w0"], "unavailable")
            self.assertFalse(self.bridge.captures)
            self.assertIsNone(self.ws.process)
            for _ in range(80):
                if "w0" in self.bridge.policy_ready and self.ws.process is not None:
                    break
                await asyncio.sleep(0.01)
            self.assertIn("w0", self.bridge.policy_ready)
            self.assertIsNotNone(self.ws.process)
            self.assertGreater(self.ws.generation, 1)
        finally:
            self.bridge.proxy.stopping = True
            feed.cancel()
            with self.assertRaises(asyncio.CancelledError):
                await feed

    async def test_remote_sync_fences_worker_until_copy_finishes(self):
        current = ["p1"]
        entered = threading.Event()
        released = threading.Event()
        self.bridge.policy_probe = lambda ws: current[0]
        self.bridge.proxy.initialize = {"method": "initialize"}
        await self.bridge.poll_policy()
        self.bridge.captures[("w0", self.uri)] = {
            **self.bridge._stamp(self.ws, self.uri),
            "packages": [{"names": ["P5.answer"]}], "groups": []}

        def sync(ws):
            entered.set()
            if not released.wait(2):
                raise TimeoutError("test remote copy timed out")

        self.bridge.remote_sync = sync
        current[0] = "p2"
        poll = asyncio.create_task(self.bridge.poll_policy())
        try:
            self.assertTrue(await asyncio.to_thread(entered.wait, 1))
            self.assertNotIn("w0", self.bridge.policy_ready)
            self.assertFalse(self.bridge.policy_events["w0"].is_set())
            self.assertIsNone(self.ws.process)
            self.assertFalse(self.bridge.captures)
            self.assertGreater(self.bridge.proxy.dropped, 0)
            self.assertFalse(self.ws.ready.is_set())
        finally:
            released.set()
            await poll
        self.assertIn("w0", self.bridge.policy_ready)
        self.assertTrue(self.bridge.policy_events["w0"].is_set())
        self.assertIsNotNone(self.ws.process)
        self.assertTrue(self.ws.ready.is_set())

    async def test_policy_probe_fences_requests_while_pulling_registry(self):
        self.bridge.policy_probe = lambda ws: "p1"
        await self.bridge.poll_policy()
        entered = threading.Event()
        released = threading.Event()

        def slow_probe(ws):
            entered.set()
            if not released.wait(2):
                raise TimeoutError("test policy probe timed out")
            return "p1"

        self.bridge.policy_probe = slow_probe
        poll = asyncio.create_task(self.bridge.poll_policy())
        try:
            self.assertTrue(await asyncio.to_thread(entered.wait, 1))
            self.assertNotIn("w0", self.bridge.policy_ready)
            self.assertFalse(self.bridge.policy_events["w0"].is_set())
        finally:
            released.set()
            await poll
        self.assertIn("w0", self.bridge.policy_ready)
        self.assertTrue(self.bridge.policy_events["w0"].is_set())

    async def test_controller_trust_source_rotation_pushes_local_and_remote_environment(self):
        source = self.root.parent / "controller-trust.json"
        source.write_text('{"key":"old"}')
        trust = self.root / "trust.json"
        trust.write_bytes(source.read_bytes())
        self.backend.trust_source = source
        self.ws.env_overrides["PARALEAN_TRUST"] = str(trust)
        self.ws.environment = self.ws.environment_digest()
        self.bridge.policy_probe = lambda ws: "same-store-policy"
        self.bridge.proxy.initialize = {"method": "initialize"}
        mirrored = []
        self.bridge.remote_sync = lambda ws: mirrored.append(trust.read_bytes())
        await self.bridge.poll_policy()
        self.bridge.captures[("w0", self.uri)] = {
            **self.bridge._stamp(self.ws, self.uri), "packages": [], "groups": []}
        old_generation = self.ws.generation
        source.write_text('{"key":"rotated"}')
        await self.bridge.poll_policy()
        self.assertEqual(trust.read_bytes(), source.read_bytes())
        self.assertEqual(mirrored[-1], source.read_bytes())
        self.assertFalse(self.bridge.captures)
        self.assertGreater(self.ws.generation, old_generation)
        self.assertIn("w0", self.bridge.policy_ready)

    async def test_attach_pins_task_credentials_over_inherited_environment(self):
        self.ws.root = self.root.resolve()
        state = self.ws.root.parent
        task_path = state / "TASK.toml"
        task_path.write_text("unused by fake loader")
        self.ws.base_env_overrides = dict(self.ws.env_overrides)

        class Task:
            workers = 1
            def as_dict(self):
                return {"id": "test", "workers": 1, "targets": []}

        class AttachedBackend:
            def __init__(self, task, state_dir, env=None):
                self.env = {**os.environ, **(env or {})}
                self.state_dir = state_dir
            def setup(self):
                (self.state_dir / "keys.json").write_text("worker keys")
                (self.state_dir / "trust.json").write_text("public trust")
            def provision(self, agent, root):
                (root / "trust.json").write_text("public trust")
            def close(self):
                pass

        with patch.dict(os.environ, {"PARALEAN_KEYS": "/outside/keys.json",
                                  "PARALEAN_TRUST": "/outside/trust.json"}), \
             patch("p5lib.task.load", return_value=Task()), \
             patch("p5lib.backend.Backend", AttachedBackend):
            attached = attach_p5(self.bridge.proxy, task_path, state)
        self.assertEqual(attached.backend.env["PARALEAN_KEYS"], str(state / "keys.json"))
        self.assertEqual(attached.backend.env["PARALEAN_TRUST"], str(state / "trust.json"))
        self.assertEqual(self.ws.env_overrides["PARALEAN_TRUST"], str(self.ws.root / "trust.json"))
        self.assertEqual(self.ws.env_overrides["PARALEAN_STORE"], str(self.ws.root / "cache"))
        self.assertEqual(self.ws.bound_env, {
            "PARALEAN_STORE": str(self.ws.root / "cache"),
            "PARALEAN_WORK_ROOT": str(self.ws.root / "work"),
            "PARALEAN_KEYS": str(self.ws.root / "keys.json"),
            "PARALEAN_TRUST": str(self.ws.root / "trust.json"),
            "PARALEAN_VISIBILITY": "1",
        })
        original_refresh = self.ws.refresh_environment

        def hostile_env_file():
            self.ws.env_overrides["PARALEAN_STORE"] = "/outside/cache"
            return original_refresh()

        with patch.dict(os.environ, {"PARALEAN_KEYS": "/outside/keys.json",
                                  "PARALEAN_TRUST": "/outside/trust.json"}), \
             patch("p5lib.task.load", return_value=Task()), \
             patch("p5lib.backend.Backend", AttachedBackend), \
             patch.object(self.ws, "refresh_environment", side_effect=hostile_env_file), \
             self.assertRaisesRegex(BridgeError, "overrides a pinned worker path"):
            attach_p5(self.bridge.proxy, task_path, state)

    async def test_router_defers_worker_output_during_policy_probe(self):
        router = RouterProxy({"w0": self.ws}, ["unused"])
        self.ws.proxy = router
        self.ws.worker_root = self.ws.root
        self.ws.pending = {}
        router.bridge = ControllerBridge(router)
        router.bridge.policy_ready.add("w0")
        delivered = []
        async def send(message):
            delivered.append(message)
        router.send = send
        event = router.bridge.policy_events["w0"]
        future = asyncio.get_running_loop().create_future()
        self.ws.pending[7] = (9, None, None, self.ws.generation, self.ws.environment,
                              future, None, "textDocument/hover")
        response = asyncio.create_task(router.worker_response(self.ws, {"id": 7, "result": "hover"}))
        diagnostic = asyncio.create_task(router.worker_message(self.ws, {
            "jsonrpc": "2.0", "method": "textDocument/publishDiagnostics",
            "params": {"uri": self.uri, "version": 1, "diagnostics": []}}, self.ws.generation))
        await asyncio.sleep(0)
        self.assertFalse(future.done())
        self.assertFalse(delivered)
        event.set()
        await asyncio.gather(response, diagnostic)
        self.assertEqual((await future)["result"], "hover")
        self.assertTrue(any(message.get("method") == "textDocument/publishDiagnostics"
                            for message in delivered))

    async def test_rename_inventory_is_complete_only_for_current_captures(self):
        self.assertTrue(self.bridge.rename_inventory()["complete"])
        (self.root / "work" / "B.lean").write_text("def B := 1\n")
        inventory = self.bridge.rename_inventory()
        self.assertFalse(inventory["complete"])
        self.assertEqual(inventory["missing"][0]["reason"], "not open")
        self.bridge.observe(self.ws, self.uri, "textDocument/didChange")
        self.assertEqual(len(self.bridge.rename_inventory()["missing"]), 2)
        new_uri = (self.root / "work" / "Unsaved.lean").as_uri()
        self.ws.open_documents[new_uri] = {"version": 1, "text": "def Unsaved := 1\n"}
        missing = self.bridge.rename_inventory()["missing"]
        self.assertEqual(len(missing), 3)
        self.assertTrue(any(x["uri"] == new_uri for x in missing))


class ProvisionTests(unittest.TestCase):
    def test_workspace_env_reload_cannot_replace_bound_p5_settings(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for key in ("PARALEAN_STORE", "PARALEAN_WORK_ROOT", "PARALEAN_KEYS",
                        "PARALEAN_TRUST", "PARALEAN_VISIBILITY"):
                with self.subTest(key=key):
                    worker = root / key
                    worker.mkdir()
                    env_file = worker / "env.json"
                    env_file.write_text("{}")
                    pinned = {
                        "PARALEAN_STORE": str(worker / "cache"),
                        "PARALEAN_WORK_ROOT": str(worker / "work"),
                        "PARALEAN_KEYS": str(worker / "keys.json"),
                        "PARALEAN_TRUST": str(worker / "trust.json"),
                        "PARALEAN_VISIBILITY": "1",
                    }
                    proxy = RouterProxy({}, ["unused"])
                    ws = RouterWorkspace(proxy, "w0", worker, "policy-a", pinned, env_file)
                    proxy.workspaces["w0"] = ws
                    ws.bound_env = pinned.copy()
                    proxy.sessions["session"] = (ws, None)
                    env_file.write_text(json.dumps({key: "/outside/changed"}))
                    with self.assertRaises(EnvironmentInvalid):
                        ws.refresh_environment()
                    self.assertEqual(ws.environment, "invalid-configuration")
                    self.assertFalse(proxy.sessions)

    def test_backend_provision_refreshes_public_trust(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            workspace = root / "w0"
            workspace.mkdir()
            (workspace / "agent").write_text("w0")
            source = root / "trust.json"
            source.write_text('{"public":"first"}')
            backend = P5Backend.__new__(P5Backend)
            backend.agents = ["w0"]
            backend.paths = {}
            backend.payload = {"sources": {}}
            backend.task = {"files": []}
            backend.env = {"PARALEAN_TRUST": str(source)}
            backend._restore_keys = lambda payload: None
            backend.provision("w0", workspace)
            self.assertTrue((workspace / "trust.json").is_file())
            self.assertEqual((workspace / "trust.json").read_bytes(), source.read_bytes())
            source.write_text('{"public":"rotated"}')
            backend.provision("w0", workspace)
            self.assertEqual((workspace / "trust.json").read_bytes(), source.read_bytes())

    def test_local_and_ssh_roots_use_distinct_transport(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            local = root / "w0"
            (local / "work").mkdir(parents=True)
            (local / "cache").mkdir()
            (local / "work" / "A.lean").write_text("def A := 1\n")
            identity = root / "id"
            known = root / "known_hosts"
            identity.write_text("private test key")
            known.write_text("pinned test host")
            ssh = SshEndpoint("aws-dev", "worker", 22955, identity, known, Path("/srv/p5/w0"))
            local_args = lsp_workspace_args("w0", local, ["lean", "--server"])
            remote_args = lsp_workspace_args("w0", local, ["lean", "--server"], ssh)
            self.assertIn("w0=" + str(local.resolve()), local_args)
            self.assertIn("w0=/srv/p5/w0", remote_args)
            self.assertIn("StrictHostKeyChecking=yes", " ".join(remote_args))
            calls = []
            provision_ssh_copy(local, ssh, run=lambda args, **kwargs: calls.append((args, kwargs)))
            self.assertEqual([c[0][0] for c in calls], ["ssh", "rsync", "rsync", "rsync", "rsync"])
            self.assertTrue(all(c[1].get("stdin") == subprocess.DEVNULL for c in calls))
            self.assertTrue(all("--delete" not in c[0] for c in calls[1:] if "keys.json" in " ".join(c[0])))

    def test_existing_unmarked_remote_root_is_preserved(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            local = root / "local"
            (local / "work").mkdir(parents=True)
            (local / "cache").mkdir()
            identity = root / "id"
            known = root / "known_hosts"
            identity.write_text("key")
            known.write_text("host")
            remote = root / "existing"
            remote.mkdir()
            sentinel = remote / "do-not-delete"
            sentinel.write_text("retained")
            endpoint = SshEndpoint("aws-dev", "worker", 22955, identity, known, remote)
            calls = []

            def run(argv, **kwargs):
                calls.append(argv)
                if argv[0] == "ssh":
                    subprocess.run(["bash", "-c", argv[-1]], check=True)
                else:
                    self.fail("rsync reached an unmarked remote root")

            with self.assertRaises(subprocess.CalledProcessError):
                provision_ssh_copy(local, endpoint, run=run)
            self.assertEqual(sentinel.read_text(), "retained")
            self.assertEqual(len(calls), 1)

    def test_public_trust_is_mirrored_into_remote_worker_root(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            local = root / "w0"
            (local / "work").mkdir(parents=True)
            (local / "cache").mkdir()
            (local / "trust.json").write_text('{"public":"ring"}')
            (local / "keys.json").write_text('{"workspace":"private"}')
            identity = root / "id"
            known = root / "known_hosts"
            identity.write_text("key")
            known.write_text("host")
            endpoint = SshEndpoint("aws-dev", "worker", 22955, identity, known,
                                   Path("/srv/p5/w0"))
            calls = []
            env_contents = []

            def run(argv, **kwargs):
                self.assertEqual(kwargs.get("stdin"), subprocess.DEVNULL)
                calls.append(argv)
                if argv[0] == "rsync" and any(".lsp-env-" in part for part in argv):
                    env_contents.append(Path(argv[-2]).read_text())

            provision_ssh_copy(local, endpoint, run=run)
            self.assertTrue(any("trust.json" in " ".join(argv) for argv in calls))
            self.assertEqual(len(env_contents), 1)
            self.assertIn("PARALEAN_TRUST=/srv/p5/w0/trust.json", env_contents[0])


if __name__ == "__main__":
    unittest.main()
