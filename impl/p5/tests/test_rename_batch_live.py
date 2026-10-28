"""A published cross-workspace rename, end to end against live services.

The router's ``paralean/renameTransaction`` runs for real, with two P5 working copies, the
controller bridge, the P5 backend, the store bridge's batch commands, a real validator,
P1 capture (stock Lean) and this instance's store. Only the LSP workers' answers
(definition and rename edits, as Lean's rename would give) and the dependency inventory
are supplied here: in a P3 copy every task file is rendered, so the router's own inventory
would hold each published group twice (once as source, once as another copy's `remote%`
element) and refuse, as W5's probe did.

Alice (w0) publishes ``Ren.foo``; Bob (w1) publishes ``Ren.use := Ren.foo + 1`` and the
frozen target ``Ren.goal``, whose proof uses ``Ren.use``. Renaming ``Ren.foo`` must
publish ``Ren.bar``, delete ``Ren.foo``'s position and revise Bob's declarations in one
batch, with each member certificate signed by its own workspace, or change nothing.

Needs a private instance: source .runs/ap/p5-env.sh (store up, bridges and P1 built).
"""

from __future__ import annotations

import asyncio
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

P5 = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(P5))
sys.path.insert(0, str(P5.parent / "p4"))

from controller_bridge import ControllerBridge  # noqa: E402
from lsp import Proxy, file_uri  # noqa: E402
from p5lib.backend import Backend  # noqa: E402
from rename_transaction import source_digest  # noqa: E402

LIVE = (os.environ.get("PARALEAN_INSTANCE", "").startswith(("ap-", "p5-"))
        and all(os.access(os.environ.get(v, ""), os.X_OK)
                for v in ("PARALEAN_P5_BRIDGE", "PARALEAN_P5_FAULT_BRIDGE", "PARALEAN_PLR",
                          "PARALEAN_P3_BIN", "PARALEAN_BIN")))
GOAL = "theorem Ren.goal : True := (fun _ => trivial) Ren.use\n"


def edit_at(text: str, needle: str, new: str) -> list[dict]:
    """The LSP edits replacing every occurrence of ``needle`` (one per line here)."""
    edits = []
    for line, content in enumerate(text.splitlines()):
        start = content.find(needle)
        if start >= 0:
            edits.append({"range": {"start": {"line": line, "character": start},
                                    "end": {"line": line, "character": start + len(needle)}},
                          "newText": new})
    return edits


class LiveWorkspace:
    """A router workspace over a provisioned P5 copy; its Lean worker answers from a script."""

    def __init__(self, name: str, root: Path, docs: dict[str, str]):
        self.name, self.root, self.worker_root = name, root, root
        self.environment, self.generation = "live-environment", 1
        self.open_documents = {uri: {"version": 1, "text": text, "public_uri": uri} for uri, text in docs.items()}
        # As attach_p5 pins them.
        self.env_overrides = {"PARALEAN_STORE": str(root / "cache"), "PARALEAN_WORK_ROOT": str(root / "work"),
                              "PARALEAN_KEYS": str(root / "keys.json"), "PARALEAN_TRUST": str(root / "trust.json"),
                              "PARALEAN_VISIBILITY": "1"}
        self.answers: dict[tuple[str, str], dict] = {}
        self.pending: dict = {}

    def environment_digest(self) -> str:
        return self.environment

    def refresh_environment(self) -> bool:
        return False

    async def request(self, message, client_id, document=None, expected_version=None):
        future = asyncio.get_running_loop().create_future()
        future.set_result(self.answers[(message["method"], document)])
        worker_id = len(self.pending) + 1
        self.pending[worker_id] = (client_id, document, expected_version, self.generation,
                                   self.environment, future, None, message["method"])
        return worker_id, future


class FixtureInventory(ControllerBridge):
    """The real bridge, with the dependency inventory captured here from the open buffers."""

    inventory: dict

    def rename_inventory(self) -> dict:
        return copy.deepcopy(self.inventory)


@unittest.skipUnless(LIVE, "source .runs/ap/p5-env.sh with the ap-p5 store up and the bridges built")
class PublishedRenameLive(unittest.IsolatedAsyncioTestCase):
    @classmethod
    def setUpClass(cls):
        base = Path(os.environ.get("TMPDIR") or tempfile.gettempdir())
        cls.run_dir = Path(tempfile.mkdtemp(prefix="p5-rename-live-", dir=base))
        cls.deployment = f"p5rename-{int(time.time())}-{os.getpid()}"
        os.environ["PARALEAN_DEPLOYMENT"] = cls.deployment
        task = {"id": "rename-live", "name": "published rename", "agents": ["w0", "w1"],
                "files": ["A.lean", "B.lean"], "sources": {},
                "targets": [{"name": "Ren.goal", "statement": "True", "file": "B.lean", "owner": "w1", "deps": []}]}
        cls.backend = backend = Backend(task, cls.run_dir)
        backend.setup()
        for agent in ("w0", "w1"):
            backend.provision(agent, cls.run_dir / agent)
        backend._start_validator()
        # Before: foo by Alice; use and the target proof by Bob, each published singly.
        (cls.run_dir / "w0/work/A.lean").write_text("def Ren.foo : Nat := 1\n")
        backend._ws("publish", "w0", cls.run_dir / "w0", "A.lean")
        backend.sync("w1", cls.run_dir / "w1")
        bob = cls.run_dir / "w1/work/B.lean"
        bob.write_text("def Ren.use : Nat := Ren.foo + 1\n")
        backend._ws("publish", "w1", cls.run_dir / "w1", "B.lean")
        cls.epoch = backend.assign_target("Ren.goal", "w1")
        # The editor buffer's layout: a package ID covers its source position.
        bob.write_text("def Ren.use : Nat := Ren.foo + 1\n\n" + GOAL)
        cls.goal_before = backend.publish("w1", cls.run_dir / "w1", "B.lean", ["Ren.goal"], cls.epoch)["validated"]["group"]
        cls.head = backend.observe_target("Ren.goal", "w1")["head"]

    @classmethod
    def tearDownClass(cls):
        cls.backend.close()
        os.environ.pop("PARALEAN_DEPLOYMENT", None)

    async def asyncSetUp(self):
        run = self.run_dir
        self.uri_a, self.uri_b = file_uri(run / "w0/work/A.lean"), file_uri(run / "w1/work/B.lean")
        if not hasattr(type(self), "texts"):
            type(self).texts = {"w0": "def Ren.foo : Nat := 1\n",
                                "w1": "def Ren.use : Nat := Ren.foo + 1\n\n" + GOAL}
        self.alice = LiveWorkspace("w0", run / "w0", {self.uri_a: self.texts["w0"]})
        self.bob = LiveWorkspace("w1", run / "w1", {self.uri_b: self.texts["w1"]})
        self.proxy = Proxy({}, ["unused"])
        self.proxy.workspaces = {"w0": self.alice, "w1": self.bob}
        self.sent = []

        async def send(message):
            self.sent.append(message)

        async def replay(*args):
            pass
        self.proxy.send, self.proxy.deliver_change = send, replay
        bridge = FixtureInventory(self.proxy, self.backend, capture_binary=os.environ["PARALEAN_BIN"],
                                  policy_probe=lambda ws: "live-policy")
        bridge.policy_ready = {"w0", "w1"}
        bridge.policy_ids = {"w0": "live-policy", "w1": "live-policy"}
        for event in bridge.policy_events.values():
            event.set()
        self.proxy.bridge = self.bridge = bridge
        documents = []
        for ws, uri in ((self.alice, self.uri_a), (self.bob, self.uri_b)):
            stamp = bridge._stamp(ws, uri)
            capture = await bridge._capture_planned(ws, uri, ws.open_documents[uri]["text"])
            documents.append({**stamp, "packages": capture["packages"], "groups": capture["groups"]})
        bridge.inventory = {"complete": True, "documents": documents, "missing": []}
        self.groups = {name: record for doc in documents for record in doc["groups"]
                       for name in record["names"]}

    def rename(self, old: str, new: str) -> dict:
        """The router's rename request, with the edits Lean's rename gives each worker."""
        text_a, text_b = self.texts["w0"], self.texts["w1"]
        for ws, uri, text in ((self.alice, self.uri_a, text_a), (self.bob, self.uri_b, text_b)):
            line = next(i for i, content in enumerate(text.splitlines()) if old in content)
            column = text.splitlines()[line].find(old)
            ws.anchor = {"line": line, "character": column + len(old) - 1}
            ws.answers[("textDocument/rename", uri)] = {"result": {"changes": {uri: edit_at(text, old, new)}}}
        definition = {"result": {"uri": self.uri_a, "range": {
            "start": {"line": 0, "character": 4}, "end": {"line": 0, "character": 4 + len(old)}}}}
        self.alice.answers[("textDocument/definition", self.uri_a)] = definition
        self.bob.answers[("textDocument/definition", self.uri_b)] = definition
        return {"id": 7, "params": {"uri": self.uri_a, "position": self.alice.anchor,
                "group": self.groups[old]["group"], "newName": new,
                "anchors": [{"uri": self.uri_a, "position": self.alice.anchor},
                            {"uri": self.uri_b, "position": self.bob.anchor}]}}

    def published(self) -> int:
        """Records the store delivers to a working copy (each pull is a fresh read)."""
        return self.backend.sync("w0", self.run_dir / "w0")["pull"][-1]["available"]

    def assert_unchanged(self, before: int):
        self.assertIn("error", self.sent[-1], self.sent[-1])
        self.assertEqual(self.alice.open_documents[self.uri_a]["text"], self.texts["w0"])
        self.assertEqual(self.bob.open_documents[self.uri_b]["text"], self.texts["w1"])
        self.assertEqual([self.alice.open_documents[self.uri_a]["version"],
                          self.bob.open_documents[self.uri_b]["version"]], [1, 1])
        self.assertEqual(self.published(), before, "a refused batch exposes no member")
        self.assertEqual(self.backend.observe_target("Ren.goal", "w1")["head"], self.head)

    def reassign(self, agent: str) -> None:
        type(self).epoch = self.backend.assign_target("Ren.goal", agent)

    def with_guard(self, before_commit):
        """Run ``before_commit`` right before the batch transaction (after validation)."""
        original = self.backend.publish_batch

        def publish_batch(members, *, lamport_floor, precommit_guard=None):
            def guard():
                before_commit()
                if precommit_guard is not None:
                    precommit_guard()
            return original(members, lamport_floor=lamport_floor, precommit_guard=guard)
        self.backend.publish_batch = publish_batch
        self.addCleanup(lambda: delattr(self.backend, "publish_batch"))

    async def test_1_stale_owner_on_one_member_refuses_the_whole_rename(self):
        before = self.published()
        # The target moves to Alice after the batch was validated: Bob's proof is stale.
        self.with_guard(lambda: self.reassign("w0"))
        await self.proxy.rename_transaction(self.rename("Ren.foo", "Ren.bar"))
        self.assertIn("not the owner of Ren.goal", self.sent[-1]["error"]["message"])
        self.reassign("w1")
        self.assert_unchanged(before)

    async def test_2_unresolved_outcome_changes_nothing_and_resolves_as_not_committed(self):
        before = self.published()
        self.backend.bridge = os.environ["PARALEAN_P5_FAULT_BRIDGE"]
        self.backend.env["PARALEAN_P5_TEST_FAULT"] = "unresolved"
        try:
            await self.proxy.rename_transaction(self.rename("Ren.foo", "Ren.bar"))
        finally:
            self.backend.bridge = os.environ["PARALEAN_P5_BRIDGE"]
            del self.backend.env["PARALEAN_P5_TEST_FAULT"]
        self.assertIn("unresolved", self.sent[-1]["error"]["message"])
        self.assert_unchanged(before)
        # Resolving the kept batch after its target moved: T12 rechecks every guard and
        # refuses, so the unknown outcome resolves as not committed.
        kept = sorted((self.run_dir / "unresolved-batches").iterdir())[-1]
        self.reassign("w0")
        certs = [arg for path in sorted(kept.glob("certs-*.json")) for arg in ("--certs", str(path))]
        resolved = self.backend._bridge("batch-publish", "--batch", str(kept / "batch.json"), *certs)
        self.assertEqual(resolved["outcome"], "refused", resolved)
        status = self.backend._bridge("batch-status", "--batch", str(kept / "batch.json"))
        self.assertEqual((status["committed"], status["visible"]), (False, 0), status)
        self.reassign("w1")
        self.assert_unchanged(before)

    async def test_3_rename_publishes_every_member_then_commits_buffers(self):
        before = self.published()
        await self.proxy.rename_transaction(self.rename("Ren.foo", "Ren.bar"))
        reply = self.sent[-1]
        self.assertIn("result", reply, reply)
        publication = reply["result"]["publication"]
        self.assertEqual(publication["outcome"], "committed")
        new_a = self.texts["w0"].replace("Ren.foo", "Ren.bar")
        new_b = self.texts["w1"].replace("Ren.foo", "Ren.bar")
        self.assertEqual(self.alice.open_documents[self.uri_a]["text"], new_a)
        self.assertEqual(self.bob.open_documents[self.uri_b]["text"], new_b)
        # bar, foo's deletion, use' and the target proof's revision: one batch.
        self.assertEqual(len(publication["members"]), 4, publication)
        self.assertEqual(self.published(), before + 4)
        checked = self.backend.validate(["Ren.goal"])
        self.assertTrue(checked["ok"], checked)
        self.assertNotEqual(checked["targets"]["Ren.goal"]["group"], self.goal_before)
        self.assertNotEqual(self.backend.observe_target("Ren.goal", "w1")["head"], self.head)
        type(self).goal_before = checked["targets"]["Ren.goal"]["group"]
        type(self).head = self.backend.observe_target("Ren.goal", "w1")["head"]
        type(self).texts = {"w0": new_a, "w1": new_b}

    async def test_4_crash_after_commit_resolves_as_committed(self):
        before = self.published()
        once = self.run_dir / "fault-once"
        self.backend.bridge = os.environ["PARALEAN_P5_FAULT_BRIDGE"]
        self.backend.env.update(PARALEAN_P5_TEST_FAULT="crash-after-commit", PARALEAN_P5_TEST_FAULT_ONCE=str(once))
        try:
            await self.proxy.rename_transaction(self.rename("Ren.bar", "Ren.baz"))
        finally:
            self.backend.bridge = os.environ["PARALEAN_P5_BRIDGE"]
            for key in ("PARALEAN_P5_TEST_FAULT", "PARALEAN_P5_TEST_FAULT_ONCE"):
                del self.backend.env[key]
        reply = self.sent[-1]
        self.assertIn("publication", reply.get("result", {}), reply)
        self.assertTrue(once.exists(), "the fault fired")
        # The first run committed and crashed; the re-run found the batch record.
        self.assertEqual((reply["result"]["publication"]["outcome"], reply["result"]["publication"]["fresh"]),
                         ("committed", False))
        self.assertEqual(self.published(), before + 4)
        self.assertEqual(self.bob.open_documents[self.uri_b]["text"], self.texts["w1"].replace("Ren.bar", "Ren.baz"))
        type(self).texts = {name: text.replace("Ren.bar", "Ren.baz") for name, text in self.texts.items()}

    # -------------------------------------------------- the store bridge's own guards

    def store_bridge(self, *args: str, keys: Path | None = None) -> tuple[int, dict, str]:
        env = {**self.backend._runtime_env(self.backend.env),
               "PARALEAN_KEYS": str(keys or self.run_dir / "keys.json")}
        proc = subprocess.run([os.environ["PARALEAN_P5_BRIDGE"], *args], env=env, text=True,
                              capture_output=True, timeout=600)
        lines = proc.stdout.strip().splitlines()
        return proc.returncode, json.loads(lines[-1]) if lines else {}, proc.stderr

    def validate(self, name: str, members: list[dict]) -> tuple[int, dict, str, Path]:
        spec, out = self.run_dir / f"{name}-spec.json", self.run_dir / f"{name}-batch.json"
        spec.write_text(json.dumps({"request": name, "lamport_floor": 0, "members": members}))
        rc, value, err = self.store_bridge("batch-validate", "--spec", str(spec), "--out", str(out),
                                     "--validator", os.environ["PARALEAN_VALIDATOR"])
        return rc, value, err, out

    def goal_member(self, ws: str, epoch: int) -> dict:
        goal = self.groups["Ren.goal"]
        return {"kind": "publish", "ws": ws, "cache": str(self.run_dir / "w1/cache"), "group": goal["group"],
                "capsule": goal["capsule"], "deps": [], "file": "B.lean", "names": ["Ren.goal"], "replaces": [],
                "target": {"name": "Ren.goal", "epoch": epoch,
                           "statement_hash": self.backend.payload["contract_hashes"]["Ren.goal"]}}

    async def renamed_batch(self, request: str) -> Path:
        """A validated, unsigned batch renaming Alice's declaration (nothing is published)."""
        current = self.bridge._declarations(self.bridge.inventory["documents"][0])[1]
        new = "Ren.qux"
        planned = await self.bridge._capture_planned(self.alice, self.uri_a,
                                                     self.texts["w0"].replace(current["names"][0], new))
        package = next(p for p in planned["packages"] if new in p["names"])
        rc, value, err, out = self.validate(request, [
            {"kind": "publish", "ws": "w0", "cache": str(self.run_dir / "w0/cache"), "group": package["group"],
             "capsule": package["capsule"], "deps": package["deps"], "file": "A.lean", "names": [new],
             "replaces": [current["group"]], "target": None},
            {"kind": "tombstone", "ws": "w0", "target": current["group"]}])
        self.assertEqual((rc, value.get("accepted")), (0, True), err)
        return out

    def assert_refused(self, result: tuple, reason: str):
        self.assertNotEqual(result[0], 0, result)
        self.assertIn(reason, result[2])

    async def test_guard_validate_refuses_a_target_of_another_workspace(self):
        epoch = self.backend.observe_target("Ren.goal", "w1")["epoch"]
        self.assert_refused(self.validate("other-owner", [self.goal_member("w0", epoch)]),
                            "target Ren.goal is owned by another workspace")

    async def test_guard_validate_refuses_a_stale_dispatch_epoch(self):
        epoch = self.backend.observe_target("Ren.goal", "w1")["epoch"]
        self.assert_refused(self.validate("stale-epoch", [self.goal_member("w1", epoch - 1)]),
                            "target Ren.goal epoch changed after controller dispatch")

    async def test_guard_validate_refuses_replacing_another_workspaces_declaration(self):
        member = {**self.goal_member("w0", 0), "names": ["Ren.other"], "target": None,
                  "replaces": [self.groups["Ren.use"]["group"]]}
        self.assert_refused(self.validate("other-replaced", [member]),
                            "replaces only its own workspace's declaration")

    async def test_guard_validate_refuses_deleting_another_workspaces_declaration(self):
        self.assert_refused(self.validate("other-deleted", [
            {"kind": "tombstone", "ws": "w0", "target": self.groups["Ren.use"]["group"]}]),
                            "deletes only its own workspace's declaration")

    async def test_guard_sign_takes_only_the_workspaces_own_key_file(self):
        batch = await self.renamed_batch("own-keys")
        own = self.run_dir / "w0/keys.json"
        self.assert_refused(self.store_bridge("batch-sign", "--batch", str(batch), "--ws", "w0",
                                        "--out", str(batch.with_suffix(".controller")), keys=self.run_dir / "keys.json"),
                            "holding no other seed")
        rc, value, err = self.store_bridge("batch-sign", "--batch", str(batch), "--ws", "w0",
                                     "--out", str(batch.with_suffix(".certs")), keys=own)
        self.assertEqual((rc, value.get("signed")), (0, 2), err)

    async def test_guard_sign_refuses_an_intent_not_signed_by_the_controller(self):
        batch = await self.renamed_batch("forged-intent")
        data = json.loads(batch.read_text())
        intent = data["intent"]
        data["intent"] = intent[:-2] + ("00" if intent[-2:] != "00" else "01")
        forged = batch.with_name("forged-intent-forged.json")
        forged.write_text(json.dumps(data))
        self.assert_refused(self.store_bridge("batch-sign", "--batch", str(forged), "--ws", "w0",
                                        "--out", str(forged.with_suffix(".certs")), keys=self.run_dir / "w0/keys.json"),
                            "batch intent is not signed by the controller")

    async def test_guard_sign_refuses_a_job_bound_to_another_batch(self):
        first, second = await self.renamed_batch("bound-one"), await self.renamed_batch("bound-two")
        data, other = json.loads(first.read_text()), json.loads(second.read_text())
        # A genuine job, receipt and marker of the same package, from another batch.
        data["members"][0] = other["members"][0]
        swapped = first.with_name("bound-swapped.json")
        swapped.write_text(json.dumps(data))
        self.assert_refused(self.store_bridge("batch-sign", "--batch", str(swapped), "--ws", "w0",
                                        "--out", str(swapped.with_suffix(".certs")), keys=self.run_dir / "w0/keys.json"),
                            "member job is not bound to this batch")


if __name__ == "__main__":
    unittest.main()
