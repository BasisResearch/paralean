"""Guards of a published rename's atomic batch: the controller bridge's capture and member
planning (impl/p4/controller_bridge.py) and the P5 backend's batch publication.

The live counterpart is test_rename_batch_live.py; mutate_rename_publication.py removes each
guard below and requires the named test to fail.
"""

from __future__ import annotations

import asyncio
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "p4"))

from controller_bridge import BridgeError, ControllerBridge  # noqa: E402
from p5lib.backend import Backend, BackendError, BackendUnresolved  # noqa: E402


def hexid(tag: str) -> str:
    return (tag.encode().hex() * 64)[:64]


FOO, LOCAL, USE, GOAL = hexid("foo"), hexid("local"), hexid("use"), hexid("goal")
BAR, LOCAL2, USE2, GOAL2 = hexid("bar"), hexid("local2"), hexid("use2"), hexid("goal2")
STAGING = "5" * 64


def group(pid, gid, names, line, deps=(), published=True):
    return {"pid": pid, "group": gid, "capsule": "c" + gid[1:], "names": names, "line": line,
            "deps": list(deps), "alreadyPublished": published}


def package(gid, names, deps=()):
    return {"group": gid, "capsule": "c" + gid[1:], "names": names, "deps": list(deps)}


class Workspace:
    def __init__(self, name: str, root: Path, file: str, text: str):
        self.name, self.root = name, root
        (root / "work").mkdir(parents=True)
        (root / "cache").mkdir()
        self.environment, self.generation = "env", 1
        self.env_overrides = {"PARALEAN_STORE": str(root / "cache")}
        self.uri = (root / "work" / file).as_uri()
        self.open_documents = {self.uri: {"version": 1, "text": text, "public_uri": self.uri}}

    def environment_digest(self):
        return self.environment


class Proxy:
    def __init__(self, *workspaces):
        self.mutation_lock = asyncio.Lock()
        self.workspaces = {ws.name: ws for ws in workspaces}
        self.client_writer = None
        self.initialize = None


class FakeBackend:
    def __init__(self):
        self.task = {"targets": [{"name": "P5.goal", "file": "B.lean"}]}
        self.agents = ["w0", "w1"]
        self.calls = []
        self.assigned = True
        self.before_commit = None

    def stage_for_capture(self, agent, package, users):
        self.calls.append(("stage", agent, package["group"], users))
        return STAGING

    def unstage(self, staging, users):
        self.calls.append(("unstage", staging, users))

    def observe_target(self, name, agent):
        self.calls.append(("observe", name, agent))
        return {"assigned_to_agent": self.assigned, "epoch": 7, "owner": "opaque"}

    def lamport_floor(self, agents):
        return 5

    def publish_batch(self, members, *, lamport_floor, precommit_guard):
        self.calls.append(("publish", members))
        if self.before_commit:
            self.before_commit()
        precommit_guard()
        return {"outcome": "committed", "batch": "b" * 64}

    def refresh_public_trust(self, agent, root):
        pass


class RenameMembersTests(unittest.IsolatedAsyncioTestCase):
    """Alice renames Ren.foo to Ren.bar; her Ren.local and Bob's Ren.use and P5.goal use it."""

    async def asyncSetUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        self.alice = Workspace("w0", root / "w0", "A.lean", "def Ren.foo := 1\ndef Ren.local := Ren.foo\n")
        self.bob = Workspace("w1", root / "w1", "B.lean", "def Ren.use := Ren.foo\n\ntheorem P5.goal : True := trivial\n")
        self.backend = FakeBackend()
        self.bridge = ControllerBridge(Proxy(self.alice, self.bob), self.backend)
        self.affected = {}
        for ws, groups in ((self.alice, [group("p-foo", FOO, ["Ren.foo"], 1), group("p-local", LOCAL, ["Ren.local"], 2, ["p-foo"])]),
                           (self.bob, [group("p-use", USE, ["Ren.use"], 1, ["p-foo"]), group("p-goal", GOAL, ["P5.goal"], 3, ["p-use"])])):
            self.affected[(ws.name, ws.uri)] = {**self.bridge._stamp(ws, ws.uri), "groups": groups, "packages": []}
        self.planned = {(ws.name, ws.uri): ws.open_documents[ws.uri]["text"].replace("Ren.foo", "Ren.bar")
                        for ws in (self.alice, self.bob)}
        # P1 lists the file's published groups the text no longer has first, then the text's.
        self.captures = {
            "w0": {"groups": [group("p-foo", FOO, ["Ren.foo"], 1), group("p-local", LOCAL, ["Ren.local"], 2),
                              group("p-bar", BAR, ["Ren.bar"], 1, published=False),
                              group("p-local2", LOCAL2, ["Ren.local"], 2, ["p-bar"], published=False)],
                   "packages": [package(BAR, ["Ren.bar"]), package(LOCAL2, ["Ren.local"], ["c" + BAR[1:]])]},
            "w1": {"groups": [group("p-use", USE, ["Ren.use"], 1), group("p-goal", GOAL, ["P5.goal"], 3),
                              group("p-use2", USE2, ["Ren.use"], 1, ["p-bar"], published=False),
                              group("p-goal2", GOAL2, ["P5.goal"], 3, ["p-use2"], published=False)],
                   "packages": [package(USE2, ["Ren.use"], ["c" + BAR[1:]]), package(GOAL2, ["P5.goal"])]},
        }
        self.captured = []

        async def capture(ws, uri, text, staging=None):
            self.captured.append((ws.name, text, staging))
            if isinstance(self.captures[ws.name], Exception):
                raise self.captures[ws.name]
            return json.loads(json.dumps(self.captures[ws.name]))
        self.bridge._capture_planned = capture

    async def asyncTearDown(self):
        self.tmp.cleanup()

    def published(self):
        return [call[1] for call in self.backend.calls if call[0] == "publish"]

    async def rename(self):
        return await self.bridge.publish_rename(self.affected, self.planned, FOO)

    async def test_members_publish_the_rename_deletion_and_dependents_in_order(self):
        result = await self.rename()
        self.assertEqual(result["outcome"], "committed")
        [members] = self.published()
        self.assertEqual([(m["kind"], m["agent"], m.get("group") or m["target"]) for m in members], [
            ("publish", "w0", BAR), ("tombstone", "w0", FOO), ("publish", "w0", LOCAL2),
            ("publish", "w1", USE2), ("publish", "w1", GOAL2)])
        self.assertEqual([m.get("replaces") for m in members if m["kind"] == "publish"],
                         [[FOO], [LOCAL], [USE], [GOAL]])
        self.assertEqual(members[3]["deps"], ["c" + BAR[1:]])

    async def test_dependents_are_captured_against_the_staged_declaration(self):
        await self.rename()
        self.assertEqual(self.captured, [("w0", self.planned[("w0", self.alice.uri)], None),
                                         ("w1", self.planned[("w1", self.bob.uri)], STAGING)])
        self.assertEqual(self.backend.calls[0], ("stage", "w0", BAR, ["w1"]))
        self.assertIn(("unstage", STAGING, ["w1"]), self.backend.calls)

    async def test_staged_records_are_removed_when_a_capture_fails(self):
        self.captures["w1"] = BridgeError("capture contains rejected declarations")
        with self.assertRaises(BridgeError):
            await self.rename()
        self.assertIn(("unstage", STAGING, ["w1"]), self.backend.calls)
        self.assertEqual(self.published(), [])

    async def test_revised_target_proof_binds_the_observed_epoch(self):
        await self.rename()
        [members] = self.published()
        self.assertEqual([(m.get("target"), m.get("epoch")) for m in members if m["kind"] == "publish"],
                         [(None, None), (None, None), (None, None), ("P5.goal", 7)])
        self.assertIn(("observe", "P5.goal", "w1"), self.backend.calls)

    async def test_target_assigned_elsewhere_refuses_before_publication(self):
        self.backend.assigned = False
        with self.assertRaisesRegex(BridgeError, "not assigned"):
            await self.rename()
        self.assertEqual(self.published(), [])

    async def test_stale_affected_capture_refuses_before_capture(self):
        self.bob.open_documents[self.bob.uri]["version"] = 2
        with self.assertRaisesRegex(BridgeError, "stale"):
            await self.rename()
        self.assertEqual((self.captured, self.published()), ([], []))

    async def test_revoked_author_refuses_the_rename(self):
        self.bob.authoring_refusal = "workspace agent key is revoked or unregistered"
        with self.assertRaisesRegex(BridgeError, "revoked"):
            await self.rename()
        self.assertEqual((self.captured, self.published()), ([], []))

    async def test_buffer_change_before_commit_refuses(self):
        self.backend.before_commit = lambda: self.bob.open_documents[self.bob.uri].update(version=2)
        with self.assertRaisesRegex(BridgeError, "expired"):
            await self.rename()

    async def test_policy_change_before_commit_refuses(self):
        current = ["p1"]
        self.bridge.policy_probe = lambda ws: current[0]
        self.bridge.policy_ids = {"w0": "p1", "w1": "p1"}
        self.bridge.policy_ready = {"w0", "w1"}
        self.backend.before_commit = lambda: current.__setitem__(0, "p2")
        with self.assertRaisesRegex(BridgeError, "store policy changed"):
            await self.rename()

    async def test_unpublished_rename_publishes_nothing(self):
        for doc in self.affected.values():
            for record in doc["groups"]:
                record["alreadyPublished"] = False
        try:
            result = await self.rename()
        except BridgeError as exc:
            self.fail(f"a rename of drafts only was refused: {exc}")
        self.assertIsNone(result)
        self.assertEqual((self.captured, self.backend.calls), ([], []))

    async def test_two_new_declarations_on_one_line_refuse(self):
        self.captures["w1"]["groups"].append(group("p-other", hexid("other"), ["Ren.other"], 3, published=False))
        self.captures["w1"]["groups"][-2], self.captures["w1"]["groups"][-1] = \
            self.captures["w1"]["groups"][-1], self.captures["w1"]["groups"][-2]
        with self.assertRaisesRegex(BridgeError, "one line"):
            await self.rename()
        self.assertEqual(self.published(), [])

    async def test_renaming_one_name_of_a_group_refuses(self):
        self.affected[("w0", self.alice.uri)]["groups"][0]["names"] = ["Ren.foo", "Ren.foo_eq"]
        self.captures["w0"]["groups"][2]["names"] = ["Ren.bar", "Ren.foo_eq"]
        with self.assertRaisesRegex(BridgeError, "one member"):
            await self.rename()
        self.assertEqual(self.published(), [])

    async def test_new_declaration_in_planned_buffer_refuses(self):
        self.captures["w1"]["groups"].append(group("p-new", hexid("new"), ["Ren.new"], 5, published=False))
        with self.assertRaisesRegex(BridgeError, "different set"):
            await self.rename()
        self.assertEqual(self.published(), [])


class PlannedCaptureTests(unittest.IsolatedAsyncioTestCase):
    """The one-shot capture worker: the document excluded from visibility, the staging ID."""

    async def asyncSetUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        self.ws = Workspace("w0", root / "w0", "A.lean", "def Ren.foo := 1\n")
        self.log = root / "env.jsonl"
        worker = root / "capture-worker"
        worker.write_text(f"""#!/usr/bin/env python3
import json, os, sys
for line in sys.stdin:
    request = json.loads(line)
    with open({str(self.log)!r}, "a") as log:
        log.write(json.dumps({{k: os.environ.get(k) for k in ("PARALEAN_VIS_EXCLUDE", "PARALEAN_BATCH")}}) + "\\n")
    print(json.dumps({{**{{k: request[k] for k in ("file", "version", "environment", "generation")}},
        "capture": {{"packages": [], "groups": [{{"pid": "p", "group": "g", "names": ["Ren.foo"], "line": 1}}]}}}}), flush=True)
""")
        worker.chmod(0o700)
        self.bridge = ControllerBridge(Proxy(self.ws), FakeBackend(), capture_binary=str(worker))

    async def asyncTearDown(self):
        await self.bridge.close()
        self.tmp.cleanup()

    def environments(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()]

    async def test_planned_capture_is_private_and_staged(self):
        await self.bridge._capture_planned(self.ws, self.ws.uri, "def Ren.bar := 1\n")
        await self.bridge._capture_planned(self.ws, self.ws.uri, "def Ren.bar := 1\n", staging=STAGING)
        self.assertEqual(self.environments(), [{"PARALEAN_VIS_EXCLUDE": "A.lean", "PARALEAN_BATCH": None},
                                               {"PARALEAN_VIS_EXCLUDE": "A.lean", "PARALEAN_BATCH": STAGING}])
        self.assertEqual(self.ws.open_documents[self.ws.uri]["text"], "def Ren.foo := 1\n")
        self.assertFalse(self.bridge.captures)

    async def test_editor_capture_excludes_its_document_from_visibility(self):
        await self.bridge.capture(self.ws, self.ws.uri, 1)
        self.assertEqual(self.environments(), [{"PARALEAN_VIS_EXCLUDE": "A.lean", "PARALEAN_BATCH": None}])


class BatchPublicationTests(unittest.TestCase):
    """Backend.publish_batch: which process signs, when the guard runs, how outcomes map."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        root = Path(self.tmp.name)
        env = {"PARALEAN_DEPLOYMENT": "test", "PARALEAN_FDB_CLUSTER": "unused", "PARALEAN_S3_ENDPOINT": "unused",
               "PARALEAN_S3_ACCESS_KEY": "unused", "PARALEAN_S3_SECRET_KEY": "unused",
               "PARALEAN_VALIDATOR": "127.0.0.1:1"}
        task = {"id": "test", "agents": ["w0", "w1"], "files": ["A.lean", "B.lean"], "sources": {},
                "targets": [{"name": "P5.goal"}]}
        self.backend = Backend(task, root / "state", env)
        self.backend.payload = {"contract_hashes": {"P5.goal": "e" * 64}}
        self.backend.paths = {"w0": root / "w0", "w1": root / "w1"}
        self.backend._start_validator = lambda: None
        self.backend.sync = lambda agent, directory: self.calls.append(("sync", agent))
        self.calls = []
        self.outcomes = [{"outcome": "committed", "batch": "b" * 64, "fresh": True}]
        self.guarded = []

        def bridge(*args, env=None):
            self.calls.append((args[0], args, env))
            if args[0] == "batch-validate":
                return {"accepted": True, "batch": "b" * 64}
            if args[0] == "batch-sign":
                return {"signed": 1}
            outcome = self.outcomes.pop(0) if self.outcomes else {"outcome": "unresolved", "reason": "unscripted"}
            if isinstance(outcome, Exception):
                raise outcome
            return outcome
        self.backend._bridge = bridge
        self.members = [
            {"kind": "publish", "agent": "w0", "file": "A.lean", "group": BAR, "capsule": "c" + BAR[1:], "deps": [],
             "names": ["Ren.bar"], "replaces": [FOO]},
            {"kind": "tombstone", "agent": "w0", "target": FOO},
            {"kind": "publish", "agent": "w1", "file": "B.lean", "group": GOAL2, "capsule": "c" + GOAL2[1:],
             "deps": ["c" + BAR[1:]], "names": ["P5.goal"], "replaces": [GOAL], "target": "P5.goal", "epoch": 7},
        ]

    def publish(self):
        return self.backend.publish_batch(self.members, lamport_floor=3,
                                          precommit_guard=lambda: self.calls.append(("guard",)))

    def published(self):
        """A publication that must succeed: a refusal is an assertion failure here."""
        try:
            return self.publish()
        except BackendError as exc:
            self.fail(f"batch publication failed: {exc}")

    def commands(self):
        return [call[0] for call in self.calls]

    def test_each_workspace_signs_its_members_with_its_own_key_file(self):
        self.published()
        signs = [(call[1][call[1].index("--ws") + 1], call[2]) for call in self.calls if call[0] == "batch-sign"]
        self.assertEqual(signs, [("w0", {"PARALEAN_KEYS": str(self.backend.paths["w0"] / "keys.json")}),
                                 ("w1", {"PARALEAN_KEYS": str(self.backend.paths["w1"] / "keys.json")})])
        # The controller's own key file signs the intent and jobs and runs T12.
        self.assertEqual([call[2] for call in self.calls if call[0] in ("batch-validate", "batch-publish")], [None, None])

    def test_precommit_guard_runs_after_signing_and_before_publication(self):
        self.published()
        self.assertEqual(self.commands(), ["batch-validate", "batch-sign", "batch-sign", "guard", "batch-publish",
                                           "sync", "sync"])

    def test_spec_binds_the_frozen_target_and_dispatch_epoch(self):
        captured = {}
        original = self.backend._bridge

        def bridge(*args, env=None):
            if args[0] == "batch-validate":
                captured.update(json.loads(Path(args[args.index("--spec") + 1]).read_text()))
            return original(*args, env=env)
        self.backend._bridge = bridge
        self.published()
        self.assertEqual([row["target"] for row in captured["members"] if row["kind"] == "publish"],
                         [None, {"name": "P5.goal", "epoch": 7, "statement_hash": "e" * 64}])
        self.assertEqual(captured["lamport_floor"], 3)

    def test_validator_rejection_raises_before_signing(self):
        original = self.backend._bridge
        self.backend._bridge = lambda *args, env=None: ({"accepted": False, "reason": "kernel"}
                                                        if args[0] == "batch-validate" else original(*args, env=env))
        with self.assertRaisesRegex(BackendError, "rejected"):
            self.publish()
        self.assertEqual(self.commands(), [])

    def test_target_member_needs_its_frozen_contract(self):
        self.backend.payload = {"contract_hashes": {}}
        with self.assertRaisesRegex(BackendError, "frozen contract"):
            self.publish()
        self.assertEqual(self.commands(), [])

    def test_unregistered_member_workspace_refuses(self):
        self.members[1]["agent"] = "w9"
        with self.assertRaisesRegex(BackendError, "unregistered"):
            self.publish()
        self.assertEqual(self.commands(), [])

    def test_refusal_raises_and_is_not_retried(self):
        self.outcomes = [{"outcome": "refused", "reason": "guard: not the owner of P5.goal"}]
        with self.assertRaisesRegex(BackendError, "not the owner") as caught:
            self.publish()
        self.assertNotIsInstance(caught.exception, BackendUnresolved)
        self.assertEqual(self.commands().count("batch-publish"), 1)

    def test_unknown_outcome_is_resolved_by_running_the_same_batch(self):
        self.outcomes = [BackendError("paralean-p5-store batch-publish failed (exit 2)"),
                         {"outcome": "committed", "batch": "b" * 64, "fresh": False}]
        self.assertEqual(self.published()["fresh"], False)
        runs = [call[1] for call in self.calls if call[0] == "batch-publish"]
        self.assertEqual(len(runs), 2)
        self.assertEqual(runs[0], runs[1])

    def test_unresolved_after_retries_raises_and_keeps_the_batch(self):
        self.outcomes = [{"outcome": "unresolved", "reason": "unresolved after 60 attempts"}] * 3
        with self.assertRaises(BackendUnresolved):
            self.publish()
        kept = list((self.backend.state_dir / "unresolved-batches").iterdir())
        self.assertEqual(len(kept), 1)
        self.assertNotIn("sync", self.commands())


class LamportFloorTests(unittest.TestCase):
    def test_floor_covers_clock_and_records_without_following_links(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            env = {"PARALEAN_DEPLOYMENT": "t", "PARALEAN_FDB_CLUSTER": "u", "PARALEAN_S3_ENDPOINT": "u",
                   "PARALEAN_S3_ACCESS_KEY": "u", "PARALEAN_S3_SECRET_KEY": "u", "PARALEAN_VALIDATOR": "127.0.0.1:1"}
            backend = Backend({"id": "t", "agents": ["w0"], "files": [], "targets": []}, root / "state", env)
            copy = root / "w0"
            (copy / "cache/p3/records").mkdir(parents=True)
            (copy / "state.json").write_text(json.dumps({"lamport": 4}))
            (copy / "cache/p3/records/m-1.json").write_text(json.dumps({"lamport": 9}))
            outside = root / "outside.json"
            outside.write_text(json.dumps({"lamport": 99}))
            os.symlink(outside, copy / "cache/p3/records/m-2.json")
            backend.paths = {"w0": copy}
            with self.assertRaises(OSError):
                backend.lamport_floor(["w0"])
            (copy / "cache/p3/records/m-2.json").unlink()
            self.assertEqual(backend.lamport_floor(["w0"]), 9)


if __name__ == "__main__":
    unittest.main()
