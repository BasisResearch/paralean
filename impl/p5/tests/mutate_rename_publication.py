#!/usr/bin/env python3
"""Remove each published-rename guard in an isolated module and require its test to fail.

Like mutate_editor_bridge.py: one source replacement per guard in controller_bridge.py or
backend.py, loaded as its own module; only an assertion failure of the named test in
test_rename_publication.py counts (an error does not).
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from impl.p5.tests import test_rename_publication as tests  # noqa: E402

BRIDGE_SOURCE = (ROOT / "impl/p4/controller_bridge.py").read_text()
BACKEND_SOURCE = (ROOT / "impl/p5/p5lib/backend.py").read_text()
BRIDGE_CASES = [
    ("rename_affected_stamp",
     'if any(doc.get(k) != v for k, v in stamp.items()):\n                raise BridgeError("an affected capture is stale")',
     'if False:\n                raise BridgeError("an affected capture is stale")',
     tests.RenameMembersTests, "test_stale_affected_capture_refuses_before_capture"),
    ("rename_authoring", "            self._assert_authoring(ws)\n            stamps[(name, uri)] = stamp",
     "            stamps[(name, uri)] = stamp", tests.RenameMembersTests, "test_revoked_author_refuses_the_rename"),
    ("rename_staged_dependents", "planned[(name, uri)], staging=staging)", "planned[(name, uri)], staging=None)",
     tests.RenameMembersTests, "test_dependents_are_captured_against_the_staged_declaration"),
    ("rename_unstage", "                await asyncio.to_thread(self.backend.unstage, staging, users)",
     "                pass", tests.RenameMembersTests, "test_staged_records_are_removed_when_a_capture_fails"),
    ("rename_tombstone", "            if not kept:\n                members.append",
     "            if False:\n                members.append",
     tests.RenameMembersTests, "test_members_publish_the_rename_deletion_and_dependents_in_order"),
    ("rename_target_owner",
     'if observation.get("assigned_to_agent") is not True or not isinstance(observation.get("epoch"), int):',
     'if not isinstance(observation.get("epoch"), int):',
     tests.RenameMembersTests, "test_target_assigned_elsewhere_refuses_before_publication"),
    ("rename_target_binding", 'member["target"], member["epoch"] = proven[0], observation["epoch"]', "pass",
     tests.RenameMembersTests, "test_revised_target_proof_binds_the_observed_epoch"),
    ("rename_precommit_stamp", "                self._assert_current(workspaces[name], uri, stamp)", "                pass",
     tests.RenameMembersTests, "test_buffer_change_before_commit_refuses"),
    ("rename_precommit_policy", "                self._assert_store_policy(each)\n",
     "",
     tests.RenameMembersTests, "test_policy_change_before_commit_refuses"),
    ("rename_published_only",
     'if not any(record.get("alreadyPublished") is True for doc in affected.values() for record in doc["groups"]):',
     "if False:", tests.RenameMembersTests, "test_unpublished_rename_publishes_nothing"),
    ("rename_same_line", 'if line in by_line and by_line[line].get("alreadyPublished") is not True:', "if False:",
     tests.RenameMembersTests, "test_two_new_declarations_on_one_line_refuse"),
    ("rename_whole_group", "if kept and kept != set(map(str, previous[\"names\"])):", "if False:",
     tests.RenameMembersTests, "test_renaming_one_name_of_a_group_refuses"),
    ("rename_same_declarations",
     'if any(line not in old and record.get("alreadyPublished") is not True for line, record in new.items()):',
     "if False:", tests.RenameMembersTests, "test_new_declaration_in_planned_buffer_refuses"),
    ("planned_capture_visibility",
     'env = {**os.environ, **ws.env_overrides, "PARALEAN_VIS_EXCLUDE": stamp["file"]}',
     "env = {**os.environ, **ws.env_overrides}",
     tests.PlannedCaptureTests, "test_planned_capture_is_private_and_staged"),
    ("planned_capture_staging", '            env["PARALEAN_BATCH"] = staging', "            pass",
     tests.PlannedCaptureTests, "test_planned_capture_is_private_and_staged"),
    ("editor_capture_visibility",
     'env={**os.environ, **ws.env_overrides, "PARALEAN_VIS_EXCLUDE": stamp["file"]},',
     "env={**os.environ, **ws.env_overrides},",
     tests.PlannedCaptureTests, "test_editor_capture_excludes_its_document_from_visibility"),
]
BACKEND_CASES = [
    ("batch_sign_own_keys", 'env={"PARALEAN_KEYS": str(self._copy(agent) / "keys.json")})', "env=None)",
     tests.BatchPublicationTests, "test_each_workspace_signs_its_members_with_its_own_key_file"),
    ("batch_precommit_guard", "            if precommit_guard is not None:\n                precommit_guard()\n            try:",
     "            try:", tests.BatchPublicationTests, "test_precommit_guard_runs_after_signing_and_before_publication"),
    ("batch_resolve_rerun", "for _ in range(self.BATCH_RESOLVE_ATTEMPTS):", "for _ in range(1):",
     tests.BatchPublicationTests, "test_unknown_outcome_is_resolved_by_running_the_same_batch"),
    ("batch_refusal_final", '            if result.get("outcome") == "refused":\n', '            if False:\n',
     tests.BatchPublicationTests, "test_refusal_raises_and_is_not_retried"),
    ("batch_committed_only", 'if result.get("outcome") == "committed":', "if True:",
     tests.BatchPublicationTests, "test_unresolved_after_retries_raises_and_keeps_the_batch"),
    ("batch_validator_verdict",
     '            if not checked.get("accepted"):\n                reason = str(checked.get("reason") or "no reason returned")[:500]\n'
     '                raise BackendError(f"trusted validator rejected batch member',
     '            if False:\n                reason = str(checked.get("reason") or "no reason returned")[:500]\n'
     '                raise BackendError(f"trusted validator rejected batch member',
     tests.BatchPublicationTests, "test_validator_rejection_raises_before_signing"),
    ("batch_target_contract", "if name not in names or not frozen:", "if False:",
     tests.BatchPublicationTests, "test_target_member_needs_its_frozen_contract"),
    ("batch_target_binding", 'target = {"name": name, "epoch": epoch, "statement_hash": frozen}', "pass",
     tests.BatchPublicationTests, "test_spec_binds_the_frozen_target_and_dispatch_epoch"),
    ("batch_registered_agent",
     '        if agent not in self.agents:\n            raise BackendError(f"unregistered agent: {agent}")\n        directory = self.paths.get(agent)',
     "        directory = self.paths.get(agent)",
     tests.BatchPublicationTests, "test_unregistered_member_workspace_refuses"),
    ("lamport_floor_no_follow", 'texts += [_read_source(records, f.name) for f in records.glob("*.json")]',
     'texts += [f.read_text() for f in records.glob("*.json")]',
     tests.LamportFloorTests, "test_floor_covers_clock_and_records_without_following_links"),
]


def run(test_class, method, log: Path) -> unittest.TestResult:
    with open(log, "w") as stream:
        return unittest.TextTestRunner(stream=stream).run(unittest.TestSuite([test_class(method)]))


def main() -> int:
    original = {name: getattr(tests, name) for name in ("ControllerBridge", "BridgeError", "Backend",
                                                         "BackendError", "BackendUnresolved")}
    with tempfile.TemporaryDirectory() as tmp:
        baseline = unittest.defaultTestLoader.loadTestsFromModule(tests)
        with open(Path(tmp) / "baseline.log", "w") as stream:
            if not unittest.TextTestRunner(stream=stream).run(baseline).wasSuccessful():
                raise AssertionError("baseline rename publication tests failed before mutation")
        killed = 0
        for source, cases, package in ((BRIDGE_SOURCE, BRIDGE_CASES, None), (BACKEND_SOURCE, BACKEND_CASES, "p5lib")):
            for index, (name, needle, replacement, test_class, method) in enumerate(cases):
                if source.count(needle) != 1:
                    raise AssertionError(f"guard anchor changed: {name}")
                path = Path(tmp) / f"{name}.py"
                path.write_text(source.replace(needle, replacement, 1))
                module_name = f"{package}.mutant_{index}" if package else f"mutant_{name}"
                spec = importlib.util.spec_from_file_location(module_name, path)
                assert spec and spec.loader
                module = importlib.util.module_from_spec(spec)
                spec.loader.exec_module(module)
                if package:
                    tests.Backend, tests.BackendError = module.Backend, module.BackendError
                    tests.BackendUnresolved = module.BackendUnresolved
                else:
                    tests.ControllerBridge, tests.BridgeError = module.ControllerBridge, module.BridgeError
                result = run(test_class, method, Path(tmp) / f"{name}.log")
                for attribute, value in original.items():
                    setattr(tests, attribute, value)
                if not result.failures or result.errors:
                    raise AssertionError(f"guard removal escaped test: {name}\n" + (Path(tmp) / f"{name}.log").read_text())
                killed += 1
                print(f"detected {name} by {method}")
        print(f"{killed}/{len(BRIDGE_CASES) + len(BACKEND_CASES)} guard mutations detected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
