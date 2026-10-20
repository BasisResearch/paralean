"""Controller crash-window tests against a deterministic durable P2/P5 stand-in."""
from __future__ import annotations

import copy
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from p5lib.controller import Controller
from p5lib.task import from_dict
from p5lib.workers import WorkerResult

NAME = "P5Recovery.target"
GROUP = "a" * 64
OWNER = "0" * 32


def task():
    return from_dict({"task": {"id": "recovery-regression"},
        "controller": {"workers": 1, "max_attempts": 2},
        "targets": [{"name": NAME, "statement": "True", "file": "Target.lean"}]})


class DurableBackend:
    def __init__(self):
        self.saved = None
        self.epoch = 0
        self.head = None
        self.receipt_epoch = None
        self.owner = OWNER
        self.lost_reply = False
        self.ack_crash = False
        self.race_at_fence = False
        self.fence_calls = 0
        self.assign_calls = 0
        self.publish_calls = 0
        self.proof_calls = 0
        self.validation_error = False
        self.fence_reply_lost = False
        self.fence_requests = {}
        self.fence_request_ids = []

    def setup(self): pass
    def load_state(self): return copy.deepcopy(self.saved)
    def save_state(self, state):
        self.saved = copy.deepcopy(state)
        if self.ack_crash and state["events"][-1]["event"] == "target_validated":
            self.ack_crash = False
            raise KeyboardInterrupt("journal committed, reply lost")
        return "journal"
    def provision(self, agent, directory):
        (directory / "work").mkdir(parents=True, exist_ok=True)
    def sync(self, agent, directory): return {"metrics": {}}
    def conflicts(self): return []
    def assign_target(self, name, agent):
        self.assign_calls += 1
        self.epoch += 1
        return self.epoch
    def observe_target(self, name, agent):
        return {"name": name, "owner": self.owner, "epoch": self.epoch,
                "head": self.head, "assigned_to_agent": self.epoch > 0}
    def fence_unfinished(self, name, agent, expected_epoch, expected_head, request):
        self.fence_calls += 1
        self.fence_request_ids.append(request)
        if request in self.fence_requests:
            return self.fence_requests[request]
        if self.race_at_fence:
            self.race_at_fence = False
            self.head, self.receipt_epoch = GROUP, self.epoch
            return {"outcome": "changed", "name": name, "owner": self.owner,
                    "epoch": self.epoch, "head": self.head}
        if self.epoch != expected_epoch or self.head != expected_head:
            return {"outcome": "changed", "name": name, "owner": self.owner,
                    "epoch": self.epoch, "head": self.head}
        self.epoch += 1
        result = {"outcome": "fenced", "name": name, "owner": self.owner,
                  "epoch": self.epoch, "head": self.head}
        self.fence_requests[request] = result
        if self.fence_reply_lost:
            self.fence_reply_lost = False
            raise RuntimeError("T4 committed but reply lost")
        return result
    def publish(self, agent, directory, file, names, epoch=None):
        self.publish_calls += 1
        if epoch != self.epoch: raise RuntimeError("T1 stale epoch")
        if self.head is not None:
            raise RuntimeError("immutable group already published")
        self.head, self.receipt_epoch = GROUP, self.epoch
        if self.lost_reply:
            self.lost_reply = False
            raise RuntimeError("T1 committed but reply lost")
        return {"groups": [GROUP], "group": GROUP, "metrics": {}}
    def validate(self, names):
        if self.validation_error:
            raise RuntimeError("validator lookup unavailable")
        ok = self.head is not None and self.receipt_epoch == self.epoch
        return {"ok": ok, "targets": {names[0]: {"ok": ok,
            "group": self.head if ok else None, "head": self.head,
            "epoch": self.epoch, "owner": self.owner}}}
    def export(self, out):
        out.mkdir(parents=True, exist_ok=True)
        return {"ok": True, "groups": 1, "buildMs": 1}


def worker_ok(*args, **kwargs):
    return WorkerResult(NAME, "w0", 1, 0, 0.01, False, "mock.log")


class RecoveryRegression(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.desktop = Path(self.tmp.name) / "desktop"
        self.backend = DurableBackend()
        self.task = task()

    def test_lost_publication_reply_adopts_without_second_proof(self):
        self.backend.lost_reply = True
        with patch("p5lib.controller.run_worker", side_effect=worker_ok) as worker:
            result = Controller(self.task, self.desktop, self.backend, workers=1).run(export=False)
        self.assertEqual(result["targets"][NAME]["status"], "done")
        self.assertEqual(self.backend.epoch, self.backend.receipt_epoch)
        self.assertEqual(self.backend.publish_calls, 1)
        self.assertEqual(worker.call_count, 1)
        self.assertTrue(any(e["event"] == "publication_reply_recovered" for e in result["events"]))

    def test_journal_commit_before_ack_survives_desktop_loss(self):
        self.backend.ack_crash = True
        with patch("p5lib.controller.run_worker", side_effect=worker_ok):
            with self.assertRaises(KeyboardInterrupt):
                Controller(self.task, self.desktop, self.backend, workers=1).run(export=False)
        self.assertEqual(self.backend.saved["targets"][NAME]["status"], "done")
        shutil.rmtree(self.desktop)
        with patch("p5lib.controller.run_worker", side_effect=AssertionError("new proof forbidden")):
            result = Controller(self.task, self.desktop, self.backend, workers=1).run(recover=True, export=False)
        self.assertEqual(result["targets"][NAME]["group"], GROUP)
        self.assertEqual(self.backend.publish_calls, 1)

    def test_t1_race_against_fence_reconciles_new_head(self):
        ctl = Controller(self.task, self.desktop, self.backend, workers=1)
        state = ctl._new_state()
        self.backend.epoch = 1
        state["targets"][NAME].update(status="running", agent="w0", epoch=1,
                                      attempts=1, dispatch_head=None, fence_expected_head=None)
        self.backend.saved = copy.deepcopy(state)
        self.backend.race_at_fence = True
        with patch("p5lib.controller.run_worker", side_effect=AssertionError("new proof forbidden")):
            result = Controller(self.task, self.desktop, self.backend, workers=1).run(recover=True, export=False)
        self.assertEqual(result["targets"][NAME]["group"], GROUP)
        self.assertEqual(self.backend.epoch, 1)
        self.assertEqual(self.backend.fence_calls, 1)

    def test_historical_receipt_cannot_complete_recovered_dispatch(self):
        ctl = Controller(self.task, self.desktop, self.backend, workers=1)
        state = ctl._new_state()
        state["targets"][NAME].update(status="running", agent="w0", epoch=1,
                                      attempts=1, dispatch_head=None)
        self.backend.saved = copy.deepcopy(state)
        self.backend.receipt_epoch = 1
        self.backend.head = GROUP
        self.backend.epoch = 2  # T4 retained the old head but invalidated its receipt.
        with patch("p5lib.controller.run_worker", side_effect=AssertionError("new proof forbidden")) as worker:
            with self.assertRaisesRegex(RuntimeError, "target assignment changed outside the controller"):
                Controller(self.task, self.desktop, self.backend, workers=1).run(recover=True, export=False)
        self.assertEqual(worker.call_count, 0)
        self.assertEqual(self.backend.fence_calls, 0)
        self.assertEqual(self.backend.epoch, 2)
        self.assertNotEqual(self.backend.saved["targets"][NAME]["status"], "done")
        self.assertNotEqual(self.backend.saved["phase"], "complete")

    def test_new_head_with_validator_error_never_fences(self):
        ctl = Controller(self.task, self.desktop, self.backend, workers=1)
        state = ctl._new_state()
        self.backend.epoch = self.backend.receipt_epoch = 1
        self.backend.head = GROUP
        self.backend.validation_error = True
        state["targets"][NAME].update(status="running", agent="w0", epoch=1,
                                      attempts=1, dispatch_head=None)
        self.backend.saved = copy.deepcopy(state)
        with patch("p5lib.controller.run_worker", side_effect=AssertionError("new proof forbidden")):
            with self.assertRaisesRegex(RuntimeError, "validator lookup unavailable"):
                Controller(self.task, self.desktop, self.backend, workers=1).run(recover=True, export=False)
        self.assertEqual(self.backend.fence_calls, 0)
        self.assertEqual(self.backend.epoch, 1)
        self.assertEqual(self.backend.saved["targets"][NAME]["attempts"], 1)

    def test_fence_committed_before_reply_reuses_stable_request(self):
        ctl = Controller(self.task, self.desktop, self.backend, workers=1)
        state = ctl._new_state()
        self.backend.epoch = 1
        self.backend.fence_reply_lost = True
        state["targets"][NAME].update(status="running", agent="w0", epoch=1,
                                      attempts=1, dispatch_head=None)
        self.backend.saved = copy.deepcopy(state)
        with patch("p5lib.controller.run_worker", side_effect=worker_ok):
            with self.assertRaisesRegex(RuntimeError, "reply lost"):
                Controller(self.task, self.desktop, self.backend, workers=1).run(recover=True, export=False)
        self.assertEqual(self.backend.epoch, 2)
        planned = self.backend.saved["targets"][NAME]["fence_request"]
        self.assertEqual(self.backend.fence_request_ids, [planned])
        shutil.rmtree(self.desktop)
        with patch("p5lib.controller.run_worker", side_effect=worker_ok):
            result = Controller(self.task, self.desktop, self.backend, workers=1).run(recover=True, export=False)
        self.assertEqual(result["targets"][NAME]["status"], "done")
        self.assertEqual(self.backend.epoch, 2)
        self.assertEqual(self.backend.fence_request_ids, [planned, planned])

    def test_published_head_clears_pending_fence_across_completed_recovery(self):
        controller = Controller(self.task, self.desktop, self.backend, workers=1)
        state = controller._new_state()
        state["targets"][NAME].update(
            status="running", agent="w0", epoch=1, attempts=1,
            dispatch_head=None, fence_request="durable-fence-intent",
            fence_expected_epoch=1, fence_expected_head=None)
        self.backend.saved = copy.deepcopy(state)
        self.backend.epoch = self.backend.receipt_epoch = 1
        self.backend.head = GROUP
        with patch("p5lib.controller.run_worker", side_effect=AssertionError("new proof forbidden")) as worker:
            first = Controller(self.task, self.desktop, self.backend, workers=1).run(recover=True)
            second = Controller(self.task, self.desktop, self.backend, workers=1).run(recover=True)
        self.assertEqual(first["phase"], "complete")
        self.assertEqual(second["phase"], "complete")
        self.assertEqual(worker.call_count, 0)
        self.assertEqual(self.backend.fence_calls, 0)
        entry = self.backend.saved["targets"][NAME]
        self.assertEqual(entry["status"], "done")
        self.assertEqual(entry["group"], GROUP)
        self.assertFalse(entry["epoch_ready"])
        self.assertNotIn("fence_request", entry)
        self.assertNotIn("fence_expected_epoch", entry)
        self.assertNotIn("fence_expected_head", entry)


if __name__ == "__main__": unittest.main()
