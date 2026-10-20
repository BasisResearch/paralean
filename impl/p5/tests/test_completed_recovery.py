"""Completed task recovery must recheck current heads and the stock export."""

from __future__ import annotations

import copy
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from p5lib.controller import Controller
from p5lib.task import from_dict


def task():
    return from_dict({
        "task": {"id": "completed-recovery"},
        "controller": {"workers": 1},
        "targets": [{"name": "P5.proof", "statement": "True", "file": "Proof.lean"}],
    })


class Backend:
    def __init__(self):
        self.saved = None
        self.current_group = "group-1"
        self.contract_ok = True
        self.validate_calls = 0
        self.export_calls = 0
        self.export_ok = True
        self.change_head_on_export = False

    def setup(self):
        pass

    def load_state(self):
        return copy.deepcopy(self.saved)

    def save_state(self, state):
        self.saved = copy.deepcopy(state)
        return "catalog-1"

    def provision(self, agent, directory):
        (directory / "work").mkdir(parents=True, exist_ok=True)

    def validate(self, names):
        self.validate_calls += 1
        return {"ok": self.contract_ok,
                "targets": {name: {"ok": self.contract_ok,
                                   "group": self.current_group} for name in names}}

    def export(self, out):
        self.export_calls += 1
        out.mkdir(parents=True, exist_ok=True)
        (out / "Proof.lean").write_text("theorem P5.proof : True := by trivial\n")
        if self.change_head_on_export:
            self.current_group = "group-2"
        return {"ok": self.export_ok, "output": str(out), "build": "stock Lean"}


class CompletedRecoveryTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.backend = Backend()
        controller = Controller(task(), self.root, self.backend)
        state = controller._new_state()
        state["phase"] = "complete"
        state["targets"]["P5.proof"].update(status="done", group="group-1")
        self.backend.save_state(state)

    def test_stale_contract_rejects_stored_completion_before_export(self):
        self.backend.contract_ok = False
        result = Controller(task(), self.root, self.backend).run(recover=True)
        self.assertEqual(result["phase"], "failed")
        self.assertFalse(result["contract_validation"]["ok"])
        self.assertEqual(self.backend.export_calls, 0)
        self.assertEqual(self.backend.saved["phase"], "failed")

    def test_reassigned_current_head_rejects_stored_completion(self):
        self.backend.current_group = "group-2"
        result = Controller(task(), self.root, self.backend).run(recover=True)
        self.assertEqual(result["phase"], "failed")
        self.assertTrue(result["contract_validation"]["ok"])
        self.assertEqual(self.backend.export_calls, 0)

    def test_existing_export_is_rebuilt_and_current_heads_rechecked(self):
        out = self.root / "export"
        out.mkdir()
        (out / "Proof.lean").write_text("corrupt\n")
        result = Controller(task(), self.root, self.backend).run(recover=True)
        self.assertEqual(result["phase"], "complete")
        self.assertEqual(self.backend.export_calls, 1)
        self.assertEqual(self.backend.validate_calls, 2)
        self.assertIn("theorem P5.proof", (out / "Proof.lean").read_text())
        self.assertEqual(result["export"]["build"], "stock Lean")

    def test_head_changed_during_export_rejects_completion(self):
        self.backend.change_head_on_export = True
        result = Controller(task(), self.root, self.backend).run(recover=True)
        self.assertEqual(result["phase"], "failed")
        self.assertEqual(self.backend.validate_calls, 2)
        self.assertEqual(self.backend.export_calls, 1)


if __name__ == "__main__":
    unittest.main()
