"""Dependency-free controller tests with a durable-store stand-in.

These check scheduling and state reconstruction. The live gate separately checks
the real P2/P3 store, validator, remote%, and stock Lean export.
"""

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
from p5lib.task import from_dict, load
from p5lib.workers import WorkerResult


class DurableBackend:
    def __init__(self):
        self.saved = None
        self.groups = {}
        self.provisioned = []
        self.fail_once = set()
        self.epochs = {}

    def setup(self):
        pass

    def save_state(self, state):
        self.saved = copy.deepcopy(state)
        return f"snapshot-{len(state['events'])}"

    def load_state(self):
        return copy.deepcopy(self.saved)

    def provision(self, agent, directory):
        (directory / "work").mkdir(parents=True, exist_ok=True)
        self.provisioned.append(agent)

    def sync(self, agent, directory):
        return {"metrics": {"transfer_bytes": 10}}

    def assign_target(self, name, agent):
        self.epochs[name] = self.epochs.get(name, 0) + 1
        return self.epochs[name]

    def conflicts(self):
        return []

    def publish(self, agent, directory, file, names, epoch=None):
        name = names[0]
        if name in self.fail_once:
            self.fail_once.remove(name)
            raise RuntimeError("registry conflict")
        self.groups[name] = f"group-{name}"
        return {"group": self.groups[name], "metrics": {"check_ms": 5}}

    def validate(self, names):
        return {"ok": all(n in self.groups for n in names),
                "targets": {n: {"group": self.groups.get(n)} for n in names}}

    def export(self, out):
        out.mkdir(parents=True, exist_ok=True)
        return {"ok": True, "groups": len(self.groups), "buildMs": 1}


def two_target_task():
    return from_dict({"task": {"id": "two", "name": "two"},
                      "controller": {"workers": 2, "max_attempts": 3},
                      "targets": [
                          {"name": "P5.base", "statement": "theorem P5.base : True", "file": "A.lean"},
                          {"name": "P5.final", "statement": "theorem P5.final : True", "file": "B.lean",
                           "deps": ["P5.base"]}]})


def worker_ok(task, target, agent, attempt, directory, feedback=""):
    return WorkerResult(target.name, agent, attempt, 0, 0.01, False, "mock.log")


class ControllerTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)

    def tearDown(self):
        self.temp.cleanup()

    def test_recover_after_entire_local_state_is_lost(self):
        backend = DurableBackend()
        state = self.root / "desktop"
        calls = 0

        def interrupted(task, target, agent, attempt, directory, feedback=""):
            nonlocal calls
            calls += 1
            if calls == 2:
                raise KeyboardInterrupt("desktop lost")
            return worker_ok(task, target, agent, attempt, directory)

        with patch("p5lib.controller.run_worker", side_effect=interrupted):
            with self.assertRaises(KeyboardInterrupt):
                Controller(two_target_task(), state, backend, parallelism=1).run()
        prior_group = backend.groups["P5.base"]
        shutil.rmtree(state)
        self.assertFalse(state.exists())
        with patch("p5lib.controller.run_worker", side_effect=worker_ok):
            result = Controller(two_target_task(), state, backend, parallelism=1).run(recover=True)
        self.assertEqual(result["phase"], "complete")
        self.assertEqual(result["targets"]["P5.base"]["group"], prior_group)
        self.assertEqual(result["targets"]["P5.base"]["attempts"], 1)
        self.assertEqual(result["targets"]["P5.final"]["status"], "done")
        self.assertEqual(backend.provisioned.count("w0"), 2)

    def test_publication_conflict_retries_without_committing_failed_attempt(self):
        backend = DurableBackend()
        backend.fail_once.add("P5.base")
        with patch("p5lib.controller.run_worker", side_effect=worker_ok):
            result = Controller(two_target_task(), self.root / "conflict", backend,
                                parallelism=1).run()
        self.assertEqual(result["phase"], "complete")
        self.assertEqual(result["targets"]["P5.base"]["attempts"], 2)
        self.assertEqual(result["targets"]["P5.final"]["attempts"], 1)
        self.assertTrue(any(x["event"] == "publication_failed" for x in result["events"]))

    def test_task_has_eight_independent_branches_and_frozen_final_contract(self):
        task = load(Path(__file__).resolve().parents[1] / "tasks/add_comm_eight.toml")
        by_name = {t.name: t for t in task.targets}
        self.assertEqual(len(by_name), 10)
        self.assertEqual({by_name[f"P5.add_comm_{i}"].deps for i in range(1, 9)},
                         {("P5.add_comm_general",)})
        final = by_name["P5.add_comm_up_to_eight"]
        self.assertEqual(len(final.deps), 8)
        self.assertTrue(all(f"n + {i} = {i} + n" in final.statement for i in range(1, 9)))

    def test_list_api_task_has_same_parallel_shape(self):
        task = load(Path(__file__).resolve().parents[1] / "tasks/list_reverse_map_lengths.toml")
        by_name = {t.name: t for t in task.targets}
        self.assertEqual(len(by_name), 10)
        self.assertEqual(by_name["P5List.map_length"].deps, ())
        for i in range(1, 9):
            self.assertEqual(by_name[f"P5List.reverse_map_len_{i}"].deps, ("P5List.map_length",))
        self.assertEqual(len(by_name["P5List.reverse_map_lengths"].deps), 8)


if __name__ == "__main__":
    unittest.main()
