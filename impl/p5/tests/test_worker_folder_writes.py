"""Controller writes never follow links a worker planted in its folder (W2 A-9)."""

from __future__ import annotations

import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import Mock, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from p5lib.backend import Backend
from p5lib.task import from_dict
from p5lib.workers import run

GROUP = "1" * 64
CAPSULE = "2" * 64
TEXT = "theorem P5.x : True := by trivial"


class TargetPublicationPathTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.state = self.root / "desktop"
        self.directory = self.state / "w0"
        (self.directory / "work").mkdir(parents=True)
        (self.directory / "work" / "A.lean").write_text(TEXT + "\n")
        capsules = self.directory / "cache" / "p3" / "capsules"
        capsules.mkdir(parents=True)
        (capsules / f"{CAPSULE}.json").write_text(json.dumps({"capsule": {"text": TEXT}}))
        self.outside_receipt = self.root / "outside-receipt"
        self.outside_plan = self.root / "outside-plan"
        for sentinel in (self.outside_receipt, self.outside_plan):
            sentinel.write_text("outside sentinel")
        task = {"id": "frozen", "agents": ["w0"], "files": ["A.lean"],
                "targets": [{"name": "P5.x", "statement": "True"}]}
        env = {"PARALEAN_DEPLOYMENT": "test-deployment", "PARALEAN_FDB_CLUSTER": "unused",
               "PARALEAN_S3_ENDPOINT": "unused", "PARALEAN_S3_ACCESS_KEY": "access",
               "PARALEAN_S3_SECRET_KEY": "secret", "PARALEAN_VALIDATOR": "127.0.0.1:1",
               "PARALEAN_P5_RECOVERY_SECRET": "controller-only-recovery-key"}
        self.backend = Backend(task, self.state, env)
        self.backend.payload = {"contract_hashes": {"P5.x": "b" * 64}}
        self.backend._start_validator = lambda: None
        self.backend.sync = lambda agent, directory: {}
        self.backend.validate = lambda names: {"ok": True, "targets": {"P5.x": {"ok": True}}}
        self.calls = {}

        def fake_run(argv, *, env=None, cwd=None):
            if len(argv) > 1 and argv[1] == "ws-capture":
                return {"packages": [{"group": GROUP, "capsule": CAPSULE,
                                      "names": ["P5.x"], "deps": []}]}
            if len(argv) > 1 and argv[1] == "ws-plan":
                receipt = Path(argv[argv.index("--receipts") + 1])
                out = Path(argv[argv.index("--out") + 1])
                self.calls["receipt"] = receipt
                self.calls["receipt_text"] = receipt.read_text()
                # Like the Lean binary, an ordinary file write follows symlinks.
                out.write_text(json.dumps([{"group": GROUP}, {"group": "3" * 64}]))
                return {"planned": 2}
            return {}

        def fake_bridge(*args, env=None):
            if args[0] == "validate-target":
                return {"accepted": True, "ms": 1}
            if args[0] == "publish-target":
                plan = Path(args[args.index("--plan") + 1])
                self.calls["plan"] = plan
                self.calls["plan_entries"] = json.loads(plan.read_text())
                return {}
            raise AssertionError(args)

        self.backend._run = fake_run
        self.backend._bridge = fake_bridge

    def test_target_publication_does_not_follow_worker_symlinks(self):
        (self.directory / "p5-target-receipt.json").symlink_to(self.outside_receipt)
        (self.directory / "p5-target-plan.json").symlink_to(self.outside_plan)
        try:
            result = self.backend.publish("w0", self.directory, "A.lean", ["P5.x"], epoch=1)
        except Exception as exc:
            self.fail(f"publication failed because of worker-planted links: {exc!r}")
        self.assertEqual(result["groups"], [GROUP])
        self.assertEqual(self.outside_receipt.read_text(), "outside sentinel")
        self.assertEqual(self.outside_plan.read_text(), "outside sentinel")
        self.assertEqual(json.loads(self.calls["receipt_text"]), {"accepted": True, "ms": 1})
        self.assertEqual(self.calls["plan_entries"], [{"group": GROUP}])
        for path in (self.calls["receipt"], self.calls["plan"]):
            self.assertNotIn(self.directory, path.parents)
            self.assertIn(self.state, path.parents)
        self.assertEqual(sorted(p.name for p in self.state.glob("p5-publish-*")), [])


class WorkerLogPathTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.directory = self.root / "w0"
        (self.directory / "work").mkdir(parents=True)
        self.task = from_dict({"task": {"id": "log-paths"}, "controller": {"workers": 1},
                               "worker": {"kind": "command", "command": ["true"]},
                               "targets": [{"name": "P5.target", "statement": "True", "file": "A.lean"}]})

    def launch(self):
        proc = Mock()
        proc.pid = 43213
        proc.wait.return_value = 0
        with patch("p5lib.workers.subprocess.Popen", return_value=proc):
            return run(self.task, self.task.targets[0], "w0", 1, self.directory)

    def test_worker_logs_replace_planted_links(self):
        logs = self.directory / "p5-logs"
        logs.mkdir()
        prompt_sentinel = self.root / "outside-prompt"
        log_sentinel = self.root / "outside-log"
        for sentinel in (prompt_sentinel, log_sentinel):
            sentinel.write_text("outside sentinel")
        (logs / "P5_target-1.prompt.txt").symlink_to(prompt_sentinel)
        os.link(log_sentinel, logs / "P5_target-1.log")
        result = self.launch()
        self.assertEqual(result.returncode, 0)
        self.assertEqual(prompt_sentinel.read_text(), "outside sentinel")
        self.assertEqual(log_sentinel.read_text(), "outside sentinel")
        prompt = logs / "P5_target-1.prompt.txt"
        self.assertFalse(prompt.is_symlink())
        self.assertIn("P5.target", prompt.read_text())

    def test_symlinked_log_directory_fails_closed(self):
        outside = self.root / "outside-dir"
        outside.mkdir()
        (self.directory / "p5-logs").symlink_to(outside, target_is_directory=True)
        with self.assertRaises(OSError):
            self.launch()
        self.assertEqual(list(outside.iterdir()), [])


if __name__ == "__main__":
    unittest.main()
