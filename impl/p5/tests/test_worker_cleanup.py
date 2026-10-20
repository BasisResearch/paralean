"""A parent-side launch error must not leave its guarded coding agent alive."""

from __future__ import annotations

import os
import sys
import signal
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import Mock, call, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from p5lib.task import from_dict
from p5lib.workers import run
from p5lib import worker_guard


class WorkerCleanupTest(unittest.TestCase):
    def test_real_cli_child_can_receive_sigterm(self):
        check_mask = ("import signal; "
                      "blocked = signal.pthread_sigmask(signal.SIG_BLOCK, set()); "
                      "print(int(signal.SIGTERM in blocked))")
        result = subprocess.run(
            [sys.executable, str(Path(worker_guard.__file__)), sys.executable,
             "-c", check_mask],
            env={**os.environ, "PARALEAN_P5_PARENT_PID": str(os.getpid())},
            capture_output=True, text=True, timeout=5, check=True)
        self.assertEqual(result.stdout.strip(), "0")

    def test_fast_exiting_guard_still_kills_cli_group(self):
        task = from_dict({"task": {"id": "worker-cleanup"},
                          "controller": {"workers": 1},
                          "worker": {"kind": "codex"},
                          "targets": [{"name": "P5.target", "statement": "True", "file": "A.lean"}]})
        proc = Mock()
        proc.pid = 43210
        proc.stdin.write.side_effect = BrokenPipeError("guard exited before prompt")
        proc.wait.return_value = 0
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp) / "w0"
            (directory / "work").mkdir(parents=True)
            with patch("p5lib.workers.subprocess.Popen", return_value=proc) as launch, \
                    patch("p5lib.workers.os.killpg") as kill_group:
                with self.assertRaises(BrokenPipeError):
                    run(task, task.targets[0], "w0", 1, directory)
        self.assertTrue(launch.call_args.kwargs["start_new_session"])
        self.assertEqual(kill_group.call_args_list,
                         [call(proc.pid, signal.SIGTERM), call(proc.pid, signal.SIGKILL)])
        proc.wait.assert_called_once_with(timeout=5)

    def test_stubborn_guard_gets_sigkill_and_is_reaped(self):
        task = from_dict({"task": {"id": "worker-cleanup-timeout"},
                          "controller": {"workers": 1},
                          "worker": {"kind": "codex"},
                          "targets": [{"name": "P5.target", "statement": "True", "file": "A.lean"}]})
        proc = Mock()
        proc.pid = 43211
        proc.stdin.write.side_effect = BrokenPipeError("guard exited before prompt")
        proc.wait.side_effect = [subprocess.TimeoutExpired("guard", 5), 0]
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp) / "w0"
            (directory / "work").mkdir(parents=True)
            with patch("p5lib.workers.subprocess.Popen", return_value=proc), \
                    patch("p5lib.workers.os.killpg") as kill_group:
                with self.assertRaises(BrokenPipeError):
                    run(task, task.targets[0], "w0", 1, directory)
        self.assertEqual(kill_group.call_args_list,
                         [call(proc.pid, signal.SIGTERM), call(proc.pid, signal.SIGKILL)])
        self.assertEqual(proc.wait.call_args_list, [call(timeout=5), call()])

    def test_parent_death_guard_kills_descendants_after_bounded_wait(self):
        child = Mock()
        child.wait.side_effect = subprocess.TimeoutExpired("coding-cli", 5)
        with patch.object(worker_guard, "child", child), \
                patch.object(worker_guard.os, "getpgrp", return_value=98765), \
                patch.object(worker_guard.os, "killpg") as kill_group, \
                patch.object(worker_guard.signal, "signal"):
            with self.assertRaises(SystemExit):
                worker_guard.terminate(signal.SIGTERM, None)
            # Cleanup runs after the signal unwinds Popen.wait's internal lock.
            worker_guard.cleanup_group()
        self.assertEqual(kill_group.call_args_list,
                         [call(98765, signal.SIGTERM), call(98765, signal.SIGKILL)])
        child.wait.assert_called_once_with(timeout=5)


if __name__ == "__main__":
    unittest.main()
