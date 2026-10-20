"""Child processes receive only the credentials they need (W2 A-23)."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import Mock, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from p5lib.backend import Backend
from p5lib.task import from_dict
from p5lib.workers import run, worker_env

FOREIGN = {
    "PARALEAN_PEER_S3_SECRET_KEY": "peer-s3-secret",
    "PARALEAN_PEER_S3_ACCESS_KEY": "peer-s3-access",
    "PARALEAN_PEER_KEYS": "/peer/keys.json",
    "PARALEAN_PEER_FDB_CLUSTER": "/peer/fdb.cluster",
    "PARALEAN_SIGNING_SEED": "seed-material",
    "PARALEAN_AUTHORITY_PRIVATE": "private-key",
    "SOME_TOKEN": "token-value",
    "X_SECRET": "secret-value",
    "GH_TOKEN": "github-token",
    "AWS_SECRET_ACCESS_KEY": "aws-secret",
    "DB_PASSWORD": "password",
    "GOOGLE_APPLICATION_CREDENTIALS": "/creds.json",
    "PARALEAN_P5_RECOVERY_SECRET": "controller-only-recovery-key",
    "PARALEAN_P5_RECOVERY_SECRET_FILE": "/prefix/p5-recovery-secret",
    "PARALEAN_GARAGE_ADMIN_TOKEN": "controller-only-admin-token",
    "PARALEAN_GARAGE_RPC_SECRET": "controller-only-rpc-secret",
}
NEEDED = {
    "PATH": "/usr/bin:/bin", "HOME": "/home/p5", "LEAN_PATH": "/lean/lib",
    "PARALEAN_STORE": "/store", "PARALEAN_TRUST": "/state/trust.json",
    "PARALEAN_PLR": "/bin/plr", "PARALEAN_DEPLOYMENT": "test-deployment",
    "PARALEAN_FDB_CLUSTER": "/fdb.cluster", "PARALEAN_S3_ENDPOINT": "http://127.0.0.1:1",
    "PARALEAN_S3_ACCESS_KEY": "own-s3-access", "PARALEAN_S3_SECRET_KEY": "own-s3-secret",
    "PARALEAN_VALIDATOR": "127.0.0.1:1",
}


class ChildEnvironmentTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()

    def assert_clean(self, env: dict) -> None:
        leaked = sorted(name for name in FOREIGN if name in env)
        self.assertEqual(leaked, [], "credentials reached a child process")
        for value in FOREIGN.values():
            self.assertNotIn(value, env.values())

    def test_tool_children_receive_no_foreign_credentials(self):
        task = {"id": "frozen", "agents": ["w0"], "files": [], "targets": []}
        backend = Backend(task, self.root, {**NEEDED, **FOREIGN})
        seen = []

        def fake_run(argv, **kwargs):
            seen.append(kwargs["env"])
            stdout = "0" * 40 if "--githash" in argv else '{"tasks": []}'
            return subprocess.CompletedProcess(argv, 0, stdout, "")

        with patch("p5lib.backend.subprocess.run", side_effect=fake_run), \
                patch.dict("os.environ", {**NEEDED, **FOREIGN}):
            backend._run(["bridge", "noop"])
            backend._ws("sync", "w0", self.root / "w0")
            Backend.list_tasks({**NEEDED, **FOREIGN})
            Backend._attest_stock_build(self.root, str(self.root / "lake"), None)
        self.assertEqual(len(seen), 5)
        for env in seen[:3]:
            self.assert_clean(env)
            for name in ("PATH", "HOME", "LEAN_PATH", "PARALEAN_TRUST", "PARALEAN_PLR",
                         "PARALEAN_S3_ACCESS_KEY", "PARALEAN_S3_SECRET_KEY"):
                self.assertEqual(env[name], NEEDED[name])
        for env in seen[:2]:  # the instance's own key file (bridge, plr, validator)
            self.assertEqual(env["PARALEAN_KEYS"], str(self.root / "keys.json"))
        for env in seen[3:]:  # the stock Lean build runs worker-authored code
            self.assert_clean(env)
            self.assertEqual(env["PATH"], NEEDED["PATH"])
            self.assertFalse(any(name.startswith("PARALEAN_") for name in env))

    def test_worker_cli_receives_no_foreign_credentials(self):
        task = from_dict({"task": {"id": "child-env"}, "controller": {"workers": 1},
                          "worker": {"kind": "command", "command": ["true"]},
                          "targets": [{"name": "P5.target", "statement": "True", "file": "A.lean"}]})
        directory = self.root / "w0"
        (directory / "work").mkdir(parents=True)
        proc = Mock()
        proc.pid = 43212
        proc.wait.return_value = 0
        parent = {**NEEDED, **FOREIGN, "PARALEAN_KEYS": "/state/keys.json",
                  "ANTHROPIC_API_KEY": "anthropic-key"}
        with patch.dict("os.environ", parent, clear=True), \
                patch("p5lib.workers.subprocess.Popen", return_value=proc) as launch:
            result = run(task, task.targets[0], "w0", 1, directory)
        self.assertEqual(result.returncode, 0)
        env = launch.call_args.kwargs["env"]
        self.assert_clean(env)
        self.assertNotIn("ANTHROPIC_API_KEY", env)
        self.assertEqual(env["PARALEAN_KEYS"], str(directory / "keys.json"))
        for name in ("PATH", "HOME", "LEAN_PATH", "PARALEAN_PLR",
                     "PARALEAN_S3_ACCESS_KEY", "PARALEAN_S3_SECRET_KEY"):
            self.assertEqual(env[name], NEEDED[name])

    def test_worker_cli_keeps_only_its_own_login_variables(self):
        parent = {**NEEDED, **FOREIGN, "ANTHROPIC_API_KEY": "anthropic-key",
                  "OPENAI_API_KEY": "openai-key", "CUSTOM_TOKEN": "custom",
                  "PARALEAN_P5_WORKER_ENV_PASSTHROUGH": "CUSTOM_TOKEN,PARALEAN_PEER_KEYS,"
                                                        "PARALEAN_GARAGE_ADMIN_TOKEN"}
        claude = worker_env("claude", parent)
        self.assertEqual(claude["ANTHROPIC_API_KEY"], "anthropic-key")
        self.assertNotIn("OPENAI_API_KEY", claude)
        self.assertEqual(claude["CUSTOM_TOKEN"], "custom")
        self.assert_clean(claude)
        codex = worker_env("codex", parent)
        self.assertEqual(codex["OPENAI_API_KEY"], "openai-key")
        self.assertNotIn("ANTHROPIC_API_KEY", codex)
        self.assert_clean(codex)


if __name__ == "__main__":
    unittest.main()
