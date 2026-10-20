"""The deployment recovery secret is separate, present and private (W2 A-20)."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from p5lib.backend import Backend, BackendError

P5 = Path(__file__).resolve().parents[1]
ADMIN = "garage-admin-token-0123456789abcdef"
S3_SECRET = "worker-held-s3-secret-0123456789"


def base_env(**extra) -> dict:
    env = {"PARALEAN_DEPLOYMENT": "test-deployment",
           "PARALEAN_GARAGE_ADMIN_TOKEN": ADMIN,
           "PARALEAN_GARAGE_RPC_SECRET": "garage-rpc-secret-0123456789abcdef",
           "PARALEAN_S3_ACCESS_KEY": "worker-held-s3-access-key",
           "PARALEAN_S3_SECRET_KEY": S3_SECRET}
    env.update(extra)
    return env


class RecoverySecretTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def private_file(self, name: str, text: str, mode: int = 0o600) -> Path:
        path = self.root / name
        path.write_text(text)
        path.chmod(mode)
        return path

    def test_recovery_secret_rejects_shared_credentials(self):
        cases = {
            "env equals Garage admin token": base_env(PARALEAN_P5_RECOVERY_SECRET=ADMIN),
            "env equals worker S3 secret": base_env(PARALEAN_P5_RECOVERY_SECRET=S3_SECRET),
            "file equals Garage admin token": base_env(
                PARALEAN_P5_RECOVERY_SECRET_FILE=str(self.private_file("admin", ADMIN + "\n"))),
        }
        for label, env in cases.items():
            with self.subTest(case=label):
                with self.assertRaisesRegex(BackendError, "must not reuse"):
                    Backend._journal_key("task", env)

    def test_recovery_secret_missing_or_empty_fails_closed(self):
        cases = {
            "unset": base_env(),
            "empty env": base_env(PARALEAN_P5_RECOVERY_SECRET=""),
            "blank env": base_env(PARALEAN_P5_RECOVERY_SECRET="   "),
            "short env": base_env(PARALEAN_P5_RECOVERY_SECRET="short"),
            "missing file": base_env(PARALEAN_P5_RECOVERY_SECRET_FILE=str(self.root / "absent")),
            "empty file": base_env(
                PARALEAN_P5_RECOVERY_SECRET_FILE=str(self.private_file("empty", "\n"))),
        }
        for label, env in cases.items():
            with self.subTest(case=label):
                with self.assertRaises(BackendError):
                    Backend._journal_key("task", env)

    def test_recovery_secret_file_must_be_private_regular_file(self):
        good = self.private_file("good", "a-separate-recovery-secret-value\n")
        group_readable = self.private_file("group", "a-separate-recovery-secret-value\n", 0o640)
        world_readable = self.private_file("world", "a-separate-recovery-secret-value\n", 0o604)
        link = self.root / "link"
        link.symlink_to(good)
        directory = self.root / "directory"
        directory.mkdir(mode=0o700)
        for label, path in (("group readable", group_readable), ("world readable", world_readable),
                            ("symlink", link), ("directory", directory)):
            with self.subTest(case=label):
                with self.assertRaises(BackendError):
                    Backend._journal_key("task", base_env(PARALEAN_P5_RECOVERY_SECRET_FILE=str(path)))
        from_file = Backend._journal_key("task", base_env(PARALEAN_P5_RECOVERY_SECRET_FILE=str(good)))
        from_env = Backend._journal_key(
            "task", base_env(PARALEAN_P5_RECOVERY_SECRET="a-separate-recovery-secret-value"))
        self.assertEqual(from_file, from_env)

    def test_signing_seed_encryption_uses_the_same_checks(self):
        task = {"id": "frozen", "agents": ["w0"], "files": [], "targets": []}
        env = base_env(PARALEAN_FDB_CLUSTER="unused", PARALEAN_S3_ENDPOINT="unused",
                       PARALEAN_VALIDATOR="127.0.0.1:1", PARALEAN_P5_RECOVERY_SECRET=ADMIN)
        backend = Backend(task, self.root / "desktop", env)
        with self.assertRaisesRegex(BackendError, "must not reuse"):
            backend._seal(b"seed")

    @unittest.skipUnless((P5.parent / "p3" / "scripts" / "env.sh").exists() and shutil.which("bash"),
                         "needs the repository's P3 environment script")
    def test_env_sh_creates_private_secret_and_drops_admin_token_default(self):
        prefix = self.root / "prefix"
        prefix.mkdir()
        script = ('set -u; . "$1"; '
                  'printf "%s\\n" "$PARALEAN_P5_RECOVERY_SECRET_FILE" "${PARALEAN_P5_RECOVERY_SECRET-unset}"')
        env = {**os.environ, "PARALEAN_P5_PREFIX": str(prefix), "TMPDIR": str(self.root / "tmp"),
               "PARALEAN_GARAGE_ADMIN_TOKEN": ADMIN, "PARALEAN_P5_RECOVERY_SECRET": ADMIN}
        env.pop("PARALEAN_P5_RECOVERY_SECRET_FILE", None)
        outputs = []
        for _ in range(2):
            proc = subprocess.run(["bash", "-c", script, "env-test", str(P5 / "scripts" / "env.sh")],
                                  env=env, text=True, capture_output=True, timeout=60)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            outputs.append(proc.stdout.splitlines()[-2:])
        path = Path(outputs[0][0])
        self.assertEqual(path, prefix / "p5-recovery-secret")
        self.assertEqual(outputs[0][1], "unset")
        self.assertEqual(path.stat().st_mode & 0o777, 0o600)
        first = path.read_text()
        self.assertEqual(outputs[1][0], str(path))
        self.assertEqual(path.read_text(), first, "sourcing again must not replace the secret")
        self.assertNotEqual(first.strip(), ADMIN)
        Backend._journal_key("task", base_env(PARALEAN_P5_RECOVERY_SECRET_FILE=str(path)))


if __name__ == "__main__":
    unittest.main()
