"""A worker's store credentials cannot rewrite the frozen P5 task journal."""

from __future__ import annotations

import copy
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from p5lib.backend import Backend, BackendError


class JournalAuthTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.task = {"id": "frozen", "agents": ["w0"], "workers": 1,
                     "files": ["A.lean"], "sources": {"A.lean": "theorem P5.x : True := by trivial"},
                     "targets": [{"name": "P5.x", "statement": "True"}]}
        self.env = {"PARALEAN_DEPLOYMENT": "test-deployment", "PARALEAN_FDB_CLUSTER": "unused",
                    "PARALEAN_S3_ENDPOINT": "unused", "PARALEAN_S3_ACCESS_KEY": "worker-can-use-this",
                    "PARALEAN_S3_SECRET_KEY": "worker-can-use-this-too",
                    "PARALEAN_P5_RECOVERY_SECRET": "controller-only-recovery-key",
                    "PARALEAN_GARAGE_ADMIN_TOKEN": "controller-only-admin-token",
                    "PARALEAN_GARAGE_RPC_SECRET": "controller-only-rpc-secret",
                    "PARALEAN_VALIDATOR": "127.0.0.1:1"}
        self.backend = Backend(self.task, self.root, self.env)
        self.blob = None

        def bridge(*args, env=None):
            if args[0] == "put":
                self.blob = json.loads(Path(args[args.index("--file") + 1]).read_text())
                return {"sequence": 1, "blob": "a" * 64}
            if args[0] == "get":
                Path(args[args.index("--out") + 1]).write_text(json.dumps(self.blob))
                return {"found": True, "sequence": 1}
            raise AssertionError(args)

        self.backend._bridge = bridge
        self.backend._commit({"task": "frozen", "contract_hash": self.backend.contract_hash,
                              "spec": self.task, "state": {"phase": "running"},
                              "contract_hashes": {"P5.x": "b" * 64}, "keys": {}})

    def test_valid_roundtrip_authenticates_full_payload(self):
        self.assertTrue(self.blob["journal_hmac"].startswith("v1:"))
        self.assertEqual(self.backend._read_snapshot()["spec"], self.task)

    def test_missing_and_changed_tags_fail_closed(self):
        original = copy.deepcopy(self.blob)
        for changed in (
            {k: v for k, v in original.items() if k != "journal_hmac"},
            {**original, "state": {"phase": "complete"}},
            {**original, "contract_hashes": {"P5.x": "c" * 64}},
            {**original, "spec": {**self.task, "targets": []}},
        ):
            with self.subTest(changed=changed):
                self.blob = changed
                with self.assertRaisesRegex(BackendError, "authentication|tag"):
                    self.backend._read_snapshot()
        self.blob = original

    def test_store_only_recovery_verifies_before_trusting_spec(self):
        self.blob["spec"] = {"id": "attacker-replacement", "targets": []}
        def fake_run(argv, **kwargs):
            Path(argv[argv.index("--out") + 1]).write_text(json.dumps(self.blob))
            return subprocess.CompletedProcess(argv, 0, '{"found":true,"sequence":1}', "")
        with patch("p5lib.backend.subprocess.run", side_effect=fake_run):
            with self.assertRaisesRegex(BackendError, "authentication"):
                Backend.recover_task("frozen", self.root / "lost-desktop", self.env)
        self.assertFalse((self.root / "lost-desktop" / "keys.json").exists())

    def test_old_signed_payload_cannot_be_replayed_at_new_head(self):
        with self.assertRaisesRegex(BackendError, "sequence"):
            Backend._verify_journal(self.blob, "frozen", self.backend.env, 2)

    def test_key_restore_rejects_symlink_and_stale_local_key(self):
        sealed = self.backend._seal(b"authenticated signing seed")
        payload = {"keys": {"keys.json": sealed}}
        outside = self.root / "outside"
        key = self.root / "keys.json"
        key.symlink_to(outside)
        with self.assertRaises(OSError):
            self.backend._restore_keys(payload)
        self.assertFalse(outside.exists())
        key.unlink()
        key.write_bytes(b"stale seed")
        with self.assertRaisesRegex(BackendError, "differs"):
            self.backend._restore_keys(payload)
        self.assertEqual(key.read_bytes(), b"stale seed")
        key.unlink()
        self.backend._restore_keys(payload)
        self.assertEqual(key.read_bytes(), b"authenticated signing seed")

    def test_runtime_child_does_not_inherit_controller_secrets(self):
        def fake_run(argv, **kwargs):
            child_env = kwargs["env"]
            for name in Backend._CONTROLLER_ONLY_ENV:
                self.assertNotIn(name, child_env)
            self.assertEqual(child_env["PARALEAN_S3_ACCESS_KEY"], "worker-can-use-this")
            return subprocess.CompletedProcess(argv, 0, "{}", "")
        with patch("p5lib.backend.subprocess.run", side_effect=fake_run):
            self.backend._run(["bridge", "noop"])
            self.backend._ws("sync", "w0", self.root / "w0")


if __name__ == "__main__":
    unittest.main()
