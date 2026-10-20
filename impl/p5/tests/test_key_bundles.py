"""Signing seeds sealed under the worker-held S3 secret are refused (W2 A-21)."""

from __future__ import annotations

import base64
import hashlib
import os
import sys
import tempfile
import unittest
from pathlib import Path

from cryptography.hazmat.primitives.ciphers.aead import AESGCM

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from p5lib.backend import Backend, BackendError

SEED = b"workspace signing seed"


class KeyBundleTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.task = {"id": "frozen", "agents": ["w0"], "workers": 1, "files": [], "targets": []}
        self.env = {"PARALEAN_DEPLOYMENT": "test-deployment", "PARALEAN_FDB_CLUSTER": "unused",
                    "PARALEAN_S3_ENDPOINT": "unused", "PARALEAN_S3_ACCESS_KEY": "worker-access-key",
                    "PARALEAN_S3_SECRET_KEY": "worker-held-s3-secret",
                    "PARALEAN_P5_RECOVERY_SECRET": "controller-only-recovery-key",
                    "PARALEAN_VALIDATOR": "127.0.0.1:1"}
        self.backend = Backend(self.task, self.root, self.env)
        self.puts = []

        def bridge(*args, env=None):
            if args[0] == "put":
                self.puts.append(args)
                return {"sequence": 1, "blob": "a" * 64}
            raise AssertionError(args)

        self.backend._bridge = bridge

    def legacy_bundle(self, data: bytes = SEED) -> str:
        # The pre-v2 format: no prefix, key derived from the S3 secret every worker holds.
        salt = (self.env["PARALEAN_DEPLOYMENT"] + "/p5/" + self.task["id"]).encode()
        key = hashlib.pbkdf2_hmac("sha256", self.env["PARALEAN_S3_SECRET_KEY"].encode(),
                                  salt, 100_000, 32)
        nonce = os.urandom(12)
        sealed = nonce + AESGCM(key).encrypt(nonce, data, self.backend.contract_hash.encode())
        return base64.b64encode(sealed).decode()

    def test_v2_bundle_roundtrip(self):
        sealed = self.backend._seal(SEED)
        self.assertTrue(sealed.startswith("v2:"))
        self.assertEqual(self.backend._open(sealed), SEED)

    def test_legacy_key_bundle_is_refused(self):
        try:
            opened = self.backend._open(self.legacy_bundle())
        except BackendError as exc:
            self.assertIn("pre-v2", str(exc))
        except Exception as exc:  # a crypto error is not an explicit refusal
            self.fail(f"legacy bundle was not refused by policy: {exc!r}")
        else:
            self.fail(f"legacy bundle sealed under the S3 secret was accepted: {opened!r}")

    def test_restore_refuses_legacy_bundle_and_writes_nothing(self):
        with self.assertRaisesRegex(BackendError, "pre-v2"):
            self.backend._restore_keys({"keys": {"keys.json": self.legacy_bundle()}})
        self.assertFalse((self.root / "keys.json").exists())

    def test_commit_refuses_legacy_bundle(self):
        data = {"task": "frozen", "contract_hash": self.backend.contract_hash, "spec": self.task,
                "state": {}, "keys": {"keys.json": self.legacy_bundle()}}
        with self.assertRaisesRegex(BackendError, "pre-v2"):
            self.backend._commit(data)
        self.assertEqual(self.puts, [])


if __name__ == "__main__":
    unittest.main()
