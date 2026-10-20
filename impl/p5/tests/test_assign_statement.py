"""Assigning a target pins its frozen statement in the store (W2 A-4)."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from p5lib.backend import Backend, BackendError


class AssignStatementTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        env = {"PARALEAN_DEPLOYMENT": "test", "PARALEAN_FDB_CLUSTER": "unused",
               "PARALEAN_S3_ENDPOINT": "unused", "PARALEAN_S3_ACCESS_KEY": "unused",
               "PARALEAN_S3_SECRET_KEY": "unused", "PARALEAN_VALIDATOR": "127.0.0.1:1",
               "PARALEAN_STOCK_LAKE": "/bin/true", "PARALEAN_LIB": "/unused"}
        task = {"id": "test", "agents": ["w0"], "files": ["A.lean"],
                "sources": {}, "targets": [{"name": "P5.target"}]}
        self.backend = Backend(task, Path(self.temp.name), env)
        self.calls = []

        def bridge(*args):
            self.calls.append(args)
            return {"epoch": 1}

        self.backend._bridge = bridge

    def test_assignment_carries_the_frozen_statement_hash(self):
        self.backend.payload = {"contract_hashes": {"P5.target": "e" * 64}}
        self.assertEqual(self.backend.assign_target("P5.target", "w0"), 1)
        args = self.calls[0]
        self.assertEqual(args[0], "assign-target")
        self.assertEqual(args[args.index("--statement-hash") + 1], "e" * 64)

    def test_assignment_without_a_frozen_statement_fails_closed(self):
        self.backend.payload = {"contract_hashes": {}}
        with self.assertRaises(BackendError):
            self.backend.assign_target("P5.target", "w0")
        self.assertEqual(self.calls, [])


if __name__ == "__main__":
    unittest.main()
