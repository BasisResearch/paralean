"""The final catalogue must describe the same group closure that stock Lean built."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from p5lib.backend import Backend, BackendError


class ExportSnapshotTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.work = self.root / "w0"
        (self.work / "work").mkdir(parents=True)
        (self.work / "cache" / "p3" / "records").mkdir(parents=True)
        (self.work / "work" / "A.lean").write_text("theorem P5.target : True := by trivial\n")
        # The old marker is still cached after a revision, but was not built.
        (self.work / "cache" / "p3" / "records" / "m-old.json").write_text(
            json.dumps({"file": "A.lean", "revisions": ["a" * 64]}))
        env = {"PARALEAN_DEPLOYMENT": "test", "PARALEAN_FDB_CLUSTER": "unused",
               "PARALEAN_S3_ENDPOINT": "unused", "PARALEAN_S3_ACCESS_KEY": "unused",
               "PARALEAN_S3_SECRET_KEY": "unused", "PARALEAN_VALIDATOR": "127.0.0.1:1",
               "PARALEAN_STOCK_LAKE": "/bin/true", "PARALEAN_LIB": "/unused"}
        task = {"id": "test", "agents": ["w0"], "files": ["A.lean"],
                "sources": {}, "targets": [{"name": "P5.target"}]}
        self.backend = Backend(task, self.root, env)
        self.backend.paths = {"w0": self.work}
        self.backend.payload = {"contract_hashes": {"P5.target": "e" * 64}}
        self.backend.validate = lambda names: {"ok": True, "targets": {
            "P5.target": {"ok": True, "group": "1" * 64}}}
        self.backend.sync = lambda agent, directory: {}
        self.backend.conflicts = lambda: []
        self.backend._commit = lambda data: "journal"
        self.backend._attest_stock_build = lambda out, lake, mathlib: {
            "attestationBuildMs": 1, "buildLogHash": "6" * 64,
            "leanCommit": "7" * 40, "mathlibCommit": ""}
        self.selection = {"groups": [
            {"group": "1" * 64, "file": "A.lean", "revisions": ["2" * 64], "current": True},
            {"group": "3" * 64, "file": "B.lean", "revisions": ["4" * 64], "current": True}]}
        self.committed = None

        def run(argv, *, env=None, cwd=None):
            if "ws-export" in argv:
                return {"ok": True, "groups": 2, "buildMs": 1}
            if "Snapshot.lean" in " ".join(argv):
                return self.selection
            raise AssertionError(argv)

        self.backend._run = run
        def bridge(*args):
            self.assertEqual(args[0], "checkpoint-targets")
            self.committed = json.loads(Path(args[args.index("--spec") + 1]).read_text())
            return {"catalog": "5" * 64, "completion_targets": []}
        self.backend._bridge = bridge

    def test_checkpoint_uses_exact_export_closure_and_excludes_cached_history(self):
        self.backend.export(self.root / "export")
        self.assertEqual(self.committed["revisions"], ["2" * 64, "4" * 64])
        self.assertEqual(self.committed["files"], {"A.lean": ["2" * 64],
                                                  "B.lean": ["4" * 64]})
        self.assertNotIn("a" * 64, self.committed["revisions"])
        self.assertEqual(self.committed["targets"], [{"name": "P5.target",
            "group": "1" * 64, "statement_hash": "e" * 64}])
        self.assertEqual(self.committed["build"]["build_log_hash"], "6" * 64)

    def test_noncurrent_dependency_cannot_be_checkpointed(self):
        self.selection["groups"][1]["current"] = False
        with self.assertRaisesRegex(BackendError, "noncurrent"):
            self.backend.export(self.root / "export")
        self.assertIsNone(self.committed)


if __name__ == "__main__":
    unittest.main()
