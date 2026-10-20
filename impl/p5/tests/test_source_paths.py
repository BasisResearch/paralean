"""Worker-controlled paths cannot make P5 read or overwrite outside its work tree."""

from __future__ import annotations

import sys
import tempfile
import unittest
import json
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from p5lib.backend import Backend, BackendError, _read_source, _write_source_if_missing
from p5lib.task import from_dict


class SourcePathTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.work = self.root / "desktop" / "w0" / "work"
        self.work.mkdir(parents=True)
        self.secret = self.root / "outside.txt"
        self.secret.write_text("outside secret")

    def test_capture_rejects_leaf_symlink_before_journaling(self):
        (self.work / "Target.lean").symlink_to(self.secret)
        backend = object.__new__(Backend)
        backend.paths = {"w0": self.work.parent}
        backend.task = {"files": ["Target.lean"]}
        with self.assertRaises(OSError):
            backend._sources()

    def test_restore_rejects_symlink_parent_and_preserves_outside(self):
        (self.work / "nested").symlink_to(self.root, target_is_directory=True)
        with self.assertRaises(OSError):
            _write_source_if_missing(self.work, "nested/outside.txt", "replacement")
        self.assertEqual(self.secret.read_text(), "outside secret")

    def test_regular_nested_source_roundtrip(self):
        _write_source_if_missing(self.work, "nested/Target.lean", "proof")
        self.assertEqual(_read_source(self.work, "nested/Target.lean"), "proof")
        _write_source_if_missing(self.work, "nested/Target.lean", "replacement")
        self.assertEqual(_read_source(self.work, "nested/Target.lean"), "proof")

    def test_noncanonical_paths_are_rejected_at_task_load(self):
        for path in ("../outside.txt", ".", "a//b.lean", "a/./b.lean", "a/../b.lean", "a\\b.lean"):
            with self.subTest(path=path), self.assertRaises(ValueError):
                from_dict({"task": {"id": "paths", "files": [path]},
                           "targets": [{"name": "P5.x", "statement": "True", "file": path}]})

    def test_cache_marker_cannot_choose_capsule_outside_cache(self):
        records = self.work.parent / "cache" / "p3" / "records"
        records.mkdir(parents=True)
        (records / "m-malicious.json").write_text(json.dumps({"capsule": "../../../../outside"}))
        backend = object.__new__(Backend)
        backend.paths = {"w0": self.work.parent}
        backend.task = {"targets": [{"name": "P5.x"}]}
        with self.assertRaisesRegex(BackendError, "malformed object ID"):
            backend._target_candidates()


if __name__ == "__main__":
    unittest.main()
