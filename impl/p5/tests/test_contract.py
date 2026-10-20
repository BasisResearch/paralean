"""Check P5's private contract compiler against P1's captured typeHash."""

from __future__ import annotations

import glob
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
CONTRACT = ROOT / "impl/p5/Contract.lean"


class ContractTest(unittest.TestCase):
    def setUp(self):
        self.lean = os.environ.get("PARALEAN_P5_LEAN")
        if not self.lean:
            prefix = os.environ.get("PARALEAN_FORK_PREFIX")
            self.lean = str(Path(prefix) / "bin/lean") if prefix else "lean"
        self.lib = os.environ.get("PARALEAN_LIB")
        self.p1 = os.environ.get("PARALEAN_BIN")
        if not self.lib or not self.p1 or not Path(self.p1).is_file():
            self.skipTest("source impl/p5/scripts/env.sh and build P1 first")
        self.env = dict(os.environ, LEAN_PATH=self.lib + os.pathsep + os.environ.get("LEAN_PATH", ""))
        self.temp = tempfile.TemporaryDirectory()
        self.dir = Path(self.temp.name)

    def tearDown(self):
        if hasattr(self, "temp"):
            self.temp.cleanup()

    def hashes(self, targets):
        spec = self.dir / "contracts.json"
        spec.write_text(json.dumps({"targets": targets}))
        return subprocess.run([self.lean, "--run", str(CONTRACT), "--input", str(spec)],
                              env=self.env, text=True, capture_output=True, timeout=45)

    def test_hash_matches_p1_capture_and_changes_with_statement(self):
        name = "P5.add_comm_general"
        statement = "∀ a b : Nat, a + b = b + a"
        good = self.hashes([{"name": name, "statement": statement}])
        self.assertEqual(good.returncode, 0, good.stderr)
        expected = json.loads(good.stdout)[name]
        source = self.dir / "Test.lean"
        source.write_text(f"theorem {name} : {statement} := by\n  intro a b\n  exact Nat.add_comm a b\n")
        store = self.dir / "store"
        captured = subprocess.run([self.p1, "capture", "--store", str(store), "--ws", "t",
                                   "--root", str(self.dir), "Test.lean"], env=self.env,
                                  text=True, capture_output=True, timeout=45)
        self.assertEqual(captured.returncode, 0, captured.stderr)
        meta_files = glob.glob(str(store / "meta/*.json"))
        self.assertEqual(len(meta_files), 1)
        actual = json.loads(Path(meta_files[0]).read_text())["members"][0]["typeHash"]
        self.assertEqual(expected, actual)
        changed = self.hashes([{"name": name, "statement": "∀ a b : Nat, b + a = a + b"}])
        self.assertEqual(changed.returncode, 0, changed.stderr)
        self.assertNotEqual(expected, json.loads(changed.stdout)[name])

    def test_bad_type_fails_closed(self):
        bad = self.hashes([{"name": "P5.bad", "statement": "(0 : Nat) = True"}])
        self.assertNotEqual(bad.returncode, 0)
        self.assertFalse(bad.stdout.strip().startswith("{"))


if __name__ == "__main__":
    unittest.main()
