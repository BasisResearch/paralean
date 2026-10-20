"""Gate assertions over actual P1 package metadata shape."""

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "scripts/gate.py"
spec = importlib.util.spec_from_file_location("p5_gate", SCRIPT)
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


class GateTest(unittest.TestCase):
    def test_dependency_check_requires_the_declared_package_edge(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            caps = root / "w0/cache/p3/capsules"
            caps.mkdir(parents=True)
            (caps / "base.json").write_text(json.dumps({"declId": "base-group", "gid": "base-package", "deps": []}))
            branch = caps / "branch.json"
            branch.write_text(json.dumps({"declId": "branch-group", "gid": "branch-package",
                                          "deps": ["base-package"]}))
            targets = [{"name": "P5.base", "deps": []},
                       {"name": "P5.branch", "deps": ["P5.base"]}]
            published = {"P5.base": "base-group", "P5.branch": "branch-group"}
            self.assertTrue(gate.check_dependency_closure(root, targets, published)["ok"])
            branch.write_text(json.dumps({"declId": "branch-group", "gid": "branch-package", "deps": []}))
            self.assertFalse(gate.check_dependency_closure(root, targets, published)["ok"])


if __name__ == "__main__":
    unittest.main()
