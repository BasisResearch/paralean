#!/usr/bin/env python3
"""Run P5 guard-removal regressions against private source copies."""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


P5 = Path(__file__).resolve().parents[1]
REPO = P5.parents[1]
OUT = REPO / "results" / "w2" / "p5-security-mutations.json"
LOGS = REPO / "results" / "w2" / "p5-security-mutation-logs"

CASES = [
    ("source_no_follow", "p5lib/backend.py", " | os.O_NOFOLLOW", "",
     "test_source_paths.py", "test_capture_rejects_leaf_symlink_before_journaling"),
    ("key_plaintext_match", "p5lib/backend.py", " or handle.read() != plaintext", "",
     "test_journal_auth.py", "test_key_restore_rejects_symlink_and_stale_local_key"),
    ("runtime_secret_filter", "p5lib/backend.py",
     "return {key: value for key, value in env.items() if key not in cls._CONTROLLER_ONLY_ENV}",
     "return dict(env)", "test_journal_auth.py", "test_runtime_child_does_not_inherit_controller_secrets"),
    ("export_recorded_head", "p5lib/controller.py",
     "        verify_recorded_heads()\n        exported =", "        exported =",
     "test_controller.py", "test_explicit_export_rejects_replaced_valid_head"),
    ("snapshot_file_path", "p5lib/backend.py",
     "            _source_parts(file)\n            seen_groups.add(group)",
     "            seen_groups.add(group)", "test_export_snapshot.py",
     "test_snapshot_rejects_unsafe_file_name_before_checkpoint"),
]


def test_copy(root: Path, pattern: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run([sys.executable, "-m", "unittest", "discover", "-s", str(root / "tests"),
                           "-p", pattern, "-q"], cwd=root, text=True, capture_output=True)


def main() -> int:
    LOGS.mkdir(parents=True, exist_ok=True)
    rows = []
    with tempfile.TemporaryDirectory(prefix="w2-p5-mutations-") as temp:
        root = Path(temp)
        shutil.copytree(P5 / "p5lib", root / "p5lib", ignore=shutil.ignore_patterns("__pycache__"))
        shutil.copytree(P5 / "tests", root / "tests", ignore=shutil.ignore_patterns("__pycache__"))
        shutil.copytree(P5 / "tasks", root / "tasks")
        shutil.copytree(P5 / "scripts", root / "scripts", ignore=shutil.ignore_patterns("__pycache__"))
        baseline = test_copy(root, "test_*.py")
        (LOGS / "baseline.log").write_text(baseline.stdout + baseline.stderr)
        if baseline.returncode != 0:
            raise RuntimeError("copied-source P5 baseline failed:\n" + baseline.stdout + baseline.stderr)
        for name, relative, old, new, pattern, assertion in CASES:
            source = root / relative
            original = source.read_text()
            count = original.count(old)
            if count == 0 or (name != "source_no_follow" and count != 1):
                raise RuntimeError(f"{name}: mutation anchor missing or ambiguous")
            try:
                source.write_text(original.replace(old, new, count if name == "source_no_follow" else 1))
                result = test_copy(root, pattern)
            finally:
                source.write_text(original)
            output = result.stdout + result.stderr
            logfile = LOGS / f"{name}.log"
            logfile.write_text(output)
            passed = (result.returncode == 1 and f"FAIL: {assertion} " in output and
                      "ERROR:" not in output)
            rows.append({"name": name, "assertion": assertion, "exit_code": result.returncode,
                         "passed": passed, "log": str(logfile.relative_to(REPO))})
            print(f"{name}: {'PASS' if passed else 'FAIL'}")
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps({"baseline": "passed" if baseline.returncode == 0 else "failed",
                               "baseline_log": str((LOGS / "baseline.log").relative_to(REPO)),
                               "cases": rows, "passed": all(row["passed"] for row in rows)},
                              indent=2) + "\n")
    print(OUT)
    return 0 if all(row["passed"] for row in rows) else 1


if __name__ == "__main__":
    raise SystemExit(main())
