#!/usr/bin/env python3
"""Disposable demonstration of P5's remaining same-UID worker read access."""

from __future__ import annotations

import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from p5lib.task import from_dict
from p5lib.workers import run


def main() -> None:
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp)
        sentinel = root / "controller-only-sentinel.txt"
        sentinel.write_text("disposable-controller-sentinel")
        workspace = root / "w0"
        (workspace / "work").mkdir(parents=True)
        task = from_dict({
            "task": {"id": "read-boundary"},
            "controller": {"workers": 1},
            "worker": {"kind": "command", "command": [sys.executable, "-c",
                "import pathlib,sys; print(pathlib.Path(sys.argv[1]).read_text())", str(sentinel)]},
            "targets": [{"name": "P5.test", "statement": "True", "file": "A.lean"}],
        })
        result = run(task, task.targets[0], "w0", 1, workspace)
        exposed = "disposable-controller-sentinel" in Path(result.log).read_text()
        print(f"worker_exit={result.returncode} read_outside_workspace={exposed}")
        if result.returncode != 0 or not exposed:
            raise SystemExit("the reproduction did not exercise the expected boundary")


if __name__ == "__main__":
    main()
