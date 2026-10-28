#!/usr/bin/env python3
"""P5 published-rename gate: a cross-workspace rename of published declarations, atomically.

Runs the scenario of impl/p5/tests/test_rename_batch_live.py against the caller's private
cluster: two P5 working copies, real P1 capture and validator, the store bridge's batch
commands and one T12 transaction, through the router's rename transaction. Stock Lean
suffices: no model-driven worker, Paralean fork or SSH endpoint is needed. The caller starts
its cluster and sources its environment; this script records rename-gate.json in RUN_DIR.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import sys
import time
import unittest

ROOT = Path(__file__).resolve().parents[3]
BRIDGE = ROOT / "impl/p5/store-bridge/target"


class Outcomes(unittest.TextTestResult):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.outcomes: dict[str, dict] = {}
        self.started = 0.0

    def startTest(self, test):
        self.started = time.monotonic()
        super().startTest(test)

    def record(self, test, status: str, detail: str = "") -> None:
        self.outcomes[test.id().rsplit(".", 1)[-1]] = {
            "ok": status == "ok", "status": status, "seconds": round(time.monotonic() - self.started, 2),
            **({"detail": detail[-2000:]} if detail else {})}

    def addSuccess(self, test):
        super().addSuccess(test)
        self.record(test, "ok")

    def addFailure(self, test, err):
        super().addFailure(test, err)
        self.record(test, "failed", self._exc_info_to_string(err, test))

    def addError(self, test, err):
        super().addError(test, err)
        self.record(test, "error", self._exc_info_to_string(err, test))

    def addSkip(self, test, reason):
        super().addSkip(test, reason)
        self.record(test, "skipped", reason)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("run_dir", type=Path)
    args = ap.parse_args()
    if not os.environ.get("PARALEAN_INSTANCE"):
        ap.error("PARALEAN_INSTANCE must identify this run's private cluster")
    run_dir = args.run_dir.resolve()
    run_dir.mkdir(parents=True, exist_ok=False)
    # The release bridge and its fault-injecting test build (cargo --features test-faults).
    os.environ.setdefault("PARALEAN_P5_BRIDGE", str(BRIDGE / "release/paralean-p5-store"))
    os.environ.setdefault("PARALEAN_P5_FAULT_BRIDGE", str(BRIDGE / "test-faults/release/paralean-p5-store"))
    os.environ["TMPDIR"] = str(run_dir)
    sys.path.insert(0, str(ROOT / "impl"))
    from p5.tests import test_rename_batch_live as live  # noqa: E402 - reads the environment above

    result: dict = {"gate": "p5-published-rename", "instance": os.environ["PARALEAN_INSTANCE"],
                    "lean": os.environ.get("PARALEAN_LEAN", "stock"), "tests": {}}
    with open(run_dir / "rename-gate.log", "w") as stream:
        runner = unittest.TextTestRunner(stream=stream, verbosity=2, resultclass=Outcomes)
        outcome = runner.run(unittest.defaultTestLoader.loadTestsFromTestCase(live.PublishedRenameLive))
    result["tests"] = outcome.outcomes
    result["ok"] = bool(outcome.outcomes) and all(t["ok"] for t in outcome.outcomes.values())
    (run_dir / "rename-gate.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"ok": result["ok"], "tests": {k: v["status"] for k, v in result["tests"].items()}}, indent=2))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
