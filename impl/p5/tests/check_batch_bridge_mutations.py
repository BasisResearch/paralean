#!/usr/bin/env python3
"""Remove each store-bridge batch guard (a `mutate-*` feature) and require its live test to fail.

Each mutant is built into its own feature set of one shared target directory, then the
guard's test in test_rename_batch_live.py runs against it. Only an assertion failure counts:
an error (a mutant that no longer builds or a broken setup) is not a detection. Needs the
private instance of .runs/ap/p5-env.sh.
"""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys

P5 = Path(__file__).resolve().parents[1]
BRIDGE = P5 / "store-bridge"
TARGET = BRIDGE / "target" / "mutants"
TEST = "p5.tests.test_rename_batch_live.PublishedRenameLive."
CASES = [
    ("mutate-batch-any-owner", "test_guard_validate_refuses_a_target_of_another_workspace"),
    ("mutate-batch-any-epoch", "test_guard_validate_refuses_a_stale_dispatch_epoch"),
    ("mutate-batch-any-replaced", "test_guard_validate_refuses_replacing_another_workspaces_declaration"),
    ("mutate-batch-any-deleter", "test_guard_validate_refuses_deleting_another_workspaces_declaration"),
    ("mutate-batch-sign-any-keys", "test_guard_sign_takes_only_the_workspaces_own_key_file"),
    ("mutate-batch-sign-unsigned-intent", "test_guard_sign_refuses_an_intent_not_signed_by_the_controller"),
    ("mutate-batch-sign-unbound-job", "test_guard_sign_refuses_a_job_bound_to_another_batch"),
]


def run_test(name: str, bridge: Path) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, "-m", "unittest", TEST + name], cwd=P5.parent,
                          env={**os.environ, "PARALEAN_P5_BRIDGE": str(bridge)},
                          capture_output=True, text=True, timeout=900)


def main() -> int:
    if not os.environ.get("PARALEAN_INSTANCE"):
        raise SystemExit("source .runs/ap/p5-env.sh first")
    release = BRIDGE / "target" / "release" / "paralean-p5-store"
    for _, test in CASES:
        baseline = run_test(test, release)
        if baseline.returncode or "OK" not in baseline.stderr or "skipped" in baseline.stderr:
            raise AssertionError(f"baseline failed before mutation: {test}\n{baseline.stderr[-3000:]}")
    for feature, test in CASES:
        build = subprocess.run(["cargo", "build", "--release", "--features", feature,
                                "--target-dir", str(TARGET)], cwd=BRIDGE, capture_output=True, text=True)
        if build.returncode:
            raise AssertionError(f"mutant does not build: {feature}\n{build.stderr[-3000:]}")
        result = run_test(test, TARGET / "release" / "paralean-p5-store")
        if result.returncode == 0 or "FAIL:" not in result.stderr or "ERROR:" in result.stderr:
            raise AssertionError(f"expected assertion failure missing for {feature}:\n{result.stderr[-3000:]}")
        print(f"KILLED {feature} by {test}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
