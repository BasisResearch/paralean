#!/usr/bin/env bash
# Run the P3 tests against this agent's cluster (scripts/cluster-up.sh). Builds impl/p1 and
# the P1 stores the tests read (core fixtures F01–F13, negatives N1–N6) when missing.
# Extra arguments go to `cargo test` (e.g. `scripts/test.sh --test adversarial`).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
repo="$(cd "$PARALEAN_P3_ROOT/../.." && pwd)"
[ -x "$PARALEAN_BIN" ] || "$repo/impl/p1/scripts/bootstrap.sh"
[ -d "$repo/.runs/p1-core/store/meta" ] || "$repo/impl/p1/scripts/run-core.sh" "$repo/.runs/p1-core" > "$repo/.runs/p1-core.log"
[ -d "$repo/.runs/p1-negative/N3SkipKernel/audit" ] || "$repo/impl/p1/scripts/run-negative.sh" "$repo/.runs/p1-negative" > "$repo/.runs/p1-negative.log"
# The fork-mode validator test needs impl/p1 built against the Paralean fork (fork/build.sh);
# point PARALEAN_P3_FORK_BIN and PARALEAN_P3_FORK_PREFIX at them, or tests/fork.rs skips.
fork_prefix="${PARALEAN_P3_FORK_PREFIX:-$repo/.deps/lean4-paralean/build/release/stage1}"
fork_bin="${PARALEAN_P3_FORK_BIN:-$repo/.runs/p1-fork-build/.lake/build/bin/paralean}"
if [ -x "$fork_prefix/bin/lean" ] && [ -x "$fork_bin" ]; then
  export PARALEAN_P3_FORK_PREFIX="$fork_prefix" PARALEAN_P3_FORK_BIN="$fork_bin"
  if [ ! -d "$repo/.runs/p1-fork-core/store/meta" ]; then
    for f in F01Theorem F04Inductive; do
      PATH="$fork_prefix/bin:$PATH" PARALEAN_SYSROOT="$fork_prefix" "$fork_bin" capture \
        --store "$repo/.runs/p1-fork-core/store" --ws F --root "$repo/corpus/fixtures" "Fixtures/$f.lean" > /dev/null
    done
  fi
fi
cd "$PARALEAN_P2_DIR"
# Each test starts Lean checkers; a few tests at a time keep the shared box usable.
exec cargo test -p paralean-validator-api -p paralean-control "$@" -- --test-threads="${PARALEAN_TEST_THREADS:-3}"
