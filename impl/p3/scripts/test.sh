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
cd "$PARALEAN_P2_DIR"
# Each test starts Lean checkers; a few tests at a time keep the shared box usable.
exec cargo test -p paralean-validator-api -p paralean-control "$@" -- --test-threads="${PARALEAN_TEST_THREADS:-3}"
