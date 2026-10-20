#!/usr/bin/env bash
# Each removed controller GC guard must fail its live FoundationDB regression test.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
# Run against an already configured, isolated FDB/Garage instance (for W4's own
# runs: source impl/p3/scripts/w4-env.sh first). Never select an instance here.
: "${PARALEAN_FDB_CLUSTER:?set PARALEAN_FDB_CLUSTER to the isolated test cluster}"
: "${PARALEAN_S3_ENDPOINT:?set PARALEAN_S3_ENDPOINT to the isolated test cluster}"
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"
cd "$here/../../p2"
cases=(
  'mutate-gc-no-head-check|gc|gc_rechecks_current_head_and_rejects_stale_leader'
  'mutate-gc-no-retention-check|gc|gc_requires_opt_in_grace_and_unpinned_superseded_root'
  'mutate-gc-no-grace-check|gc|gc_requires_opt_in_grace_and_unpinned_superseded_root'
  'mutate-gc-no-opt-in-check|gc|gc_requires_opt_in_grace_and_unpinned_superseded_root'
  'mutate-gc-no-candidate-check|lib|gc::tests::stale_scanned_candidate_cannot_collect_new_retirement'
  'mutate-gc-modulo-schedule|lib|controller::gc_schedule_tests::gc_schedule_progresses_when_other_replica_takes_every_multiple_of_eight'
)
failed=0
for case in "${cases[@]}"; do
  IFS='|' read -r feature target test_name <<<"$case"
  if [[ "$target" == lib ]]; then
    selector=(--lib)
  else
    selector=(--test "$target")
  fi
  if output="$(cargo test -q -p paralean-control -j 1 --features "$feature" "${selector[@]}" -- --exact "$test_name" 2>&1)"; then
    echo "SURVIVED  $feature"
    failed=1
  elif grep -Fq "$test_name --- FAILED" <<<"$output" &&
       grep -Eq 'assertion failed|assertion `left == right` failed' <<<"$output"; then
    echo "detected  $feature"
  else
    echo "ERROR     $feature"
    tail -20 <<<"$output"
    failed=1
  fi
done
# Restore the ordinary binary after feature-gated integration-test builds.
cargo build -q -p paralean-control -j 1 || failed=1
exit "$failed"
