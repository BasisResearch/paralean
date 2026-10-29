#!/usr/bin/env bash
# W4-rest store GC (docs/w4-rest-log.md Design 1): each removed guard must fail its named
# test. Store cases run live against an already configured private instance (for W4-rest:
# source impl/p3/scripts/w4r-env.sh, then scripts/up.sh); never select an instance here.
# Gateway cases are unit tests.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
: "${PARALEAN_INSTANCE:?source impl/p3/scripts/w4r-env.sh (a private w4r-* instance)}"
case "$PARALEAN_INSTANCE" in w4r-*) ;; *) echo "refusing instance $PARALEAN_INSTANCE (not w4r-*)" >&2; exit 2 ;; esac
: "${PARALEAN_FDB_CLUSTER:?set PARALEAN_FDB_CLUSTER to the isolated test cluster}"
: "${PARALEAN_S3_ENDPOINT:?set PARALEAN_S3_ENDPOINT to the isolated test cluster}"
jobs="${CARGO_BUILD_JOBS:-4}"
cd "$here/.."
# The live store tests start their own gateway from the ordinary (unmutated) binary.
cargo build -q -p s3-guard -j "$jobs" || exit 1
cases=(
  'paralean-store|mutate-storegc-doom-no-ref-check|store_gc|gc_never_collects_published_tombstoned_moved_or_revised'
  'paralean-store|mutate-storegc-doom-no-grace|store_gc|gc_collects_staged_orphans_only_after_grace'
  'paralean-store|mutate-storegc-doom-no-ocert-clear|store_gc|gc_t5_t6_refuse_a_doomed_snapshot'
  'paralean-store|mutate-storegc-t1-no-doomed-check|store_gc|gc_t1_doom_race_both_orders'
  'paralean-store|mutate-storegc-ref-no-gone-check|store_gc|gc_t1_doom_race_both_orders'
  'paralean-store|mutate-storegc-t6-no-doomed-check|store_gc|gc_t5_t6_refuse_a_doomed_snapshot'
  'paralean-store|mutate-storegc-ae-serves-gone|store_gc|gc_ae_never_serves_collected_objects_or_retired_records'
  'paralean-store|mutate-storegc-retire-no-fence-check|store_gc|gc_dead_catalogue_record_retired_and_recovery'
  'paralean-store|mutate-storegc-job-release-no-check|store_gc|gc_pending_jobs_protect_their_objects'
  'paralean-store|mutate-storegc-ae-pending-no-ref|store_gc|gc_pending_ae_events_protect_their_objects'
  # Atomic batches (T12; docs/atomic-pub-log.md).
  'paralean-store|mutate-storegc-batch-no-record-ref|store_gc|gc_batches_protect_members_and_revive'
  'paralean-store|mutate-storegc-batch-no-member-refs|store_gc|gc_batches_protect_members_and_revive'
  'paralean-store|mutate-storegc-batch-no-revival|store_gc|gc_batches_protect_members_and_revive'
  's3-guard|mutate-storegc-guard-no-mark-check|unit|tests::gc_content_delete_needs_doomed_mark'
  's3-guard|mutate-storegc-guard-any-principal|unit|tests::gc_content_delete_needs_gc_principal'
  's3-guard|mutate-storegc-guard-gone-with-inflight|unit|tests::gc_gone_waits_for_unanswered_attempts'
)
failed=0
for case in "${cases[@]}"; do
  IFS='|' read -r package feature target test_name <<<"$case"
  if [[ "$target" == unit ]]; then selector=(); else selector=(--test "$target"); fi
  # The unmutated test must pass first, so a detection is the mutation's doing.
  if ! base="$(cargo test -q -p "$package" -j "$jobs" "${selector[@]}" -- --exact "$test_name" --test-threads=1 2>&1)"; then
    echo "BASELINE  $feature ($test_name fails without the mutation)"
    tail -20 <<<"$base"
    failed=1
    continue
  fi
  if output="$(cargo test -q -p "$package" -j "$jobs" --features "$feature" "${selector[@]}" -- --exact "$test_name" --test-threads=1 2>&1)"; then
    echo "SURVIVED  $feature"
    failed=1
  elif grep -Eq "^---- $test_name( stdout)? ----$|test $test_name \.\.\. FAILED" <<<"$output" && grep -q "panicked" <<<"$output"; then
    echo "detected  $feature  by $test_name"
  else
    echo "ERROR     $feature"
    tail -20 <<<"$output"
    failed=1
  fi
done
# Restore the ordinary test binaries after feature-gated builds.
cargo test -q -p paralean-store -j "$jobs" --test store_gc --no-run >/dev/null 2>&1 || failed=1
exit "$failed"
