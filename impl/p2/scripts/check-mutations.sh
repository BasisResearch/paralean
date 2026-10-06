#!/usr/bin/env bash
# Guard-removal mutations (the implementation counterpart of verification/TLA-GUARDS.md):
# each cargo feature deletes one guard; the listed tests must then FAIL. A mutation that
# no test detects is reported and makes this script exit 1. ONLY=<feature prefix> runs a
# subset. The anti-entropy cases need PARALEAN_PEER_INSTANCE (as scripts/test.sh).
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
cd "$here/.."
# feature | test target | test name (exact)
cases=(
  "mutate-no-owner-check|guards|t1_rejects_non_owner"
  "mutate-no-owner-check|fixtures|fixture_stale_owner_publish_after_reassignment"
  "mutate-no-epoch-fence|guards|t1_rejects_stale_epoch_after_reassignment"
  "mutate-no-head-cas|guards|t1_head_compare_and_swap"
  "mutate-no-head-cas|faults|concurrent_writers_multi_threaded"
  "mutate-cert-outside-publish|faults|publisher_crash_right_after_publish_leaves_head_discoverable"
  "mutate-unfenced-commit|fixtures|fixture_stale_writer_after_rotation"
  "mutate-unfenced-commit|fixtures|fixture_put_before_rotation_acked_after"
  "mutate-unfenced-commit|property|random_interleavings_keep_store_invariants"
  "mutate-no-parent-check|fixtures|fixture_orphan_commit_rejected"
  "mutate-no-parent-check|guards|t5_fenced_commit_and_its_guards"
  "mutate-tombstone-cert-outside|tombstones|tombstone_faults_resolve"
  "mutate-tombstone-no-target-check|tombstones|t8_tombstone_guards"
  "mutate-tombstone-no-author-check|tombstones|t8_tombstone_guards"
  "mutate-tombstone-raw-scan|tombstones|fixture_uncertified_tombstone_is_ignored"
  "mutate-render-ignores-tombstones|tombstones|fixture_tombstoned_and_superseded_leave_the_rendered_file"
  "mutate-render-ignores-tombstones|property|random_interleavings_keep_store_invariants"
  "mutate-render-ignores-supersession|tombstones|fixture_tombstoned_and_superseded_leave_the_rendered_file"
  "mutate-receive-unverified-certs|antientropy|receiver_rejects_corrupt_forged_and_untrusted"
  "mutate-receive-foreign-cert|antientropy|sync_converges_between_two_clusters"
  "mutate-receive-overwrite-marker|antientropy|marker_conflict_is_reported_not_overwritten"
  "mutate-receive-no-payload-ack|antientropy|corrupt_payloads_at_rest_are_repaired_or_wait"
)
fail=0
for c in "${cases[@]}"; do
  IFS='|' read -r feat target name <<<"$c"
  case "$feat" in "${ONLY:-}"*) ;; *) continue ;; esac
  out="$(PROPTEST_CASES=${PROPTEST_CASES:-40} "$here/test.sh" -q -p paralean-store --features "$feat" --test "$target" -- --exact "$name" 2>&1)"
  if grep -q "$name --- FAILED\|test $name ... FAILED" <<<"$out"; then
    echo "detected  $feat  by $target::$name"
  elif grep -q "test result: ok. 1 passed\|^1 passed\|^\.$" <<<"$out"; then
    echo "SURVIVED  $feat  $target::$name passed with the guard removed"; fail=1
  else
    echo "ERROR     $feat  $target::$name (no verdict)"; echo "$out" | tail -20; fail=1
  fi
done
exit $fail
