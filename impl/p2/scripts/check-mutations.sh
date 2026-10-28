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
  "mutate-receive-no-receipt-check|antientropy|received_groups_need_a_receipt_valid_here"
  "mutate-receive-no-receipt-check|antientropy|receiver_rejects_corrupt_forged_and_untrusted"
  "mutate-no-revocation-check|antientropy|received_groups_need_a_receipt_valid_here"
  "mutate-no-revocation-check|tombstones|t8_named_receipt_respects_revocation"
  "mutate-catalogue-no-source-proof|network|catalogue_guards_reject_forged_source_token_and_object_proofs|paralean-ae-service"
  "mutate-catalogue-no-token-proof|network|catalogue_guards_reject_forged_source_token_and_object_proofs|paralean-ae-service"
  "mutate-catalogue-no-object-proof|network|catalogue_guards_reject_forged_source_token_and_object_proofs|paralean-ae-service"
  "mutate-catalogue-no-parent|network|catalogue_child_waits_for_parent_and_ignores_receiver_fence|paralean-ae-service"
  "mutate-checkpoint-no-buildable|guards|t5_unresolved_collision_rejects_every_checkpoint_path"
  "mutate-checkpoint-no-current|guards|t5_unresolved_collision_rejects_every_checkpoint_path"
  "mutate-checkpoint-partial-group|guards|t5_partial_atomic_group_cannot_hide_a_colliding_name"
  "mutate-checkpoint-no-deps|guards|t5_dependency_closure_rejects_omitted_colliding_group"
  "mutate-position-group-wide-delete|positions|certified_move_preserves_registry_and_converges_with_tombstone"
  "mutate-position-receive-conflict|antientropy|moved_position_and_tombstone_converge_between_replicas"
  "mutate-position-no-tombstone-guard|positions|move_rejects_uncertified_tombstone"
  "mutate-position-bad-root|positions|move_rejects_forged_root_path"
  "mutate-position-no-anchor|positions|move_rejects_uncertified_anchor"
  "mutate-position-lineage|positions|move_rejects_changed_lineage"
  "mutate-position-cross-file|positions|move_rejects_cross_file_placement"
  "mutate-position-author|positions|controller_deleted_position_cannot_be_reinserted_by_author"
  "mutate-no-agent-registry|authority|forged_author_and_revoked_agent_key_fail_at_t1"
  "mutate-agent-no-revocation|authority|forged_author_and_revoked_agent_key_fail_at_t1"
  "mutate-agent-foreign-rotation|authority|rotated_writer_key_is_accepted_by_immutable_federation_roster_only_with_home_grant"
  "mutate-agent-historical-t8|authority|old_signer_cannot_make_fresh_tombstone_under_rotated_ring"
  "mutate-no-controller-fence|authority|controller_delete_requires_local_signature_and_current_fence"
  "mutate-controller-no-source|authority|controller_delete_relay_keeps_origin_authority"
  "mutate-controller-no-origin|authority|foreign_controller_cannot_claim_another_origins_writer_certificate"
)
fail=0
for c in "${cases[@]}"; do
  IFS='|' read -r feat target name package <<<"$c"
  package="${package:-paralean-store}"
  case "$feat" in "${ONLY:-}"*) ;; *) continue ;; esac
  out="$(PROPTEST_CASES=${PROPTEST_CASES:-40} "$here/test.sh" -q -p "$package" --features "paralean-store/$feat" --test "$target" -- --exact "$name" 2>&1)"
  if grep -Eq "test[[:space:]]+${name}[[:space:]]+(---|\.\.\.)[[:space:]]+FAILED" <<<"$out"; then
    echo "detected  $feat  by $target::$name"
  elif grep -q "test result: ok. 1 passed\|^1 passed\|^\.$" <<<"$out"; then
    echo "SURVIVED  $feat  $target::$name passed with the guard removed"; fail=1
  else
    echo "ERROR     $feat  $target::$name (no verdict)"; echo "$out" | tail -20; fail=1
  fi
done
exit $fail
