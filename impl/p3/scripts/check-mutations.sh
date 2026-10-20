#!/usr/bin/env bash
# Guard-removal mutations for the P3 receipt binding and control plane (the counterpart of
# PUBLICATION-RECEIPTS.md's `unreceipted_staging`/`unreceipted_publication` and
# TARGET-NAMES.md's `target_no_epoch_fence`/`target_no_owner_check` guards): each cargo
# feature deletes one check; the listed test must then FAIL. A mutation no test detects is
# reported and makes this script exit 1. Runs against scripts/cluster-up.sh's cluster.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
cd "$PARALEAN_P2_DIR"
# feature | test target | test name (exact)
cases=(
  "paralean-store/mutate-no-receipt-check|adversarial|forged_receipts_fail_closed"
  "paralean-store/mutate-no-receipt-check|adversarial|worker_that_skips_validation_cannot_publish"
  "paralean-store/mutate-no-receipt-check|adversarial|receipt_for_another_group_policy_checker_base_or_target_fails_closed"
  "paralean-store/mutate-no-epoch-binding|adversarial|receipt_for_another_epoch_fails_closed"
  "paralean-store/mutate-issuer-signs-targets|adversarial|job_issuer_keys_sign_target_free_envelopes_only"
  "paralean-store/mutate-no-revocation-check|adversarial|revoked_or_retired_validator_key_fails_closed"
  "paralean-store/mutate-no-cancel-check|adversarial|receipt_for_another_or_cancelled_request_fails_closed"
  "paralean-store/mutate-no-undeclared-target|adversarial|stale_owner_after_lease_expiry_cannot_publish"
  "mutate-no-dispatch-owner-check|adversarial|stale_owner_after_lease_expiry_cannot_publish"
  "mutate-no-lease-reassign|adversarial|stale_owner_after_lease_expiry_cannot_publish"
  "mutate-no-lease-reassign|processes|killed_owner_is_replaced_and_the_target_published"
  "mutate-no-request-dedup|control|duplicate_and_retried_jobs_are_deduplicated"
  "mutate-validator-skips-dep-check|adversarial|dependency_must_be_published_with_a_receipt"
  "mutate-validator-ignores-axioms|adversarial|validator_enforces_the_envelope_policy"
  "mutate-no-checker-sandbox|sandbox|checker_cannot_read_secrets_write_outside_or_use_network"
  "mutate-no-checker-sandbox|sandbox|native_lean_tactic_cannot_reach_host"
  "mutate-no-checker-seccomp|sandbox|checker_cannot_read_secrets_write_outside_or_use_network"
  "mutate-no-checker-disk-limit|sandbox|checker_disk_budget_is_tmpfs_enospc_and_rlimit_fsize"
  "mutate-no-checker-fsize-limit|sandbox|checker_disk_budget_is_tmpfs_enospc_and_rlimit_fsize"
  "mutate-no-checker-process-limit|sandbox|checker_process_count_is_hard_limited"
  "mutate-no-checker-memory-limit|sandbox|checker_memory_rss_poll_catches_sustained_hog_without_cgroup"
  "mutate-no-checker-cgroup|sandbox|checker_memory_cgroup_hard_limit_kills_fast_burst"
  "mutate-no-checker-cpu-limit|sandbox|checker_cpu_budget_kills_busy_loop"
  "mutate-checker-config-unsandboxed|sandbox|production_config_enables_the_sandbox"
  "mutate-checker-fallback-unsandboxed|sandbox|sandbox_fails_closed_when_bwrap_is_missing"
  "mutate-checker-seccomp-allows-io-uring|sandbox|checker_io_uring_is_blocked"
  "mutate-unbounded-checker-output|checker_protocol|cold_output_flood_cannot_fill_validator_memory"
  "mutate-drop-invalid-axiom|checker_protocol|cold_malformed_axiom_cannot_be_silently_dropped"
  "mutate-unbounded-completed-slots|lib|validator::completed_tests::completed_receipt_cache_is_bounded"
  # W2 control-plane review (results/w2/control-fixes).
  "mutate-unchecked-gid|adversarial|hostile_capsule_gid_is_refused_before_any_write"
  "paralean-store/mutate-unscoped-job-keys|control|request_ids_are_scoped_per_workspace"
  "mutate-unscoped-validator-slots|control|validator_slots_are_scoped_by_issuer_and_workspace"
  "mutate-attached-validation|control|dropped_validation_still_finishes_and_releases_its_resources"
  "mutate-validator-checks-issuer-targets|adversarial|job_issuer_keys_sign_target_free_envelopes_only"
  "mutate-recover-every-tick|control|inconclusive_recovery_is_bounded"
  "mutate-keep-old-snapshot-chunks|durable|superseded_snapshot_chunks_are_cleared_with_the_head_swap"
  "mutate-role-keys-unchecked|processes|processes_refuse_key_files_with_seeds_of_other_roles"
)
fail=0
for c in "${cases[@]}"; do
  IFS='|' read -r feat target name <<<"$c"
  if [ "$target" = lib ]; then
    out="$(cargo test -q -j "${PARALEAN_CARGO_JOBS:-4}" -p paralean-control --features "$feat" --lib -- --exact "$name" 2>&1)"
  else
    out="$(cargo test -q -j "${PARALEAN_CARGO_JOBS:-4}" -p paralean-control --features "$feat" --test "$target" -- --exact "$name" 2>&1)"
  fi
  if grep -q "$name --- FAILED\|test $name ... FAILED\|^test result: FAILED" <<<"$out"; then
    echo "detected  $feat  by $target::$name"
  elif grep -q "test result: ok. 1 passed" <<<"$out"; then
    echo "SURVIVED  $feat  $target::$name passed with the check removed"; fail=1
  else
    echo "ERROR     $feat  $target::$name (no verdict)"; echo "$out" | tail -20; fail=1
  fi
done
exit $fail
