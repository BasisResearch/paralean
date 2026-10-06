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
)
fail=0
for c in "${cases[@]}"; do
  IFS='|' read -r feat target name <<<"$c"
  out="$(cargo test -q -p paralean-control --features "$feat" --test "$target" -- --exact "$name" 2>&1)"
  if grep -q "$name --- FAILED\|test $name ... FAILED\|^test result: FAILED" <<<"$out"; then
    echo "detected  $feat  by $target::$name"
  elif grep -q "test result: ok. 1 passed" <<<"$out"; then
    echo "SURVIVED  $feat  $target::$name passed with the check removed"; fail=1
  else
    echo "ERROR     $feat  $target::$name (no verdict)"; echo "$out" | tail -20; fail=1
  fi
done
exit $fail
