#!/usr/bin/env bash
# Run against an already configured, isolated FDB/Garage instance.
set -uo pipefail
: "${PARALEAN_FDB_CLUSTER:?set PARALEAN_FDB_CLUSTER to the isolated test cluster}"
: "${PARALEAN_S3_ENDPOINT:?set PARALEAN_S3_ENDPOINT to the isolated test cluster}"
cd "$(dirname "$0")/../../p2"
cases=(
  'mutate-no-term-fence|expired_same_holder_cannot_reuse_old_term_or_write_during_gap'
  'mutate-no-logical-expiry|expired_same_holder_cannot_reuse_old_term_or_write_during_gap'
  'mutate-no-shard-catalog|shard_terms_and_target_catalog_are_independent'
  'mutate-no-shard-catalog|queued_target_claim_blocks_another_shards_assignment'
  'mutate-no-shard-topology|different_topology_is_rejected_before_a_leader_can_write'
  'mutate-no-shard-topology|legacy_controller_state_requires_offline_migration'
  'mutate-no-validation-catalog|target_free_job_routes_its_cancellation_to_issuing_shard'
  'mutate-no-receipt-shard-check|target_free_job_routes_its_cancellation_to_issuing_shard'
  'mutate-no-unowned-reassign|unowned_fence_can_be_taken_by_later_registered_worker'
  'mutate-no-task-claim-check|task_and_shard_claims_are_mutually_exclusive|p5_claims'
)
fail=0
for case in "${cases[@]}"; do
  IFS='|' read -r feature name test <<<"$case"
  test="${test:-durable}"
  output="$(cargo test -q -j1 -p paralean-control --features "$feature" --test "$test" -- --exact "$name" 2>&1)"
  if rg -q 'assertion failed|assertion `left == right` failed' <<<"$output" && rg -q "${name} --- FAILED|test\s+${name}\s+\.\.\. FAILED" <<<"$output"; then
    echo "detected  $feature  by $test::$name"
  else
    echo "SURVIVED  $feature  $test::$name"
    echo "$output" | tail -20
    fail=1
  fi
done
# Integration-test builds also replace target/debug/paralean-p3. Leave the
# ordinary command with every guard enabled after exercising the mutations.
cargo build -q -j1 -p paralean-control || fail=1
exit "$fail"
