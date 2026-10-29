#!/usr/bin/env bash
# W4-rest design 2: each removed dynamic-topology guard must fail its own live FDB
# regression in tests/w4r_shards.rs, which passes with every guard in place.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
# Run against an already configured, isolated FDB/Garage instance (for W4-rest:
# PARALEAN_INSTANCE=w4r-b source impl/p3/scripts/w4r-env.sh). Never select one here.
: "${PARALEAN_FDB_CLUSTER:?set PARALEAN_FDB_CLUSTER to the isolated test cluster}"
: "${PARALEAN_S3_ENDPOINT:?set PARALEAN_S3_ENDPOINT to the isolated test cluster}"
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"
cd "$here/../../p2"
cases=(
  'mutate-shard-export-keeps-source|move_preserves_every_job_exactly_once'
  'mutate-shard-issue-job-no-gc-refs|dynamic_pending_jobs_protect_their_objects'
  'mutate-shard-flip-without-handoff|move_preserves_every_job_exactly_once'
  'mutate-shard-dest-serves-moving|move_preserves_every_job_exactly_once'
  'mutate-shard-import-no-state-check|second_import_does_not_resurrect_work'
  'mutate-shard-no-fence-reserve|stale_source_cannot_write_moved_buckets'
  'mutate-shard-no-fence-assign|stale_source_cannot_write_moved_buckets'
  'mutate-shard-no-fence-issue-job|stale_source_cannot_write_moved_buckets'
  'mutate-shard-no-fence-receipt|stale_source_cannot_write_moved_buckets'
  'mutate-shard-no-fence-recovery|stale_source_cannot_write_moved_buckets'
  'mutate-shard-no-drain|inflight_validation_is_drained_before_export'
  'mutate-shard-export-no-lease|stale_leader_export_is_fenced_by_lease'
  'mutate-shard-save-no-cas|snapshot_saves_compare_the_loaded_generation'
  'mutate-shard-remove-owning|add_shard_takes_buckets_and_remove_shard_retires'
  'mutate-shard-retired-lease-live|add_shard_takes_buckets_and_remove_shard_retires'
  'mutate-shard-no-cross-replay|compacted_work_and_poll_tokens_resolve_across_shards'
  'mutate-shard-no-poll-rows|compacted_work_and_poll_tokens_resolve_across_shards'
  # Atomic batches (docs/atomic-pub-log.md) on dynamic shards.
  'mutate-shard-batch-no-bucket-check|dynamic_batches_issue_on_one_shard_and_drain_their_buckets'
  'mutate-shard-batch-own-bucket|dynamic_batches_issue_on_one_shard_and_drain_their_buckets'
  'mutate-shard-batch-no-drain|dynamic_batches_issue_on_one_shard_and_drain_their_buckets'
)
failed=0
# Every detecting test must pass with all guards in place.
names=()
for case in "${cases[@]}"; do names+=("${case#*|}"); done
mapfile -t names < <(printf '%s\n' "${names[@]}" | sort -u)
for test_name in "${names[@]}"; do
  if cargo test -q -p paralean-control --test w4r_shards -- --exact "$test_name" --test-threads=1 >/dev/null 2>&1; then
    echo "baseline  $test_name passes"
  else
    echo "ERROR     baseline $test_name fails without mutations"
    failed=1
  fi
done
for case in "${cases[@]}"; do
  IFS='|' read -r feature test_name <<<"$case"
  if output="$(cargo test -q -p paralean-control --features "$feature" --test w4r_shards -- --exact "$test_name" --test-threads=1 2>&1)"; then
    echo "SURVIVED  $feature  w4r_shards::$test_name"
    failed=1
  elif grep -Eq "$test_name --- FAILED|test[[:space:]]+$test_name[[:space:]]+[.]{3}.*FAILED|^---- $test_name ----$" <<<"$output" &&
       grep -Eq 'panicked at' <<<"$output" && ! grep -Eq '^error\[E[0-9]+\]|could not compile' <<<"$output"; then
    why="$(grep -A1 'panicked at' <<<"$output" | sed -n 2p | cut -c1-140)"
    echo "detected  $feature  by w4r_shards::$test_name  ($why)"
  else
    echo "ERROR     $feature"
    tail -25 <<<"$output"
    failed=1
  fi
done
# Feature builds must not leave the ordinary controller binary mutated.
cargo build -q -p paralean-control || failed=1
exit "$failed"
