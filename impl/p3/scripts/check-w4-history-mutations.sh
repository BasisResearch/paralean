#!/usr/bin/env bash
# Each removed history guard must fail its own live FDB regression assertion.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
# Run against an already configured, isolated FDB/Garage instance (for W4's own
# runs: source impl/p3/scripts/w4-env.sh first). Never select an instance here.
: "${PARALEAN_FDB_CLUSTER:?set PARALEAN_FDB_CLUSTER to the isolated test cluster}"
: "${PARALEAN_S3_ENDPOINT:?set PARALEAN_S3_ENDPOINT to the isolated test cluster}"
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"
cd "$here/../../p2"
cases=(
  'mutate-history-no-work-replay|replay_survives_restart_with_gc_disabled_and_poll_tokens_do_not_steal_work'
  'mutate-history-no-poll-replay|replay_survives_restart_with_gc_disabled_and_poll_tokens_do_not_steal_work'
  'mutate-history-no-grace|terminal_history_obeys_grace_and_preserves_active_and_retained_snapshot'
  'mutate-history-no-term-fence|stale_history_compactor_cannot_prune'
  'mutate-history-omit-work-marker|history_batch_commit_survives_crash_before_memory_update'
  'mutate-history-omit-poll-marker|history_batch_commit_survives_crash_before_memory_update'
  'mutate-history-no-cancel-overlay|replay_survives_restart_with_gc_disabled_and_poll_tokens_do_not_steal_work'
  'mutate-history-no-fair-scan|active_poll_tokens_cannot_starve_terminal_work'
  'mutate-history-prune-active|terminal_history_obeys_grace_and_preserves_active_and_retained_snapshot'
  'mutate-history-no-opt-in|default_disabled_preserves_history_after_logical_grace'
  'mutate-history-no-work-identity|replay_survives_restart_with_gc_disabled_and_poll_tokens_do_not_steal_work'
  'mutate-history-no-poll-worker|replay_survives_restart_with_gc_disabled_and_poll_tokens_do_not_steal_work'
  'mutate-history-no-row-conflict|history_replay_rows_reject_conflicting_rewrites'
  'mutate-history-no-terminal-grace|old_poll_token_waits_for_its_work_to_settle_and_age'
  'mutate-history-no-poll-epoch|old_poll_token_cannot_claim_new_epoch_on_same_worker'
)
failed=0
for case in "${cases[@]}"; do
  IFS='|' read -r feature test_name <<<"$case"
  if output="$(cargo test -q -p paralean-control -j 1 --features "$feature" --test w4_history -- --exact "$test_name" --test-threads=1 2>&1)"; then
    echo "SURVIVED  $feature"
    failed=1
  elif grep -Eq "$test_name --- FAILED|test[[:space:]]+$test_name[[:space:]]+[.]{3} FAILED" <<<"$output" &&
       grep -Eq 'panicked at|assertion failed|assertion `left == right` failed' <<<"$output"; then
    echo "detected  $feature"
  else
    echo "ERROR     $feature"
    tail -25 <<<"$output"
    failed=1
  fi
done
# Feature builds must not leave the ordinary controller binary mutated.
cargo build -q -p paralean-control -j 1 || failed=1
exit "$failed"
