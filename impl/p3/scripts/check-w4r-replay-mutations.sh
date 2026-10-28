#!/usr/bin/env bash
# Each removed replay-horizon guard (docs/w4-rest-log.md design 3) must fail its own
# live FDB regression assertion in tests/w4r_replay.rs.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
# Run against an already configured, isolated FDB/Garage instance (for W4-rest's own
# runs: PARALEAN_INSTANCE=w4r-c source impl/p3/scripts/w4r-env.sh). Never select one here.
: "${PARALEAN_FDB_CLUSTER:?set PARALEAN_FDB_CLUSTER to the isolated test cluster}"
: "${PARALEAN_S3_ENDPOINT:?set PARALEAN_S3_ENDPOINT to the isolated test cluster}"
jobs="${CARGO_BUILD_JOBS:-1}"
cd "$here/../../p2"
cases=(
  'mutate-replay-accept-g-minus-2|retired_generations_are_refused_before_and_after_their_rows_go'
  'mutate-replay-retire-g-minus-1|in_window_duplicates_are_deduplicated_after_compaction'
  'mutate-replay-retire-no-grace|retired_generations_are_refused_before_and_after_their_rows_go'
  'mutate-replay-advance-no-fence|retirement_and_advance_need_the_fenced_leader'
  'mutate-replay-retire-no-fence|retirement_and_advance_need_the_fenced_leader'
  'mutate-replay-retire-gen0|legacy_generation_zero_is_unchanged_and_never_retired'
  'mutate-replay-dedupe-ignores-generation|in_window_duplicates_are_deduplicated_after_compaction'
  'mutate-replay-poll-token-unchecked|retired_poll_tokens_cannot_take_new_work'
  'mutate-replay-accept-legacy|require_replay_generation_refuses_generation_zero'
  # Integration with design 2: a deployment-wide window, re-checked at commit.
  'mutate-replay-per-shard-generation|dynamic_generations_follow_requests_across_moves'
  'mutate-replay-no-commit-check|replay::tests::saves_recheck_the_request_generation|lib'
)
failed=0
for case in "${cases[@]}"; do
  IFS='|' read -r feature test_name target <<<"$case"
  if [[ "${target:-}" == lib ]]; then selector=(--lib); else selector=(--test w4r_replay); fi
  if output="$(cargo test -q -p paralean-control -j "$jobs" --features "$feature" "${selector[@]}" -- --exact "$test_name" --test-threads=1 2>&1)"; then
    echo "SURVIVED  $feature"
    failed=1
  elif grep -Eq "$test_name --- FAILED|test[[:space:]]+$test_name[[:space:]]+[.]{3} FAILED|^---- $test_name ----$" <<<"$output" &&
       grep -Eq 'panicked at|assertion failed|assertion `left == right` failed' <<<"$output"; then
    echo "detected  $feature  ($test_name)"
  else
    echo "ERROR     $feature"
    tail -25 <<<"$output"
    failed=1
  fi
done
# Feature builds must not leave the ordinary controller binary mutated.
cargo build -q -p paralean-control -j "$jobs" || failed=1
exit "$failed"
