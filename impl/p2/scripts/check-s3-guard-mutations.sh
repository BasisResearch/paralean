#!/usr/bin/env bash
# Each deliberately removed delete guard must make the unit tests fail.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
cd "$here/.."
failed=0
cases=(
  'mutate-no-gc-principal-check|gc_key_only_allows_signed_object_delete_candidate'
  'mutate-no-bucket-delete-check|gc_key_only_allows_signed_object_delete_candidate'
  'mutate-no-query-key-decode|decodes_query_keys_before_denying_destructive_subresources'
)
for case in "${cases[@]}"; do
  IFS='|' read -r feature test_name <<<"$case"
  if output="$(cargo test -p s3-guard -j 1 --features "$feature" -- --exact "tests::$test_name" 2>&1)"; then
    echo "SURVIVED  $feature"
    failed=1
  elif grep -q "test tests::$test_name ... FAILED" <<<"$output"; then
    echo "detected  $feature"
  else
    echo "ERROR     $feature"
    tail -20 <<<"$output"
    failed=1
  fi
done
exit "$failed"
