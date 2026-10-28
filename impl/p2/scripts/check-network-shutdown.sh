#!/usr/bin/env bash
# Check the FDB process-exit stop/join contract and its guard-removal mutation.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
out="${OUT:-$here/../../../results/w2/finish/chaos/network-shutdown}"
mkdir -p "$out"
out="$(cd "$out" && pwd)"
cd "$here/.."
test_name=meta::lifecycle_tests::network_stops_before_process_exit
cargo test -j 1 -p paralean-store --lib "$test_name" -- --exact \
  > "$out/normal.log" 2>&1
if cargo test -j 1 -p paralean-store --lib --features mutate-no-network-shutdown \
    "$test_name" -- --exact > "$out/mutation.log" 2>&1; then
  echo "shutdown mutation survived" >&2
  exit 1
fi
if ! grep -q 'shutdown did not stop and join FDB' "$out/mutation.log"; then
  echo "mutation failed for an unrelated reason; see $out/mutation.log" >&2
  exit 1
fi
echo "explicit shutdown PASS; no-shutdown mutation killed ($out)"
