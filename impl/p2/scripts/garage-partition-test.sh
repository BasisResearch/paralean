#!/usr/bin/env bash
# Exercise a live Garage RPC cut on an existing, isolated three-node instance.
# Requires proc.sh garage-split/garage-heal and PARALEAN_GARAGE_NETSPLIT=1.
# Uses each node's S3 API directly so a gateway retry cannot hide which side served a request.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
[ -n "$PARALEAN_INSTANCE" ] || { echo 'set PARALEAN_INSTANCE; refusing the default cluster' >&2; exit 2; }
[ "$PARALEAN_GARAGE_NODES" = 3 ] && [ "$PARALEAN_GARAGE_REPLICATION" = 3 ] || {
  echo 'needs three Garage nodes with replication 3' >&2; exit 2;
}
[ "${PARALEAN_GARAGE_NETSPLIT:-0}" = 1 ] || {
  echo 'needs PARALEAN_GARAGE_NETSPLIT=1 on this instance' >&2; exit 2;
}
command -v aws >/dev/null || { echo 'aws CLI is required' >&2; exit 2; }

H="$PARALEAN_HOME"
[ -f "$H/run/garage-netsplit.pid" ] && kill -0 "$(cat "$H/run/garage-netsplit.pid")" 2>/dev/null || {
  echo 'garage-netsplit is not running' >&2; exit 2;
}
out="${OUT:-$here/../../../results/p2/garage-partition-$PARALEAN_INSTANCE-$(date -u +%Y%m%dT%H%M%SZ)}"
mkdir -p "$out"
export AWS_ACCESS_KEY_ID="$PARALEAN_S3_ACCESS_KEY" AWS_SECRET_ACCESS_KEY="$PARALEAN_S3_SECRET_KEY"
export AWS_DEFAULT_REGION="$PARALEAN_S3_REGION" AWS_EC2_METADATA_DISABLED=true AWS_MAX_ATTEMPTS=1
proc() { "$here/proc.sh" "$@"; }
s3() { # node index, s3api arguments
  local node=$1; shift
  timeout 35 aws --no-cli-pager --cli-connect-timeout 2 --cli-read-timeout 15 \
    --endpoint-url "http://127.0.0.1:$((PARALEAN_GARAGE_S3_PORT + node))" s3api "$@"
}
log() { echo "[$(date -u +%FT%TZ)] $*" | tee -a "$out/events.log"; }
split=0
cleanup() {
  if [ "$split" = 1 ]; then
    if proc garage-heal >> "$out/events.log" 2>&1; then
      log 'Garage RPC partition healed on exit'
    else
      log 'ERROR: Garage RPC partition could not be healed'
    fi
  fi
}
trap cleanup EXIT

key_base="faults/garage-partition/$(date +%s%N)"
printf 'acknowledged before Garage RPC partition: %s\n' "$key_base" > "$out/baseline.txt"
printf 'acknowledged by Garage majority while node 2 is isolated: %s\n' "$key_base" > "$out/majority.txt"
printf 'attempted on isolated Garage node 2: %s\n' "$key_base" > "$out/minority.txt"

log 'write and read an acknowledged baseline object through all nodes'
s3 0 put-object --bucket "$PARALEAN_S3_BUCKET" --key "$key_base/baseline" \
  --body "$out/baseline.txt" > "$out/baseline-put.json"
for node in 0 1 2; do
  s3 "$node" get-object --bucket "$PARALEAN_S3_BUCKET" --key "$key_base/baseline" \
    "$out/baseline-node$node.txt" > "$out/baseline-node$node.json"
  cmp "$out/baseline.txt" "$out/baseline-node$node.txt"
done

log 'isolate Garage node 2 from nodes 0 and 1'
proc garage-split 2 >> "$out/events.log" 2>&1
split=1
sleep 5

log 'isolated minority must not acknowledge a new object'
set +e
s3 2 put-object --bucket "$PARALEAN_S3_BUCKET" --key "$key_base/minority" \
  --body "$out/minority.txt" > "$out/minority-put.out" 2> "$out/minority-put.err"
minority_rc=$?
set -e
if [ "$minority_rc" -eq 0 ]; then
  log 'FAIL: isolated minority acknowledged a PUT'
  exit 1
fi
if [ "$minority_rc" -ne 124 ] &&
   ! grep -Eiq '\(InternalError\)|\(ServiceUnavailable\)|\(RequestTimeout\)|quorum|timed? ?out|Internal Server Error' "$out/minority-put.err"; then
  log "FAIL: minority PUT failed unexpectedly (exit $minority_rc): $(tail -1 "$out/minority-put.err")"
  exit 1
fi
log "minority PUT did not acknowledge (exit $minority_rc)"

log 'two-node majority must acknowledge and read a new object during the cut'
majority_ok=0
for attempt in $(seq 1 12); do
  if s3 0 put-object --bucket "$PARALEAN_S3_BUCKET" --key "$key_base/majority" \
    --body "$out/majority.txt" > "$out/majority-put.json" 2> "$out/majority-put.err"; then
    majority_ok=1; break
  fi
  sleep 3
done
[ "$majority_ok" = 1 ] || { log 'FAIL: Garage majority could not acknowledge PUT'; exit 1; }
s3 1 get-object --bucket "$PARALEAN_S3_BUCKET" --key "$key_base/majority" \
  "$out/majority-node1.txt" > "$out/majority-node1.json"
cmp "$out/majority.txt" "$out/majority-node1.txt"

log 'heal RPC partition and verify the majority acknowledgement on every node'
proc garage-heal >> "$out/events.log" 2>&1
split=0
for node in 0 1 2; do
  found=0
  for attempt in $(seq 1 40); do
    if s3 "$node" get-object --bucket "$PARALEAN_S3_BUCKET" --key "$key_base/majority" \
      "$out/majority-node$node.txt" > "$out/majority-node$node.json" 2> "$out/majority-node$node.err" \
      && cmp -s "$out/majority.txt" "$out/majority-node$node.txt"; then
      found=1; break
    fi
    sleep 3
  done
  [ "$found" = 1 ] || { log "FAIL: node $node cannot read acknowledged majority object after healing"; exit 1; }
  found=0
  for attempt in $(seq 1 40); do
    if s3 "$node" get-object --bucket "$PARALEAN_S3_BUCKET" --key "$key_base/baseline" \
      "$out/baseline-healed-node$node.txt" > "$out/baseline-healed-node$node.json" 2> "$out/baseline-healed-node$node.err" \
      && cmp -s "$out/baseline.txt" "$out/baseline-healed-node$node.txt"; then
      found=1; break
    fi
    sleep 3
  done
  [ "$found" = 1 ] || { log "FAIL: node $node cannot read pre-partition acknowledgement after healing"; exit 1; }
done
log 'PASS: minority did not acknowledge; majority remained available; all nodes read both acknowledged objects after healing'
