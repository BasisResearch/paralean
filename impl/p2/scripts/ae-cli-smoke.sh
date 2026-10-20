#!/usr/bin/env bash
# Two real P2 instances, two ae-service OS processes, and only public peer config.
# Example: PARALEAN_A_INSTANCE=mp2-net PARALEAN_B_INSTANCE=mp2-peer ./scripts/ae-cli-smoke.sh
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../../.." && pwd)"
bin="${PARALEAN_P2_BIN:-$here/../target/debug/paralean-p2}"
a_instance="${PARALEAN_A_INSTANCE:-}"
b_instance="${PARALEAN_B_INSTANCE:-}"
prefix="${PARALEAN_P2_PREFIX:-/data/home/kirancodes/paralean-p2}"
[ -n "$a_instance" ] && [ -n "$b_instance" ] && [ "$a_instance" != "$b_instance" ] || {
  echo 'set distinct PARALEAN_A_INSTANCE and PARALEAN_B_INSTANCE; refusing default instances' >&2
  exit 2
}
[ -x "$bin" ] || { echo "build the production paralean-p2 binary first: $bin" >&2; exit 2; }
for instance in "$a_instance" "$b_instance"; do
  [ -f "$prefix/inst/$instance/instance.sh" ] || {
    echo "instance $instance is not initialized" >&2; exit 2;
  }
done
umask 077
stamp="$(date -u +%Y%m%dT%H%M%SZ)-$$"
private="$repo/.runs/ae-cli-smoke-$stamp"
out="${OUT:-$repo/results/p2/ae-cli-smoke-$stamp}"
mkdir -p "$private" "$out"
chmod 700 "$private"
a_deployment="ae-cli-$stamp-a"
b_deployment="ae-cli-$stamp-b"
a_port="${PARALEAN_AE_PORT_A:-24720}"
b_port="${PARALEAN_AE_PORT_B:-24721}"
target='Target.cliSmoke'
a_pid=''
b_pid=''
cleanup() {
  for pid in "$a_pid" "$b_pid"; do
    if [ -n "$pid" ] && kill -0 "$pid" 2>/dev/null; then
      kill -TERM "$pid" 2>/dev/null || true
      wait "$pid" 2>/dev/null || true
    fi
  done
}
trap cleanup EXIT
run_a() (
  export PARALEAN_INSTANCE="$a_instance" PARALEAN_DEPLOYMENT="$a_deployment"
  export PARALEAN_KEYS="$private/a-keys.json"
  unset PARALEAN_S3_PREFIX
  . "$here/env.sh"
  if [ -f "$private/a-config.json" ]; then export PARALEAN_FEDERATION_CONFIG="$private/a-config.json"; fi
  exec "$bin" "$@"
)
run_b() (
  export PARALEAN_INSTANCE="$b_instance" PARALEAN_DEPLOYMENT="$b_deployment"
  export PARALEAN_KEYS="$private/b-keys.json"
  unset PARALEAN_S3_PREFIX
  . "$here/env.sh"
  if [ -f "$private/b-config.json" ]; then export PARALEAN_FEDERATION_CONFIG="$private/b-config.json"; fi
  exec "$bin" "$@"
)
start_a() {
  export PARALEAN_INSTANCE="$a_instance" PARALEAN_DEPLOYMENT="$a_deployment"
  export PARALEAN_KEYS="$private/a-keys.json" PARALEAN_FEDERATION_CONFIG="$private/a-config.json"
  unset PARALEAN_S3_PREFIX
  . "$here/env.sh"
  exec "$bin" ae-service "$private/a-config.json"
}
start_b() {
  export PARALEAN_INSTANCE="$b_instance" PARALEAN_DEPLOYMENT="$b_deployment"
  export PARALEAN_KEYS="$private/b-keys.json" PARALEAN_FEDERATION_CONFIG="$private/b-config.json"
  unset PARALEAN_S3_PREFIX
  . "$here/env.sh"
  exec "$bin" ae-service "$private/b-config.json"
}
log() { printf '[%s] %s\n' "$(date -u +%FT%TZ)" "$*" | tee -a "$out/events.log"; }
await_group() {
  local id="$1" label="$2" short="${1:0:12}" i
  for i in $(seq 1 60); do
    run_b discover > "$out/$label-discover.txt"
    if grep -Fq "$short" "$out/$label-discover.txt"; then
      # `discover` renders abbreviated debug IDs; the exact-ID GET closes a
      # possible prefix collision and checks the received S3 object too.
      run_b get group "$id" > "$out/$label-group.pce"
      return
    fi
    sleep 1
  done
  log "FAIL: B did not discover group $id ($label)"
  exit 1
}
await_drained() {
  local label="$1" i
  for i in $(seq 1 60); do
    run_b ae-status "$private/b-config.json" > "$out/$label-ae-status.txt"
    if grep -q 'cursor: Some' "$out/$label-ae-status.txt" &&
       ! grep -q '^  event ' "$out/$label-ae-status.txt"; then return; fi
    sleep 1
  done
  log "FAIL: B's anti-entropy cursor/pending queue did not drain ($label)"
  exit 1
}

log 'generate distinct random local authority, validator, writer and transport keys'
run_a keys init "$private/a-keys.json" --workspaces 2 > "$out/a-keys-init.txt"
run_b keys init "$private/b-keys.json" --workspaces 2 > "$out/b-keys-init.txt"
run_a ae-keygen "$private/a-transport.seed" > "$private/a-transport.pub"
run_b ae-keygen "$private/b-transport.seed" > "$private/b-transport.pub"
run_a federation-member "$a_deployment" "$(cat "$private/a-transport.pub")" > "$private/a-member.json"
run_b federation-member "$b_deployment" "$(cat "$private/b-transport.pub")" > "$private/b-member.json"
python3 - "$private" "$a_deployment" "$b_deployment" "$a_port" "$b_port" "$target" <<'PY'
import json, pathlib, sys
p = pathlib.Path(sys.argv[1])
a, b, ap, bp, target = sys.argv[2:]
members = {a: json.loads((p / 'a-member.json').read_text()), b: json.loads((p / 'b-member.json').read_text())}
validators = [json.loads((p / f'{side}-keys.json').read_text())['validators']['v0']['public'] for side in ('a', 'b')]
for side, local, remote, listen, peer in [('a', a, b, ap, bp), ('b', b, a, bp, ap)]:
    config = {
        'deployment': local, 'members': members, 'target_homes': {target: a},
        'trusted_validators': validators, 'signing_seed_file': str(p / f'{side}-transport.seed'),
        'listen': f'127.0.0.1:{listen}', 'peers': {remote: f'127.0.0.1:{peer}'},
        'sync_writer': 'w1', 'interval_ms': 200,
    }
    (p / f'{side}-config.json').write_text(json.dumps(config, indent=2) + '\n')
PY

log 'pin identical public federation roster before publication'
run_a federation-init "$private/a-config.json" > "$out/a-init.txt"
run_b federation-init "$private/b-config.json" > "$out/b-init.txt"
start_a > "$out/a-daemon.log" 2>&1 & a_pid=$!
start_b > "$out/b-daemon-1.log" 2>&1 & b_pid=$!
sleep 2
kill -0 "$a_pid" && kill -0 "$b_pid" || { log 'FAIL: daemon exited at startup'; exit 1; }

log 'publish a free group, checkpoint, and home-target group at A'
run_a publish-demo w0 Demo.cliSmoke first > "$out/a-publish-1.txt"
first_id="$(awk '$1=="published" && $2=="group" {print $3}' "$out/a-publish-1.txt")"
[ -n "$first_id" ] || { log 'FAIL: no first group ID'; exit 1; }
run_a checkpoint-demo w0 cliCheckpoint > "$out/a-checkpoint.txt"
run_a assign "$target" w0 > "$out/a-target-assign.txt"
run_a publish-demo w0 "$target" target > "$out/a-target-publish.txt"
target_id="$(awk '$1=="published" && $2=="group" {print $3}' "$out/a-target-publish.txt")"
await_group "$first_id" first
await_group "$target_id" target
await_drained first
run_b audit > "$out/b-audit-1.txt"
log 'B discovered free and home-target groups; cursor drained and audit passed'

log 'SIGTERM B service, await clean exit, and restart with the same durable cursor'
kill -TERM "$b_pid"
wait "$b_pid"
b_pid=''
cp "$out/first-ae-status.txt" "$out/b-status-before-restart.txt"
start_b > "$out/b-daemon-2.log" 2>&1 & b_pid=$!
sleep 2
kill -0 "$b_pid" || { log 'FAIL: B daemon did not restart'; exit 1; }
run_b ae-status "$private/b-config.json" > "$out/b-status-after-restart.txt"
grep -q 'cursor: Some' "$out/b-status-after-restart.txt" || { log 'FAIL: B cursor lost at restart'; exit 1; }

log 'publish a second group after B restart and verify incremental arrival'
run_a publish-demo w0 Demo.cliSmokeAfterRestart second > "$out/a-publish-2.txt"
second_id="$(awk '$1=="published" && $2=="group" {print $3}' "$out/a-publish-2.txt")"
[ -n "$second_id" ] || { log 'FAIL: no second group ID'; exit 1; }
await_group "$second_id" second
await_drained second
run_b audit > "$out/b-audit-2.txt"
kill -TERM "$b_pid" "$a_pid"
wait "$b_pid"
wait "$a_pid"
b_pid='' a_pid=''
log 'PASS: two-process authenticated CLI anti-entropy, restart cursor, graceful SIGTERM'
log "public evidence: $out (private local files: $private)"
