#!/usr/bin/env bash
# Faults within, and beyond, the redundancy mode of an instance cluster with several
# fdbservers behind netsplit and several Garage nodes (up.sh; e.g. the `ft` instance:
# triple, 6 processes in 6 zones, 5 coordinators, Garage 3 nodes with replication 3).
#
#   PHASE=stress    stress workers (with acknowledgement logs) while single processes are
#                   killed, paused, partitioned and wiped, one and two at a time (FDB triple
#                   tolerates two zones), and Garage nodes are killed, paused and wiped (one
#                   at a time: replication 3, quorum 2); then every acknowledged effect must
#                   be in the store and the audit clean
#   PHASE=fixtures  the regression fixtures, guard and tombstone suites (FIXTURE_ROUNDS times),
#                   then the fault, anti-entropy, property and multi-process tests, while a
#                   chaos loop keeps faulting processes within tolerance
#   PHASE=beyond    three fdbservers (a coordinator majority) down, then two Garage nodes
#                   down: an outage (nothing acknowledged, reads fail rather than lie), then
#                   recovery with nothing lost and a clean audit
#   PHASE=dataloss  (destructive, opt-in) three fdbservers down *and wiped*: data loss beyond
#                   tolerance; the cluster must stay unavailable rather than serve anything
# A probe writes and reads a key once a second (probe.log: time, ok, latency).
# Logs go to $OUT (default results/p2/faults-<instance>).
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
[ -n "$PARALEAN_INSTANCE" ] && [ "$PARALEAN_FDB_PROCS" -ge 5 ] || { echo "needs a multi-process instance (PARALEAN_INSTANCE)" >&2; exit 2; }
H="$PARALEAN_HOME"
phase="${PHASE:-stress}"
out="${OUT:-$here/../../../results/p2/faults-$PARALEAN_INSTANCE}/$phase"
mkdir -p "$out"; rm -f "$out"/*.log "$out/stop"
cd "$here/.."
cargo build -q -p paralean-cli || exit 1
bin="$PWD/target/debug/paralean-p2"
proc() { "$here/proc.sh" "$@" >> "$out/events.log" 2>&1; }
fdbcli() { "$PARALEAN_P2_PREFIX/bin/fdbcli" -C "$PARALEAN_FDB_CLUSTER" "$@"; }
log() { echo "[$(date +%T)] $*" | tee -a "$out/events.log"; }
export PARALEAN_DEPLOYMENT="faults-$phase-$(date +%s)"
export PARALEAN_KEYS="$out/keys.json"
"$bin" keys init "$PARALEAN_KEYS" --demo --workspaces 6 >/dev/null

# Zones the cluster can still lose without losing availability (-1: status unavailable).
tolerance() {
  fdbcli --timeout 10 --exec "status json" 2>/dev/null | python3 -c '
import json, sys
try:
    c = json.load(sys.stdin)["cluster"]
    print(c["fault_tolerance"]["max_zone_failures_without_losing_availability"] if c.get("database_available") else -1)
except Exception:
    print(-1)'
}
writes() { fdbcli --timeout 5 --exec "writemode on; set probe-w $(date +%s%N)" >/dev/null 2>&1; }
# Before the next fault: writes commit again and FDB reports the given fault tolerance.
wait_tolerance() { # min seconds
  local i t0=$(date +%s)
  for i in $(seq 1 "$2"); do
    writes && [ "$(tolerance)" -ge "$1" ] && { log "writes ok and fault tolerance >= $1 after $(( $(date +%s) - t0 )) s"; return 0; }
    sleep 1
  done
  log "WARNING: not recovered (writes and tolerance >= $1) after $2 tries"; return 1
}
probe() {
  while [ ! -f "$out/stop-probe" ]; do
    t0=$(date +%s%N)
    if fdbcli --timeout 5 --exec "writemode on; set probe $(date +%s%N); get probe" >/dev/null 2>&1; then ok=1; else ok=0; fi
    echo "$(date +%s) $ok $((($(date +%s%N) - t0) / 1000000))" >> "$out/probe.log"
    sleep 1
  done
}
workers() { # n ops-per-round fault-p
  local w
  for w in $(seq 0 $(($1 - 1))); do
    ( seed=$((w * 1000 + 1))
      while [ ! -f "$out/stop" ]; do
        "$bin" stress --worker "$w" --ops "$2" --seed "$seed" --fault-p "$3" --ack-log "$out/acks-$w.log" >> "$out/w$w.log" 2>&1
        rc=$?; [ $rc -eq 0 ] || echo "$(date +%T) round seed $seed exit $rc" >> "$out/w$w.err"
        seed=$((seed + 1))
      done ) &
    wpids+=($!)
  done
}
stop_workers() { touch "$out/stop"; for p in "${wpids[@]}"; do wait "$p"; done; wpids=(); rm -f "$out/stop"; }
acks() { cat "$out"/acks-*.log 2>/dev/null | wc -l; }
summary() {
  python3 - "$out/probe.log" <<'PY' | tee -a "$out/events.log"
import sys
rows = [l.split() for l in open(sys.argv[1])]
ok = [int(r[1]) for r in rows]
gap = cur = 0
for x in ok:
    cur = 0 if x else cur + 1
    gap = max(gap, cur)
lat = sorted(int(r[2]) for r in rows if r[1] == "1")
print(f"probe: {len(ok)} probes, {sum(ok)} ok ({100*sum(ok)/max(1,len(ok)):.1f}%), longest failed run {gap} probes; "
      f"latency ok p50 {lat[len(lat)//2] if lat else '-'} ms, max {lat[-1] if lat else '-'} ms")
import time
runs, start = [], None
for r in rows + [["0", "1", "0"]]:
    if r[1] == "0" and start is None:
        start = int(r[0])
    elif r[1] == "1" and start is not None:
        runs.append((start, int(r[0]) - start)); start = None
for s, d in runs:
    print(f"  unavailable from {time.strftime('%H:%M:%S', time.localtime(s))} for about {d} s")
PY
}
finish() { # verify acknowledged effects and audit
  local rc=0
  log "acknowledged effects logged: $(acks)"
  "$bin" verify-acks "$out"/acks-*.log 2>&1 | tee -a "$out/events.log" | tail -3 || rc=1
  "$bin" audit > "$out/audit.log" 2>&1 || rc=1
  tail -15 "$out/audit.log" | tee -a "$out/events.log"
  cat "$out"/w*.err 2>/dev/null | sed 's/^/worker error: /' | tee -a "$out/events.log"
  [ -z "$(cat "$out"/w*.err 2>/dev/null)" ] || rc=1
  return $rc
}

garage_up() { # how many Garage nodes node 0 sees as up
  "$PARALEAN_P2_PREFIX/bin/garage" -c "$H/garage/n0/garage.toml" status 2>/dev/null | awk '/====/{h = /HEALTHY/; next} h && /127\.0\.0\.1:/{n++} END{print n+0}'
}
wpids=()
for j in $(seq 0 $((PARALEAN_GARAGE_NODES - 1))); do proc garage start "$j"; done
probe & probe_pid=$!
wait_tolerance 2 300
sleep 5; log "garage nodes up: $(garage_up) of $PARALEAN_GARAGE_NODES" 
rc=0
case "$phase" in
stress)
  workers 6 25 0.02
  sleep 10
  fault() { log "FAULT $*"; }
  fault "kill fdbserver-1";             proc fdb kill 1; sleep 10; proc fdb start 1; wait_tolerance 2 300
  fault "pause fdbserver-2 (SIGSTOP)";  proc fdb pause 2; sleep 15; proc fdb resume 2; wait_tolerance 2 300
  fault "partition fdbserver-3";        proc split 3; sleep 15; proc heal; wait_tolerance 2 300
  fault "kill fdbserver-0 and fdbserver-4 (two coordinators)"; proc fdb kill 0; proc fdb kill 4; sleep 15
  proc fdb start 0; proc fdb start 4; wait_tolerance 2 300
  fault "pause fdbserver-1 and partition fdbserver-5"; proc fdb pause 1; proc split 5; sleep 15
  proc fdb resume 1; proc heal; wait_tolerance 2 300
  fault "partition fdbservers 2 and 3 together (a minority side)"; proc split 2 3; sleep 15; proc heal; wait_tolerance 2 300
  fault "kill and wipe fdbserver-2 (disk loss)"; proc fdb kill 2; proc fdb wipe 2; sleep 5; proc fdb start 2; wait_tolerance 2 600
  fault "kill and wipe fdbserver-3 and fdbserver-5 (two disk losses)"; proc fdb kill 3; proc fdb kill 5
  proc fdb wipe 3; proc fdb wipe 5; sleep 5; proc fdb start 3; proc fdb start 5; wait_tolerance 2 600
  fault "kill garage-0 (the gateway's first upstream)"; proc garage kill 0; sleep 15; proc garage start 0; sleep 10
  log "garage nodes up: $(garage_up)"
  fault "pause garage-1 (SIGSTOP)"; proc garage pause 1; sleep 15; proc garage resume 1; sleep 10
  log "garage nodes up: $(garage_up)"
  fault "kill and wipe garage-2 (disk loss), resync blocks"; proc garage kill 2; proc garage wipe 2; sleep 10
  proc garage start 2
  for i in $(seq 1 60); do "$PARALEAN_P2_PREFIX/bin/garage" -c "$H/garage/n2/garage.toml" status >/dev/null 2>&1 && break; sleep 1; done
  "$PARALEAN_P2_PREFIX/bin/garage" -c "$H/garage/n2/garage.toml" repair --yes blocks >> "$out/events.log" 2>&1 && log "block resync launched on garage-2"
  sleep 20
  log "garage nodes up: $(garage_up)"
  log "faults done; stopping workers"
  stop_workers
  finish || rc=1
  ;;
fixtures)
  ( i=0
    while [ ! -f "$out/stop" ]; do
      p=$((RANDOM % PARALEAN_FDB_PROCS)); q=$(((p + 1 + RANDOM % (PARALEAN_FDB_PROCS - 1)) % PARALEAN_FDB_PROCS))
      case $((i % 6)) in
        0) log "FAULT kill fdbserver-$p"; proc fdb kill $p; sleep 8; proc fdb start $p ;;
        1) log "FAULT pause fdbserver-$p"; proc fdb pause $p; sleep 8; proc fdb resume $p ;;
        2) log "FAULT partition fdbserver-$p"; proc split $p; sleep 8; proc heal ;;
        3) log "FAULT kill fdbserver-$p, partition fdbserver-$q"; proc fdb kill $p; proc split $q; sleep 8; proc heal; proc fdb start $p ;;
        4) log "FAULT pause fdbserver-$p and fdbserver-$q"; proc fdb pause $p; proc fdb pause $q; sleep 8; proc fdb resume $p; proc fdb resume $q ;;
        5) g=$((RANDOM % PARALEAN_GARAGE_NODES)); log "FAULT kill garage-$g"; proc garage kill $g; sleep 8; proc garage start $g ;;
      esac
      i=$((i + 1)); wait_tolerance 2 300
    done ) & chaos=$!
  log "running the test suite under chaos"
  # The fixture, guard and tombstone suites take seconds; repeat them so faults land inside.
  rounds="${FIXTURE_ROUNDS:-20}"
  for r in $(seq 1 "$rounds"); do
    "$here/test.sh" -p paralean-store --test fixtures --test guards --test tombstones >> "$out/tests.log" 2>&1 \
      || { rc=1; log "fast suites round $r FAILED"; }
  done
  log "fast suites: $rounds rounds done"
  PROPTEST_CASES="${PROPTEST_CASES:-8}" "$here/test.sh" -p paralean-store --test faults --test antientropy --test property \
    >> "$out/tests.log" 2>&1 || rc=1
  "$here/test.sh" -p paralean-cli --test multiprocess >> "$out/tests.log" 2>&1 || rc=1
  touch "$out/stop"; wait $chaos; rm -f "$out/stop"
  grep -E "^test result|FAILED|panicked" "$out/tests.log" | sort | uniq -c | tee -a "$out/events.log"
  log "faults injected during the tests: $(grep -c FAULT "$out/events.log")"
  ;;
beyond)
  workers 3 25 0
  sleep 10
  log "FAULT kill fdbservers 0, 1, 2 (three of five coordinators: beyond tolerance)"
  proc fdb kill 0; proc fdb kill 1; proc fdb kill 2
  sleep 5; a0=$(acks); log "acks 5 s into the outage: $a0; tolerance $(tolerance)"
  timeout 20 "$bin" discover > "$out/outage-read.log" 2>&1; log "a read during the outage: exit $? (124: no answer after 20 s)"
  sleep 25; a1=$(acks); log "acks 30 s into the outage: $a1"
  [ "$a0" = "$a1" ] && log "no effect acknowledged during the outage" || { log "VIOLATION: acks during the outage"; rc=1; }
  proc fdb start 0; proc fdb start 1; proc fdb start 2; wait_tolerance 2 600
  sleep 10
  stop_workers
  finish || rc=1
  log "FAULT kill garage-1 and garage-2 (beyond replication 3 / quorum 2)"
  proc garage kill 1; proc garage kill 2; sleep 3
  before=$("$bin" status 2>/dev/null | awk '$1=="marker"{print $2}')
  timeout 120 "$bin" publish-demo w0 Beyond.g beyond-garage > "$out/garage-publish.log" 2>&1
  log "publish with one Garage node: exit $? ($(tail -1 "$out/garage-publish.log" | cut -c1-160))"
  g="$(grep -h "^group" "$out"/acks-*.log | head -1 | awk '{print $2}')"
  timeout 120 "$bin" get group "$g" > /dev/null 2> "$out/garage-get.log"
  log "verified read of an acknowledged group with one Garage node: exit $? ($(tail -1 "$out/garage-get.log" | cut -c1-160))"
  after=$("$bin" status 2>/dev/null | awk '$1=="marker"{print $2}')
  [ "$before" = "$after" ] && log "no marker written while payloads could not be acknowledged ($after markers)" || { log "VIOLATION: marker written"; rc=1; }
  proc garage start 1; proc garage start 2; sleep 10
  timeout 120 "$bin" publish-demo w0 Beyond.g beyond-garage >> "$out/garage-publish.log" 2>&1 && log "the same publish after recovery: ok"
  finish || rc=1
  ;;
dataloss)
  [ "${I_KNOW_THIS_DESTROYS_THE_INSTANCE:-}" = 1 ] || { echo "set I_KNOW_THIS_DESTROYS_THE_INSTANCE=1" >&2; exit 2; }
  "$bin" publish-demo w0 Loss.g before-loss >> "$out/events.log" 2>&1
  log "FAULT kill and wipe fdbservers 0, 1, 2 (three zones and three coordinators lost)"
  proc fdb kill 0; proc fdb kill 1; proc fdb kill 2; proc fdb wipe 0; proc fdb wipe 1; proc fdb wipe 2
  proc fdb start 0; proc fdb start 1; proc fdb start 2
  sleep 60
  log "tolerance after 60 s: $(tolerance)"
  timeout 30 "$bin" discover > "$out/loss-read.log" 2>&1; log "a read after the loss: exit $? (124: no answer)"
  timeout 30 "$bin" publish-demo w0 Loss.h after-loss >> "$out/events.log" 2>&1; log "a write after the loss: exit $?"
  ;;
esac
touch "$out/stop-probe"; wait $probe_pid; rm -f "$out/stop-probe"
summary
log "phase $phase: $([ $rc -eq 0 ] && echo PASS || echo FAIL)"
exit $rc
