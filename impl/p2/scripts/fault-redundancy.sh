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
# FAULT_SCOPE=combined (default), fdb, or garage runs the corresponding fault
# family on a private instance. Split scopes allow bounded process budgets:
# six FDB + one Garage for fdb; one FDB + three Garage for garage. Set
# STRESS_WORKERS=1 there to keep at most eight active data/workload processes.
# SKIP_BUILD=1 uses an existing debug CLI. Scoped fixtures log explicit skips
# for anti-entropy peers and multiprocess tests when they need a separate wave.
# CORE_DUMPS=1 (stress and beyond phases): unlimited core size, the CLI's opt-in fault
# reporter (PARALEAN_SEGV_REPORT=1, written to w<i>.log), and a copy of each signalled
# worker's core from $CORE_DIR (default /var/lib/apport/coredump, where this host's apport
# keeps cores of unpackaged binaries) into $out/cores, at most $MAX_CORES.
# PHASE=fixtures: FAST_SUITE_ARGS replaces the repeated suites' test.sh arguments (default
# `-p paralean-store --test fixtures --test guards --test tombstones`); SLOW_SUITES lists
# the once-run store suites (default `faults property`; empty skips them).
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
[ -n "$PARALEAN_INSTANCE" ] || { echo "requires a private PARALEAN_INSTANCE" >&2; exit 2; }
scope="${FAULT_SCOPE:-combined}"
case "$scope" in
  combined|fdb)
    [ "$PARALEAN_FDB_PROCS" -ge 6 ] && [ "$PARALEAN_FDB_REDUNDANCY" = triple ] && [ "$PARALEAN_NETSPLIT" = 1 ] || {
      echo "$scope scope needs six FDB processes, triple redundancy and netsplit" >&2; exit 2;
    }
    min_tolerance=2 ;;
  garage) min_tolerance=0 ;;
  *) echo "FAULT_SCOPE must be combined, fdb or garage" >&2; exit 2 ;;
esac
if [ "$scope" != fdb ]; then
  [ "$PARALEAN_GARAGE_NODES" -ge 3 ] && [ "$PARALEAN_GARAGE_REPLICATION" -eq 3 ] || {
    echo "$scope scope needs three Garage nodes with replication 3" >&2; exit 2;
  }
fi
[[ "${STRESS_WORKERS:-6}" =~ ^[1-9][0-9]*$ ]] || { echo "STRESS_WORKERS must be positive" >&2; exit 2; }
H="$PARALEAN_HOME"
phase="${PHASE:-stress}"
case "$phase" in stress|fixtures|beyond|dataloss) ;; *) echo "unknown PHASE=$phase" >&2; exit 2 ;; esac
[ "$phase" != dataloss ] || [ "$scope" != garage ] || { echo 'dataloss requires FDB scope' >&2; exit 2; }
default_out="$here/../../../results/p2/faults-$PARALEAN_INSTANCE"
[ "$scope" = combined ] || default_out="$default_out/$scope"
if [ -n "${OUT:-}" ]; then
  out="$OUT/$phase"
else
  out="$default_out/$phase/$(date -u +%Y%m%dT%H%M%SZ)-$$"
fi
if [ -e "$out/events.log" ]; then echo "refusing to overwrite previous run at $out" >&2; exit 2; fi
mkdir -p "$out"; rm -f "$out/stop" "$out/stop-probe" "$out/fault-command-failed"
cd "$here/.."
if [ "${SKIP_BUILD:-0}" != 1 ]; then cargo build -q -j 1 -p paralean-cli || exit 1; fi
bin="${CLI_BIN:-$PWD/target/debug/paralean-p2}" # CLI_BIN pins a prebuilt binary (with SKIP_BUILD=1)
[ -x "$bin" ] || { echo "missing $bin; build CLI first" >&2; exit 2; }
proc() {
  "$here/proc.sh" "$@" >> "$out/events.log" 2>&1 && return 0
  echo "fault command failed: proc.sh $*" | tee -a "$out/events.log"
  touch "$out/fault-command-failed"
  return 1
}
fdbcli() { "$PARALEAN_P2_PREFIX/bin/fdbcli" -C "$PARALEAN_FDB_CLUSTER" "$@"; }
log() { echo "[$(date +%T)] $*" | tee -a "$out/events.log"; }
log "phase=$phase scope=$scope fdb=$PARALEAN_FDB_PROCS garage=$PARALEAN_GARAGE_NODES workers=${STRESS_WORKERS:-6} skip_build=${SKIP_BUILD:-0} result_dir=$out"
log "cli sha256 $(sha256sum "$bin" | cut -d' ' -f1)"
if [ "${CORE_DUMPS:-0}" = 1 ]; then
  ulimit -c unlimited
  export PARALEAN_SEGV_REPORT=1
  log "core dumps: ulimit -c $(ulimit -c), cores from ${CORE_DIR:-/var/lib/apport/coredump}"
fi
save_core() { # pid of a worker killed by a signal
  [ "${CORE_DUMPS:-0}" = 1 ] || return 0
  local core dir="${CORE_DIR:-/var/lib/apport/coredump}"
  mkdir -p "$out/cores"
  [ "$(ls "$out/cores" | wc -l)" -lt "${MAX_CORES:-5}" ] || return 0
  for _ in $(seq 1 30); do core="$(ls "$dir"/core.*."$1".* 2>/dev/null | head -1)"; [ -n "$core" ] && break; sleep 1; done
  if [ -n "$core" ]; then cp "$core" "$out/cores/core.$1" && echo "$(date +%T) core of pid $1 saved as cores/core.$1 ($core)" >> "$out/cores.log"
  else echo "$(date +%T) no core for pid $1 in $dir" >> "$out/cores.log"; fi
}
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
        "$bin" stress --worker "$w" --ops "$2" --seed "$seed" --fault-p "$3" --ack-log "$out/acks-$w.log" >> "$out/w$w.log" 2>&1 &
        cpid=$!; wait "$cpid"; rc=$?
        echo "$(date +%T) seed $seed pid $cpid exit $rc" >> "$out/w$w.rounds"
        if [ $rc -ne 0 ]; then
          echo "$(date +%T) round seed $seed exit $rc (pid $cpid)" >> "$out/w$w.err"
          [ $rc -lt 128 ] || save_core "$cpid"
        fi
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
for r in rows:
    if r[1] == "0" and start is None:
        start = int(r[0])
    elif r[1] == "1" and start is not None:
        runs.append((start, int(r[0]) - start)); start = None
for s, d in runs:
    print(f"  unavailable from {time.strftime('%H:%M:%S', time.localtime(s))} for about {d} s (sampled until next success)")
if start is not None:
    last = int(rows[-1][0])
    print(f"  unavailable from {time.strftime('%H:%M:%S', time.localtime(start))} through last failed sample "
          f"{time.strftime('%H:%M:%S', time.localtime(last))} (sampled span {max(0, last-start)} s; right-censored)")
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
garage_split_marker="$out/garage-rpc-split-issued"
cleanup_garage_split() {
  if [ -f "$garage_split_marker" ]; then
    if proc garage-heal; then
      rm -f "$garage_split_marker"
      log 'Garage RPC partition healed by EXIT cleanup'
    else
      log 'ERROR: Garage RPC partition could not be healed by EXIT cleanup'
    fi
  fi
}
cleanup_probe() {
  if [ -n "${probe_pid:-}" ]; then
    touch "$out/stop-probe"
    wait "$probe_pid" || true
    probe_pid=''
    rm -f "$out/stop-probe"
  fi
}
cleanup() {
  cleanup_garage_split
  cleanup_probe
}
trap cleanup EXIT
for j in $(seq 0 $((PARALEAN_GARAGE_NODES - 1))); do proc garage start "$j"; done
probe & probe_pid=$!
wait_tolerance "$min_tolerance" 300 || exit 1
sleep 5; log "garage nodes up: $(garage_up) of $PARALEAN_GARAGE_NODES" 
rc=0
case "$phase" in
stress)
  workers "${STRESS_WORKERS:-6}" 25 0.02
  sleep 10
  fault() { log "FAULT $*"; }
  fdb_stress() {
    fault "kill fdbserver-1"; proc fdb kill 1; sleep 10; proc fdb start 1; wait_tolerance 2 300 || return 1
    fault "pause fdbserver-2 (SIGSTOP)"; proc fdb pause 2; sleep 15; proc fdb resume 2; wait_tolerance 2 300 || return 1
    fault "partition fdbserver-3"; proc split 3; sleep 15; proc heal; wait_tolerance 2 300 || return 1
    fault "kill fdbserver-0 and fdbserver-4 (two coordinators)"; proc fdb kill 0; proc fdb kill 4; sleep 15
    proc fdb start 0; proc fdb start 4; wait_tolerance 2 300 || return 1
    fault "pause fdbserver-1 and partition fdbserver-5"; proc fdb pause 1; proc split 5; sleep 15
    proc fdb resume 1; proc heal; wait_tolerance 2 300 || return 1
    fault "partition fdbservers 2 and 3 together (a minority side)"; proc split 2 3; sleep 15; proc heal; wait_tolerance 2 300 || return 1
    fault "kill and wipe fdbserver-2 (disk loss)"; proc fdb kill 2; proc fdb wipe 2; sleep 5; proc fdb start 2; wait_tolerance 2 600 || return 1
    fault "kill and wipe fdbserver-3 and fdbserver-5 (two disk losses)"; proc fdb kill 3; proc fdb kill 5
    proc fdb wipe 3; proc fdb wipe 5; sleep 5; proc fdb start 3; proc fdb start 5; wait_tolerance 2 600
  }
  garage_stress() {
    fault "kill garage-0 (the gateway's first upstream)"; proc garage kill 0; sleep 15; proc garage start 0; sleep 10
    log "garage nodes up: $(garage_up)"
    fault "pause garage-1 (SIGSTOP)"; proc garage pause 1; sleep 15; proc garage resume 1; sleep 10
    log "garage nodes up: $(garage_up)"
    if [ "${PARALEAN_GARAGE_NETSPLIT:-0}" = 1 ]; then
      fault "partition Garage RPC node 2"; touch "$garage_split_marker" || return 1
      proc garage-split 2 || return 1
      sleep 15; proc garage-heal || return 1; rm -f "$garage_split_marker"; sleep 10
      log "garage nodes up: $(garage_up)"
    fi
    fault "kill and wipe garage-2 (disk loss), resync blocks"; proc garage kill 2; proc garage wipe 2; sleep 10
    proc garage start 2
    local i
    for i in $(seq 1 60); do "$PARALEAN_P2_PREFIX/bin/garage" -c "$H/garage/n2/garage.toml" status >/dev/null 2>&1 && break; sleep 1; done
    "$PARALEAN_P2_PREFIX/bin/garage" -c "$H/garage/n2/garage.toml" repair --yes blocks >> "$out/events.log" 2>&1 || return 1
    log "block resync launched on garage-2"
    sleep 20
    log "garage nodes up: $(garage_up)"
  }
  if [ "$scope" != garage ]; then fdb_stress || rc=1; fi
  if [ "$scope" != fdb ] && [ "$rc" -eq 0 ]; then garage_stress || rc=1; fi
  log "faults done; stopping workers"
  stop_workers
  finish || rc=1
  ;;
fixtures)
  chaos_seed="${CHAOS_SEED:-$(od -An -N2 -tu2 /dev/urandom | tr -d ' ')}"
  [[ "$chaos_seed" =~ ^[0-9]+$ ]] || { echo 'CHAOS_SEED must be a decimal integer' >&2; exit 2; }
  log "fixture chaos seed=$chaos_seed"
  ( RANDOM="$chaos_seed"; i=0
    while [ ! -f "$out/stop" ]; do
      if [ "$scope" = garage ]; then
        mode=5
      elif [ "$scope" = fdb ]; then
        mode=$((i % 5))
      else
        mode=$((i % 6))
      fi
      p=$((RANDOM % PARALEAN_FDB_PROCS))
      q=$(((p + 1 + RANDOM % (PARALEAN_FDB_PROCS > 1 ? PARALEAN_FDB_PROCS - 1 : 1)) % PARALEAN_FDB_PROCS))
      case "$mode" in
        0) log "FAULT kill fdbserver-$p"; proc fdb kill $p; sleep 8; proc fdb start $p ;;
        1) log "FAULT pause fdbserver-$p"; proc fdb pause $p; sleep 8; proc fdb resume $p ;;
        2) log "FAULT partition fdbserver-$p"; proc split $p; sleep 8; proc heal ;;
        3) log "FAULT kill fdbserver-$p, partition fdbserver-$q"; proc fdb kill $p; proc split $q; sleep 8; proc heal; proc fdb start $p ;;
        4) log "FAULT pause fdbserver-$p and fdbserver-$q"; proc fdb pause $p; proc fdb pause $q; sleep 8; proc fdb resume $p; proc fdb resume $q ;;
        5) g=$((RANDOM % PARALEAN_GARAGE_NODES)); log "FAULT kill garage-$g"; proc garage kill $g; sleep 8; proc garage start $g ;;
      esac
      i=$((i + 1)); wait_tolerance "$min_tolerance" 300 || exit 1
    done ) & chaos=$!
  log "running the test suite under chaos"
  # The fixture, guard and tombstone suites take seconds; repeat them so faults land inside.
  rounds="${FIXTURE_ROUNDS:-20}"
  for r in $(seq 1 "$rounds"); do
    # shellcheck disable=SC2086
    "$here/test.sh" ${FAST_SUITE_ARGS:--p paralean-store --test fixtures --test guards --test tombstones} >> "$out/tests.log" 2>&1 \
      || { rc=1; log "fast suites round $r FAILED"; }
  done
  log "fast suites: $rounds rounds done"
  read -r -a store_tests <<< "${SLOW_SUITES-faults property}"
  if [ "${SKIP_AE:-0}" = 1 ] || [ "$scope" = fdb ]; then
    log 'SKIP antientropy test during this fault scope; run separately with a bounded peer'
  else
    store_tests+=(antientropy)
  fi
  test_args=()
  for t in "${store_tests[@]}"; do test_args+=(--test "$t"); done
  if [ "${#test_args[@]}" -gt 0 ]; then
    PROPTEST_CASES="${PROPTEST_CASES:-8}" "$here/test.sh" -p paralean-store "${test_args[@]}" \
      >> "$out/tests.log" 2>&1 || rc=1
  else
    log 'SKIP once-run store suites (SLOW_SUITES empty)'
  fi
  if [ "${SKIP_MULTIPROCESS:-0}" = 1 ] || [ "$scope" != combined ]; then
    log 'SKIP multiprocess test during this fault scope; run separately with a bounded wave'
  else
    "$here/test.sh" -p paralean-cli --test multiprocess >> "$out/tests.log" 2>&1 || rc=1
  fi
  touch "$out/stop"; wait "$chaos" || rc=1; rm -f "$out/stop"
  grep -E "^test result|FAILED|panicked" "$out/tests.log" | sort | uniq -c | tee -a "$out/events.log"
  log "faults injected during the tests: $(grep -c FAULT "$out/events.log")"
  ;;
beyond)
  if [ "$scope" != garage ]; then
    if [ "$scope" = combined ]; then beyond_workers="${BEYOND_WORKERS:-3}"; else beyond_workers="${BEYOND_WORKERS:-${STRESS_WORKERS:-1}}"; fi
    workers "$beyond_workers" 25 0
    sleep 10
    log "FAULT kill fdbservers 0, 1, 2 (three of five coordinators: beyond tolerance)"
    proc fdb kill 0; proc fdb kill 1; proc fdb kill 2
    sleep 5; a0=$(acks); log "acks 5 s into the outage: $a0; tolerance $(tolerance)"
    timeout 20 "$bin" discover > "$out/outage-read.log" 2>&1; read_rc=$?
    log "a read during the outage: exit $read_rc (124: no answer after 20 s)"
    [ "$read_rc" -ne 0 ] || { log 'VIOLATION: read succeeded beyond FDB tolerance'; rc=1; }
    sleep 25; a1=$(acks); log "acks 30 s into the outage: $a1"
    [ "$a0" = "$a1" ] && log "no effect acknowledged during the outage" || { log "VIOLATION: acks during the outage"; rc=1; }
    proc fdb start 0; proc fdb start 1; proc fdb start 2; wait_tolerance 2 600 || rc=1
    sleep 10
    stop_workers
    finish || rc=1
  fi
  if [ "$scope" != fdb ]; then
    if [ "$scope" = garage ]; then
      "$bin" publish-demo w0 Beyond.baseline before-garage-loss > "$out/garage-baseline.log" 2>&1 || {
        log 'FAILED: baseline publish before Garage outage'; exit 1;
      }
      g="$(awk '$1=="published" && $2=="group" {print $3; exit}' "$out/garage-baseline.log")"
    else
      g="$(grep -h '^group' "$out"/acks-*.log | head -1 | awk '{print $2}')"
    fi
    [ -n "$g" ] || { log 'FAILED: no acknowledged baseline group for Garage outage'; exit 1; }
    "$bin" get group "$g" > "$out/garage-baseline-bytes.bin" 2> "$out/garage-baseline-get.log" || {
      log 'FAILED: acknowledged group not readable before Garage outage'; exit 1;
    }
    log "FAULT kill garage-1 and garage-2 (beyond replication 3 / quorum 2)"
    proc garage kill 1; proc garage kill 2; sleep 3
    before=$("$bin" status 2>/dev/null | awk '$1=="marker"{print $2}')
    [ -n "$before" ] || { log 'FAILED: cannot read marker count before Garage outage'; rc=1; }
    timeout 120 "$bin" publish-demo w0 Beyond.g beyond-garage > "$out/garage-publish.log" 2>&1; publish_rc=$?
    log "publish with one Garage node: exit $publish_rc ($(tail -1 "$out/garage-publish.log" | cut -c1-160))"
    [ "$publish_rc" -ne 0 ] || { log 'VIOLATION: publish acknowledged without Garage quorum'; rc=1; }
    timeout 120 "$bin" get group "$g" > "$out/garage-outage-bytes.bin" 2> "$out/garage-get.log"; get_rc=$?
    log "read of acknowledged group with one Garage node: exit $get_rc ($(tail -1 "$out/garage-get.log" | cut -c1-160))"
    if [ "$get_rc" -eq 0 ]; then
      cmp "$out/garage-baseline-bytes.bin" "$out/garage-outage-bytes.bin" || {
        log 'VIOLATION: verified read returned different bytes during Garage quorum loss'; rc=1;
      }
    else
      log 'acknowledged object read unavailable without Garage quorum'
    fi
    after=$("$bin" status 2>/dev/null | awk '$1=="marker"{print $2}')
    [ -n "$after" ] && [ "$before" = "$after" ] && log "no marker written while payloads could not be acknowledged ($after markers)" || { log 'VIOLATION: marker count changed or unavailable'; rc=1; }
    proc garage start 1; proc garage start 2; sleep 10
    timeout 120 "$bin" publish-demo w0 Beyond.g beyond-garage >> "$out/garage-publish.log" 2>&1 && log 'same publish after recovery acknowledged' || { log 'FAILED: publish after recovery'; rc=1; }
    timeout 120 "$bin" get group "$g" > "$out/garage-recovered-bytes.bin" 2> "$out/garage-recovered-get.log" || {
      log 'FAILED: pre-loss acknowledged group unreadable after recovery'; rc=1;
    }
    cmp "$out/garage-baseline-bytes.bin" "$out/garage-recovered-bytes.bin" || {
      log 'VIOLATION: acknowledged group bytes changed after Garage recovery'; rc=1;
    }
    if [ "$scope" = combined ]; then
      finish || rc=1
    else
      "$bin" audit > "$out/audit.log" 2>&1 || { log 'FAILED: audit after Garage recovery'; rc=1; }
    fi
  fi
  ;;
dataloss)
  [ "${I_KNOW_THIS_DESTROYS_THE_INSTANCE:-}" = 1 ] || { echo "set I_KNOW_THIS_DESTROYS_THE_INSTANCE=1" >&2; exit 2; }
  "$bin" publish-demo w0 Loss.g before-loss >> "$out/events.log" 2>&1 || {
    log 'FAILED: baseline publish before destructive data-loss test'; exit 1;
  }
  log "FAULT kill and wipe fdbservers 0, 1, 2 (three zones and three coordinators lost)"
  proc fdb kill 0; proc fdb kill 1; proc fdb kill 2; proc fdb wipe 0; proc fdb wipe 1; proc fdb wipe 2
  proc fdb start 0; proc fdb start 1; proc fdb start 2
  sleep 60
  log "tolerance after 60 s: $(tolerance)"
  timeout 30 "$bin" discover > "$out/loss-read.log" 2>&1; read_rc=$?
  log "a read after the loss: exit $read_rc (124: no answer)"
  [ "$read_rc" -ne 0 ] || { log 'VIOLATION: read succeeded after loss beyond FDB tolerance'; rc=1; }
  timeout 30 "$bin" publish-demo w0 Loss.h after-loss >> "$out/events.log" 2>&1; write_rc=$?
  log "a write after the loss: exit $write_rc"
  [ "$write_rc" -ne 0 ] || { log 'VIOLATION: write acknowledged after loss beyond FDB tolerance'; rc=1; }
  ;;
esac
cleanup_probe
summary
[ ! -e "$out/fault-command-failed" ] || rc=1
log "phase $phase: $([ $rc -eq 0 ] && echo PASS || echo FAIL)"
exit $rc
