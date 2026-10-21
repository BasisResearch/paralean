#!/usr/bin/env bash
# Many short CLI processes, each opening FDB and exiting, optionally while single FDB
# processes are killed, paused and partitioned (within triple tolerance). Detects processes
# killed by a signal (e.g. SIGSEGV in FDB client teardown at exit) and keeps their cores.
#
#   PARALEAN_INSTANCE=w2-chaos BIN=target/debug/paralean-p2 RUNS=500 LANES=4 CHAOS=1 \
#     OUT=results/p2/exit-race-w2-x scripts/exit-race.sh
#
# Each run is `stress --ops $OPS --fault-p $FAULT_P` with a recorded seed. Core dumps:
# `ulimit -c unlimited`; this host's apport keeps cores of unpackaged binaries in
# $CORE_DIR (default /var/lib/apport/coredump), named with the crashed PID. Up to
# $MAX_CORES are copied to $OUT/cores. PARALEAN_SEGV_REPORT=1 is exported so a fault also
# prints its address, thread and lifecycle stage to the run's stderr (OUT/lane-*.log).
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
[ -n "$PARALEAN_INSTANCE" ] || { echo "requires a private PARALEAN_INSTANCE" >&2; exit 2; }
bin="${BIN:?BIN=<paralean-p2 binary>}"; bin="$(cd "$(dirname "$bin")" && pwd)/$(basename "$bin")"
out="${OUT:?OUT=<result dir>}"
runs="${RUNS:-500}" lanes="${LANES:-4}" chaos="${CHAOS:-0}" ops="${OPS:-3}" fault_p="${FAULT_P:-0.02}"
core_dir="${CORE_DIR:-/var/lib/apport/coredump}" max_cores="${MAX_CORES:-5}"
seed_base="${SEED_BASE:-1}"
[ ! -e "$out/runs.log" ] || { echo "refusing to overwrite $out" >&2; exit 2; }
mkdir -p "$out/cores"
ulimit -c unlimited
export PARALEAN_SEGV_REPORT=1
export PARALEAN_DEPLOYMENT="exit-race-$(date +%s)"
export PARALEAN_KEYS="$out/keys.json"
"$bin" keys init "$PARALEAN_KEYS" --demo --workspaces 6 >/dev/null
log() { echo "[$(date -u +%T)] $*" | tee -a "$out/events.log"; }
log "bin=$bin sha256=$(sha256sum "$bin" | cut -d' ' -f1) runs=$runs lanes=$lanes chaos=$chaos ops=$ops fault_p=$fault_p seed_base=$seed_base deployment=$PARALEAN_DEPLOYMENT"
fdbcli() { "$PARALEAN_P2_PREFIX/bin/fdbcli" -C "$PARALEAN_FDB_CLUSTER" "$@"; }
healthy() { # writes commit and FDB tolerates two zone failures
  fdbcli --timeout 5 --exec "writemode on; set exit-race-probe $(date +%s%N)" >/dev/null 2>&1 || return 1
  fdbcli --timeout 10 --exec "status json" 2>/dev/null | python3 -c '
import json, sys
c = json.load(sys.stdin)["cluster"]
sys.exit(0 if c.get("database_available") and c["fault_tolerance"]["max_zone_failures_without_losing_availability"] >= 2 else 1)'
}
wait_healthy() { local i; for i in $(seq 1 300); do healthy && return 0; sleep 1; done; log "WARNING: not healthy after 300 s"; return 1; }
proc() { "$here/proc.sh" "$@" >> "$out/events.log" 2>&1; }
chaos_loop() {
  local i=0 p
  RANDOM="$seed_base"
  while [ ! -f "$out/stop" ]; do
    p=$((RANDOM % PARALEAN_FDB_PROCS))
    case $((i % 3)) in
      0) log "FAULT kill fdbserver-$p"; proc fdb kill "$p"; sleep 8; proc fdb start "$p" ;;
      1) log "FAULT pause fdbserver-$p"; proc fdb pause "$p"; sleep 8; proc fdb resume "$p" ;;
      2) log "FAULT partition fdbserver-$p"; proc split "$p"; sleep 8; proc heal ;;
    esac
    i=$((i + 1)); wait_healthy || break
  done
}
lane() { # lane index
  local l=$1 i seed pid rc core
  for i in $(seq 0 $((runs - 1))); do
    [ ! -f "$out/stop-lanes" ] || break
    seed=$((seed_base + l * 1000000 + i))
    "$bin" stress --worker $((l % 6)) --ops "$ops" --seed "$seed" --fault-p "$fault_p" >> "$out/lane-$l.log" 2>&1 &
    pid=$!; wait "$pid"; rc=$?
    echo "$(date -u +%T.%N) lane $l run $i seed $seed pid $pid rc $rc" >> "$out/runs.log"
    if [ "$rc" -ge 128 ]; then
      log "SIGNAL lane $l run $i seed $seed pid $pid rc $rc (signal $((rc - 128)))"
      if [ "$(ls "$out/cores" | wc -l)" -lt "$max_cores" ]; then
        for _ in $(seq 1 30); do
          core="$(ls "$core_dir"/core.*."$pid".* 2>/dev/null | head -1)"
          [ -n "$core" ] && break; sleep 1
        done
        if [ -n "$core" ]; then cp "$core" "$out/cores/core.$pid" && log "core saved: cores/core.$pid (from $core)"
        else log "no core found for pid $pid in $core_dir"; fi
      fi
    fi
  done
}
rm -f "$out/stop" "$out/stop-lanes"
wait_healthy || exit 1
if [ "$chaos" = 1 ]; then chaos_loop & chaos_pid=$!; fi
lpids=()
for l in $(seq 0 $((lanes - 1))); do lane "$l" & lpids+=($!); done
for p in "${lpids[@]}"; do wait "$p"; done
touch "$out/stop"
[ -z "${chaos_pid:-}" ] || wait "$chaos_pid"
proc heal
total=$(wc -l < "$out/runs.log")
signalled=$(awk '$NF >= 128' "$out/runs.log" | wc -l)
other=$(awk '$NF != 0 && $NF < 128' "$out/runs.log" | wc -l)
log "runs $total; killed by a signal $signalled; other nonzero exits $other; FDB faults $(grep -c 'FAULT' "$out/events.log")"
awk '$NF != 0 {print $NF}' "$out/runs.log" | sort | uniq -c | sed 's/^/  exit status counts: /' | tee -a "$out/events.log"
[ "$signalled" -eq 0 ]
