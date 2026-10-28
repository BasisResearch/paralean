#!/usr/bin/env bash
# Loop the exit-race reproducer (crates/store/examples/exit_race.rs) and keep backtraces of
# the first crashed runs. No FDB faults: the race is between the FDB network thread and
# libfdb_c's own exit-time destructors.
#
#   PARALEAN_INSTANCE=w2c-chaos MODES="idle keep busy stop" RUNS=1000 \
#     OUT=results/w2/finish/chaos/exit-race-repro scripts/exit-race-repro.sh
#
# Writes $OUT/<mode>.runs (one exit status per line), $OUT/summary.txt and, for the first
# $MAX_BT crashes of each mode, $OUT/<mode>-bt-<pid>.txt from apport's core in $CORE_DIR.
# A mode `idle+gap` runs `idle` with EXIT_RACE_GAP_MS (exported by the caller).
# The cores themselves are not kept. Runs are sequential by default: four parallel lanes
# (LANES=4) did not crash in 400 idle runs on this host, one lane crashed in about 1%.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
[ -n "$PARALEAN_INSTANCE" ] || { echo "requires a private PARALEAN_INSTANCE" >&2; exit 2; }
cd "$here/.."
cargo build -q -j 1 -p paralean-store --example exit_race || exit 1
bin="$PWD/target/debug/examples/exit_race"
out="${OUT:?OUT=<result dir>}"; mkdir -p "$out"; out="$(cd "$out" && pwd)"
modes="${MODES:-idle keep busy stop}" runs="${RUNS:-1000}" lanes="${LANES:-1}"
core_dir="${CORE_DIR:-/var/lib/apport/coredump}" max_bt="${MAX_BT:-2}"
ulimit -c unlimited
echo "bin sha256 $(sha256sum "$bin" | cut -d' ' -f1); libfdb_c sha256 $(sha256sum "$PARALEAN_P2_PREFIX/lib/libfdb_c.so" | cut -d' ' -f1)" > "$out/summary.txt"
bt() { # mode pid: backtrace from apport's core now (apport keeps only its latest few)
  local core="" i
  for i in $(seq 1 20); do core="$(ls "$core_dir"/core.*exit_race*."$2".* 2>/dev/null | head -1)"; [ -n "$core" ] && break; sleep 0.5; done
  [ -n "$core" ] || { echo "no core for pid $2" > "$out/$1-bt-$2.txt"; return; }
  gdb -batch -nx -ex "set debuginfod enabled off" -ex "info threads" -ex "thread apply all bt 25" \
    "$bin" "$core" > "$out/$1-bt-$2.txt" 2>&1
}
one() { # mode -> "pid rc"
  EXIT_RACE_MODE="${1%%+*}" "$bin" >/dev/null 2>&1 & local pid=$!
  wait "$pid"; local rc=$?
  if [ "$rc" -ge 128 ] && [ "$(ls "$out" | grep -c "^$1-bt-")" -lt "$max_bt" ]; then bt "$1" "$pid"; fi
  echo "$pid $rc"
}
export -f one bt; export bin out core_dir max_bt
for mode in $modes; do
  seq 1 "$runs" | xargs -P "$lanes" -I{} bash -c "one $mode" > "$out/$mode.runs"
  crashed=$(awk '$2 >= 128' "$out/$mode.runs" | wc -l)
  other=$(awk '$2 != 0 && $2 < 128' "$out/$mode.runs" | wc -l)
  echo "$mode: runs $(wc -l < "$out/$mode.runs"); signalled $crashed; other nonzero $other" | tee -a "$out/summary.txt"
done
