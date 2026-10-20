#!/usr/bin/env bash
# Full P1 gate run. Logs go to impl/p1/results/ (or $PARALEAN_RESULTS).
# Usage: scripts/run-all.sh [WORKDIR] [--no-mathlib] [--reuse-mathlib]
# Defaults (scripts/env.sh): WORKDIR=$PARALEAN_RUNS/gate, binary impl/p1/.lake/build/bin/paralean,
# Mathlib .deps/mathlib. Set everything up first with scripts/bootstrap.sh [--mathlib].
# On the fork: PARALEAN_LEAN=fork PARALEAN_RESULTS=impl/p1/results/fork scripts/run-all.sh
# (adds scripts/simp-cost.sh; PARALEAN_FORK_HOOKS selects fork hooks vs library workarounds).
set -u
source "$(dirname "$0")/env.sh"
require_bin
mathlib=1; reuse_mathlib=0; W=""
for a in "$@"; do
  case "$a" in
    --no-mathlib) mathlib=0 ;;
    --reuse-mathlib) reuse_mathlib=1 ;;
    *) W="$a" ;;
  esac
done
W="${W:-$PARALEAN_RUNS/gate}"
if [ "$mathlib" = 1 ]; then require_mathlib; fi
P="$PARALEAN_BIN"
here="$P1_DIR"
R="${PARALEAN_RESULTS:-$here/results}"; mkdir -p "$R" "$W"
status="$R/stage-status.tsv"
printf 'stage\texit\n' > "$status"
record_status() { printf '%s\t%s\n' "$1" "$2" >> "$status"; }
{ echo "host: $(uname -srm)"; echo "lean: $(lean --githash) (PARALEAN_LEAN=$PARALEAN_LEAN; $( [ "$PARALEAN_LEAN" = fork ] && echo "$PARALEAN_FORK_PREFIX" || echo "$ELAN_TOOLCHAIN"))"
  echo "fork hooks: ${PARALEAN_FORK_HOOKS:-all available}"; echo "date: $(date -u +%FT%TZ)"; } > "$R/run-env.txt"
"$here/scripts/run-core.sh" "$W/core" > "$R/core.log" 2>&1
record_status core "$?"
"$P" stats --store "$W/core/store" >> "$R/core.log" 2>&1
record_status core-stats "$?"
# OPEN-14 experiment: the same export without the `Elab.async false` pin (stock async)
PARALEAN_EXPORT_ASYNC=1 "$P" export --store "$W/core/store" --out "$W/core/export-async" > "$R/core-async-export.log" 2>&1
record_status core-async-export "$?"
"$here/scripts/run-crossws.sh" "$W/crossws" > "$R/crossws.log" 2>&1
record_status crossws "$?"
( S="$W/f15"; rm -rf "$S"
  "$P" capture --store "$S/store" --ws F15 --root "$REPO/corpus/fixtures" Fixtures/F15Module.lean
  echo "capture-exit=$?"
  "$P" replay --store "$S/store" --isolated 1
  echo "replay-exit=$?"
  "$P" export --store "$S/store" --out "$S/export"
  echo "export-exit=$?"
  "$P" stats --store "$S/store"
  echo "stats-exit=$?" ) > "$R/f15.log" 2>&1
record_status f15 "$?"
# G4 source/line mapping probe (accepted declarations with known stock diagnostics)
( S="$W/diagmap"; rm -rf "$S"
  "$P" capture --store "$S/store" --ws D --root "$here/fixtures/diagmap" DiagMap.lean
  echo "capture-exit=$?"
  "$P" replay --store "$S/store" --isolated 1
  echo "replay-exit=$?"
  "$P" export --store "$S/store" --out "$S/export"
  echo "export-exit=$?" ) > "$R/diagmap.log" 2>&1
record_status diagmap "$?"
if [ "$mathlib" = 1 ]; then
  ML="$PARALEAN_MATHLIB"
  ( LEAN_PATH="$(mathlib_lean_path)"; export LEAN_PATH; S="$W/f16"; rm -rf "$S"
    "$P" capture --store "$S/store" --ws F16 --root "$REPO/corpus/mathlib-fixtures" F16MathlibAttrs.lean
    echo "capture-exit=$?"
    "$P" replay --store "$S/store" --isolated 1
    echo "replay-exit=$?"
    "$P" export --store "$S/store" --out "$S/export" --mathlib "$ML"
    echo "export-exit=$?"
    "$P" stats --store "$S/store"
    echo "stats-exit=$?" ) > "$R/f16.log" 2>&1
  record_status f16 "$?"
  if [ "$reuse_mathlib" = 1 ]; then
    for i in $(seq -w 1 18); do
      log="$W/mathlib/M$i/log.txt"
      [ -f "$log" ] && grep -q '^capture-exit=0$' "$log" &&
        grep -q '^replay-exit=0$' "$log" && grep -q '^stats-exit=0$' "$log" &&
        grep -q '^stock lake build: OK ' "$log" || die "cannot reuse incomplete Mathlib $i at $log"
    done
    record_status mathlib-reused 0
  else
    "$here/scripts/run-mathlib.sh" "$W/mathlib" > "$R/mathlib-summary.log" 2>&1
    record_status mathlib "$?"
  fi
  for d in "$W"/mathlib/M*; do cp "$d/log.txt" "$R/mathlib-$(basename "$d").log"; done
fi
"$here/scripts/run-negative.sh" "$W/negative" > "$R/negative.log" 2>&1
record_status negative "$?"
"$P" fasync --file "$here/fixtures/fasync/FAsync.lean" --store "$W/fasync" > "$R/fasync.log" 2>&1
record_status fasync "$?"
# fork only: native `simp` record (hook 4) against the library's dry-run replay
if [ "$mathlib" = 1 ] && [ "$PARALEAN_LEAN" = fork ]; then
  "$here/scripts/simp-cost.sh" "$W/simp-cost" > "$R/simp-cost.tsv" 2> "$R/simp-cost.err"
  record_status simp-cost "$?"
fi
python3 "$here/scripts/g2.py" "$W" > "$R/g2.txt" 2>&1
record_status g2 "$?"
python3 "$here/scripts/g4.py" "$W" > "$R/g4.txt" 2>&1
record_status g4 "$?"
python3 "$here/scripts/summarize.py" > /dev/null
record_status summarize "$?"
echo done
