#!/usr/bin/env bash
# Full P1 gate run. Logs go to impl/p1/results/ (or $PARALEAN_RESULTS).
# Usage: scripts/run-all.sh [WORKDIR] [--no-mathlib]
# Defaults (scripts/env.sh): WORKDIR=$PARALEAN_RUNS/gate, binary impl/p1/.lake/build/bin/paralean,
# Mathlib .deps/mathlib. Set everything up first with scripts/bootstrap.sh [--mathlib].
set -u
source "$(dirname "$0")/env.sh"
require_bin
mathlib=1; W=""
for a in "$@"; do
  case "$a" in
    --no-mathlib) mathlib=0 ;;
    *) W="$a" ;;
  esac
done
W="${W:-$PARALEAN_RUNS/gate}"
if [ "$mathlib" = 1 ]; then require_mathlib; fi
P="$PARALEAN_BIN"
here="$P1_DIR"
R="${PARALEAN_RESULTS:-$here/results}"; mkdir -p "$R" "$W"
{ echo "host: $(uname -srm)"; echo "lean: $(lean --githash) ($ELAN_TOOLCHAIN)"; echo "date: $(date -u +%FT%TZ)"; } > "$R/run-env.txt"
"$here/scripts/run-core.sh" "$W/core" > "$R/core.log" 2>&1
"$P" stats --store "$W/core/store" >> "$R/core.log" 2>&1
# OPEN-14 experiment: the same export without the `Elab.async false` pin (stock async)
PARALEAN_EXPORT_ASYNC=1 "$P" export --store "$W/core/store" --out "$W/core/export-async" > "$R/core-async-export.log" 2>&1
"$here/scripts/run-crossws.sh" "$W/crossws" > "$R/crossws.log" 2>&1
( S="$W/f15"; rm -rf "$S"
  "$P" capture --store "$S/store" --ws F15 --root "$REPO/corpus/fixtures" Fixtures/F15Module.lean
  "$P" replay --store "$S/store" --isolated 1
  "$P" export --store "$S/store" --out "$S/export"
  "$P" stats --store "$S/store" ) > "$R/f15.log" 2>&1
# G4 source/line mapping probe (accepted declarations with known stock diagnostics)
( S="$W/diagmap"; rm -rf "$S"
  "$P" capture --store "$S/store" --ws D --root "$here/fixtures/diagmap" DiagMap.lean
  "$P" replay --store "$S/store" --isolated 1
  "$P" export --store "$S/store" --out "$S/export" ) > "$R/diagmap.log" 2>&1
if [ "$mathlib" = 1 ]; then
  ML="$PARALEAN_MATHLIB"
  ( LEAN_PATH="$(mathlib_lean_path)"; export LEAN_PATH; S="$W/f16"; rm -rf "$S"
    "$P" capture --store "$S/store" --ws F16 --root "$REPO/corpus/mathlib-fixtures" F16MathlibAttrs.lean
    "$P" replay --store "$S/store" --isolated 1
    "$P" export --store "$S/store" --out "$S/export" --mathlib "$ML"
    "$P" stats --store "$S/store" ) > "$R/f16.log" 2>&1
  "$here/scripts/run-mathlib.sh" "$W/mathlib" > "$R/mathlib-summary.log" 2>&1
  for d in "$W"/mathlib/M*; do cp "$d/log.txt" "$R/mathlib-$(basename "$d").log"; done
fi
"$here/scripts/run-negative.sh" "$W/negative" > "$R/negative.log" 2>&1
"$P" fasync --file "$here/fixtures/fasync/FAsync.lean" --store "$W/fasync" > "$R/fasync.log" 2>&1
python3 "$here/scripts/g2.py" "$W" > "$R/g2.txt" 2>&1
python3 "$here/scripts/g4.py" "$W" > "$R/g4.txt" 2>&1
python3 "$here/scripts/summarize.py" > /dev/null
echo done
