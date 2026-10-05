#!/usr/bin/env bash
# Full P1 gate run. Logs go to impl/p1/results/.
set -u
here="$(cd "$(dirname "$0")/.." && pwd)"; repo="$(cd "$here/../.." && pwd)"
export TMPDIR="${TMPDIR:-$HOME/tmp}"
P="${PARALEAN_BIN:-$HOME/tmp/p1/bin/paralean}"; export PARALEAN_BIN="$P"
R="$here/results"; W="${1:-$HOME/tmp/p1/gate}"; mkdir -p "$R" "$W"
"$here/scripts/run-core.sh" "$W/core" > "$R/core.log" 2>&1
"$P" stats --store "$W/core/store" >> "$R/core.log" 2>&1
"$here/scripts/run-crossws.sh" "$W/crossws" > "$R/crossws.log" 2>&1
( S="$W/f15"; rm -rf "$S"
  "$P" capture --store "$S/store" --ws F15 --root "$repo/corpus/fixtures" Fixtures/F15Module.lean
  "$P" replay --store "$S/store" --isolated 1
  "$P" export --store "$S/store" --out "$S/export"
  "$P" stats --store "$S/store" ) > "$R/f15.log" 2>&1
ML="$repo/.deps/mathlib"
( export LEAN_PATH="$(cd "$ML" && lake env printenv LEAN_PATH)"; S="$W/f16"; rm -rf "$S"
  "$P" capture --store "$S/store" --ws F16 --root "$repo/corpus/mathlib-fixtures" F16MathlibAttrs.lean
  "$P" replay --store "$S/store" --isolated 1
  "$P" export --store "$S/store" --out "$S/export" --mathlib "$ML"
  "$P" stats --store "$S/store" ) > "$R/f16.log" 2>&1
"$here/scripts/run-mathlib.sh" "$W/mathlib" > "$R/mathlib-summary.log" 2>&1
for d in "$W"/mathlib/M*; do cp "$d/log.txt" "$R/mathlib-$(basename "$d").log"; done
"$here/scripts/run-negative.sh" "$W/negative" > "$R/negative.log" 2>&1
"$P" fasync --file "$here/fixtures/fasync/FAsync.lean" --store "$W/fasync" > "$R/fasync.log" 2>&1
echo done
