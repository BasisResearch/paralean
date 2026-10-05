#!/usr/bin/env bash
# P1 Mathlib corpus run (docs/p1-corpus.md M01–M18): per module, a fresh store; capture,
# replay (source, kernel, isolated), export against the pinned Mathlib checkout.
# Usage: scripts/run-mathlib.sh [WORKDIR] [IDS...]
set -u
here="$(cd "$(dirname "$0")/.." && pwd)"
repo="$(cd "$here/../.." && pwd)"
work="${1:-$HOME/tmp/p1/mathlib}"; shift || true
export TMPDIR="${TMPDIR:-$HOME/tmp}"
ML="$repo/.deps/mathlib"; export PARALEAN_MATHLIB="$ML"
export LEAN_PATH="$(cd "$ML" && lake env printenv LEAN_PATH)"
P="${PARALEAN_BIN:-$HOME/tmp/p1/bin/paralean}"
mkdir -p "$work"
grep -E '^M[0-9]+' "$repo/corpus/modules.txt" | while read -r id mod _; do
  if [ $# -gt 0 ] && ! printf '%s\n' "$@" | grep -qx "$id"; then continue; fi
  f="$(echo "$mod" | tr . /).lean"
  d="$work/$id"; rm -rf "$d"; mkdir -p "$d"
  {
    echo "### $id $mod"
    /usr/bin/time -f "capture-time %e s maxrss %M KB" "$P" capture --store "$d/store" --ws "$id" --root "$ML" "$f"
    /usr/bin/time -f "replay-time %e s maxrss %M KB" "$P" replay --store "$d/store" --isolated 1
    /usr/bin/time -f "export-time %e s maxrss %M KB" "$P" export --store "$d/store" --out "$d/export" --mathlib "$ML"
    "$P" stats --store "$d/store"
  } > "$d/log.txt" 2>&1
  grep -E "^###|=>|^source|^kernel|^isolated|^stock|^verify|-time|^STATS" "$d/log.txt"
done
