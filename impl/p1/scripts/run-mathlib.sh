#!/usr/bin/env bash
# P1 Mathlib corpus run (docs/p1-corpus.md M01–M18): per module, a fresh store; capture,
# replay (source, kernel, isolated), export against the pinned Mathlib checkout.
# Usage: scripts/run-mathlib.sh [WORKDIR] [IDS...]   (default $PARALEAN_RUNS/mathlib)
# Needs the Mathlib checkout with its .olean cache: scripts/bootstrap.sh --mathlib.
set -u
source "$(dirname "$0")/env.sh"
require_bin
require_mathlib
work="${1:-$PARALEAN_RUNS/mathlib}"; shift || true
ML="$PARALEAN_MATHLIB"
LEAN_PATH="$(mathlib_lean_path)" || die "cannot compute Mathlib's LEAN_PATH"
export LEAN_PATH
P="$PARALEAN_BIN"
# GNU time takes -f; BSD time (macOS) takes -l and prints its own format
if /usr/bin/time -f "%e" true >/dev/null 2>&1; then
  timed() { local label=$1; shift; /usr/bin/time -f "$label-time %e s maxrss %M KB" "$@"; }
else
  timed() {
    local label=$1; shift; local tf; tf=$(mktemp)
    /usr/bin/time -l -o "$tf" "$@"; local rc=$?
    awk -v l="$label" '/real/ {t=$1} /maximum resident set size/ {m=int($1/1024)} END {printf "%s-time %s s maxrss %d KB\n", l, t, m}' "$tf" >&2
    rm -f "$tf"; return $rc
  }
fi
mkdir -p "$work"
grep -E '^M[0-9]+' "$REPO/corpus/modules.txt" | while read -r id mod _; do
  if [ $# -gt 0 ] && ! printf '%s\n' "$@" | grep -qx "$id"; then continue; fi
  f="$(echo "$mod" | tr . /).lean"
  d="$work/$id"; rm -rf "$d"; mkdir -p "$d"
  {
    echo "### $id $mod"
    timed capture "$P" capture --store "$d/store" --ws "$id" --root "$ML" "$f"
    timed replay "$P" replay --store "$d/store" --isolated 1
    timed export "$P" export --store "$d/store" --out "$d/export" --mathlib "$ML"
    "$P" stats --store "$d/store"
  } > "$d/log.txt" 2>&1
  grep -E "^###|=>|^source|^kernel|^isolated|^stock|^verify|-time|^STATS" "$d/log.txt"
done
