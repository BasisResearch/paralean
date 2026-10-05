#!/usr/bin/env bash
# F-async (c): a capture cancelled after N commands, or killed mid-file, must leave nothing
# in the store: groups are written only when the file is committed.
# Usage: scripts/run-cancel.sh [WORKDIR]   (default $PARALEAN_RUNS/cancel)
set -u
source "$(dirname "$0")/env.sh"
require_bin
work="${1:-$PARALEAN_RUNS/cancel}"
P="$PARALEAN_BIN"
rm -rf "$work"; mkdir -p "$work"
count() { # store -> objects, metas, file records (publishable and audit)
  local s=$1
  printf "objects %s, meta %s, file records %s, audit objects %s\n" \
    "$(find "$s/objects" -name '*.grp' 2>/dev/null | wc -l | tr -d ' ')" \
    "$(find "$s/meta" -name '*.json' 2>/dev/null | wc -l | tr -d ' ')" \
    "$(find "$s/files" -name '*.json' 2>/dev/null | wc -l | tr -d ' ')" \
    "$(find "$s/audit/objects" -name '*.grp' 2>/dev/null | wc -l | tr -d ' ')"
}
echo "### cancelled after 4 commands (F03Structure)"
PARALEAN_CANCEL_AFTER=4 "$P" capture --store "$work/c1" --ws F --root "$REPO/corpus/fixtures" Fixtures/F03Structure.lean
echo "exit=$?"; count "$work/c1"
echo "### SIGKILL mid-file (Mathlib.Order.Basic, 213 groups, killed after 20 s)"
require_mathlib
LEAN_PATH="$(mathlib_lean_path)" "$P" capture --store "$work/c2" --ws M01 --root "$PARALEAN_MATHLIB" \
  Mathlib/Order/Basic.lean > "$work/c2.log" 2>&1 &
pid=$!; sleep 20; kill -9 "$pid" 2>/dev/null; wait "$pid" 2>/dev/null
echo "stdout lines written before the kill: $(wc -l < "$work/c2.log" | tr -d ' ')"; count "$work/c2"
echo "### uncancelled reference (F03Structure)"
"$P" capture --store "$work/c3" --ws F --root "$REPO/corpus/fixtures" Fixtures/F03Structure.lean > /dev/null
count "$work/c3"
