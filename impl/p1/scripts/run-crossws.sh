#!/usr/bin/env bash
# F14 B→A→B: B captures (helper_c fails: helper unknown), A captures against B's group,
# B re-captures (A's group injected once helper_b re-appears), replay, export.
# Usage: scripts/run-crossws.sh [WORKDIR]   (default $PARALEAN_RUNS/crossws)
set -u
source "$(dirname "$0")/env.sh"
require_bin
work="${1:-$PARALEAN_RUNS/crossws}"
P="$PARALEAN_BIN"; C="$REPO/corpus/fixtures/crossws"
rm -rf "$work"; mkdir -p "$work"; S="$work/store"
"$P" capture --store "$S" --ws B --root "$C" ws_b/B.lean
"$P" capture --store "$S" --ws A --root "$C" ws_a/A.lean
"$P" capture --store "$S" --ws B --root "$C" ws_b/B.lean
"$P" replay --store "$S" --isolated 1
"$P" export --store "$S" --out "$work/export"
"$P" stats --store "$S"
