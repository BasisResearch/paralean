#!/usr/bin/env bash
# F14 B→A→B: B captures (helper_c fails: helper unknown), A captures against B's group,
# B re-captures (A's group injected once helper_b re-appears), replay, export.
set -u
here="$(cd "$(dirname "$0")/.." && pwd)"; repo="$(cd "$here/../.." && pwd)"
work="${1:-$HOME/tmp/p1/crossws}"; export TMPDIR="${TMPDIR:-$HOME/tmp}"
P="${PARALEAN_BIN:-$HOME/tmp/p1/bin/paralean}"; C="$repo/corpus/fixtures/crossws"
rm -rf "$work"; mkdir -p "$work"; S="$work/store"
"$P" capture --store "$S" --ws B --root "$C" ws_b/B.lean
"$P" capture --store "$S" --ws A --root "$C" ws_a/A.lean
"$P" capture --store "$S" --ws B --root "$C" ws_b/B.lean
"$P" replay --store "$S" --isolated 1
"$P" export --store "$S" --out "$work/export"
"$P" stats --store "$S"
