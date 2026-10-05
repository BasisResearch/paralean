#!/usr/bin/env bash
# P1 core-fixture run: capture F01–F13 (one workspace), replay (source, kernel, isolated),
# export to a clean stock-Lean package. Usage: scripts/run-core.sh [WORKDIR]
set -u
here="$(cd "$(dirname "$0")/.." && pwd)"
repo="$(cd "$here/../.." && pwd)"
work="${1:-$HOME/tmp/p1/core}"
export TMPDIR="${TMPDIR:-$HOME/tmp}"
P="${PARALEAN_BIN:-$HOME/tmp/p1/bin/paralean}"
R="$repo/corpus/fixtures"
rm -rf "$work"; mkdir -p "$work"
S="$work/store"
for f in F01Theorem F02Def F03Structure F04Inductive F05Mutual F06Structural F07WellFounded \
         F08PrivateGenerated F09InstanceOnly F10SimpAttrDecl F10SimpAttrUse F11ScopedDecl \
         F11ScopedUse F12Macro F13InitDecl F13InitUse; do
  "$P" capture --store "$S" --ws F --root "$R" "Fixtures/$f.lean"
done
"$P" replay --store "$S" --isolated 1
"$P" export --store "$S" --out "$work/export"
