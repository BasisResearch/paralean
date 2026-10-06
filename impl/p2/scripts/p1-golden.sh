#!/usr/bin/env bash
# Equality check between P1 and P2 group IDs (docs/p0-interfaces.md §1.1/§1.2; p2-log.md
# deviation 10, fixed). For every group object of each P1 store, P2 recomputes
# H("v0/group", bytes) and `paralean-p2 check-p1` requires it to equal P1's declId (the object's
# file name). Exit 1 on any mismatch.
# Usage: scripts/p1-golden.sh [P1_STORE...]
# Without arguments, captures the P1 core fixtures F01-F13 into a temporary store with the P1
# binary (impl/p1/scripts/env.sh: bootstrap P1 first; PARALEAN_LEAN=fork for the fork) and checks it.
# Needs no P2 services. The Rust test `id::tests::p1_group_id_matches` pins one P1 group's bytes and ID.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
source "$here/env.sh"
(cd "$here/.." && cargo build --release -q -p paralean-cli)
p2="$here/../target/release/paralean-p2"
stores=("$@")
if [ ${#stores[@]} -eq 0 ]; then
  store="$( source "$here/../../p1/scripts/env.sh"; require_bin
    tmp="$(mktemp -d)"
    for f in F01Theorem F02Def F03Structure F04Inductive F05Mutual F06Structural F07WellFounded \
             F08PrivateGenerated F09InstanceOnly F10SimpAttrDecl F10SimpAttrUse F11ScopedDecl \
             F11ScopedUse F12Macro F13InitDecl F13InitUse; do
      "$PARALEAN_BIN" capture --store "$tmp/store" --ws F --root "$REPO/corpus/fixtures" "Fixtures/$f.lean" >/dev/null
    done
    echo "$tmp/store" )"
  stores=("$store")
fi
rc=0
for s in "${stores[@]}"; do
  echo "## $s"
  "$p2" check-p1 "$s" | tail -1 || rc=1
done
exit $rc
