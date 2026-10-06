#!/usr/bin/env bash
# Print SHA-256 golden vectors computed by P1's pure-Lean implementation
# (impl/p1/Paralean/Sha256.lean) with P1's pinned toolchain. The Rust test
# `id::tests::matches_p1_lean_sha256` hard-codes this output.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
p1="$here/../../p1"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
{ sed -e '/^module$/d' -e '/^@\[expose\] public section$/d' "$p1/Paralean/Sha256.lean"; cat <<'LEAN'

open Paralean.Sha256 in
def main : IO Unit := do
  let inputs : List ByteArray := [
    "".toUTF8, "abc".toUTF8,
    "paralean\x00v0/group\x00xyz".toUTF8,
    ByteArray.mk ((List.range 1000).map (fun i => (i % 251).toUInt8)).toArray,
    "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8 ]
  for i in inputs do
    IO.println (hashHex i)
LEAN
} > "$tmp/Golden.lean"
cd "$tmp" && elan run "$(sed 's/-nightly:/:/' "$p1/lean-toolchain" | sed 's/lean4:/lean4:/')" lean --run Golden.lean
