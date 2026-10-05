#!/usr/bin/env bash
# Elaboration cost of Elab.async=false vs the stock default (true), stock `lean`, per corpus
# file; best of N runs of wall time, plus CPU time. Output: TSV on stdout.
set -u
here="$(cd "$(dirname "$0")/.." && pwd)"; repo="$(cd "$here/../.." && pwd)"
export TMPDIR="${TMPDIR:-$HOME/tmp}"
N="${N:-3}"
LEAN="$HOME/.elan/toolchains/leanprover--lean4-nightly---nightly-2026-10-03/bin/lean"
ML="$repo/.deps/mathlib"
MLP="$(cd "$ML" && lake env printenv LEAN_PATH)"
FX="$repo/corpus/fixtures"
(cd "$FX" && lake build >/dev/null 2>&1)
FXP="$FX/.lake/build/lib/lean:$MLP"
measure() { # path leanpath async -> best wall, cpu of that run
  local best=999999 bcpu=0
  for _ in $(seq "$N"); do
    local tf; tf=$(mktemp)
    /usr/bin/time -o "$tf" -f "%e %U %S" env LEAN_PATH="$2" "$LEAN" -DElab.async="$3" "$1" >/dev/null 2>&1
    local out; out=$(tail -1 "$tf"); rm -f "$tf"
    local w u s; read -r w u s <<<"$out"
    if awk "BEGIN{exit !($w < $best)}"; then best=$w; bcpu=$(awk "BEGIN{print $u+$s}"); fi
  done
  echo "$best $bcpu"
}
printf "file\twall_async_s\tcpu_async_s\twall_sync_s\tcpu_sync_s\n"
for f in "$FX"/Fixtures/F*.lean "$repo"/corpus/mathlib-fixtures/F16MathlibAttrs.lean "$here"/fixtures/fasync/FAsync.lean; do
  read -r wa ca <<<"$(measure "$f" "$FXP" true)"; read -r ws cs <<<"$(measure "$f" "$FXP" false)"
  printf "%s\t%s\t%s\t%s\t%s\n" "$(basename "$f")" "$wa" "$ca" "$ws" "$cs"
done
grep -E '^M[0-9]+' "$repo/corpus/modules.txt" | while read -r id mod _; do
  f="$ML/$(echo "$mod" | tr . /).lean"
  read -r wa ca <<<"$(measure "$f" "$MLP" true)"; read -r ws cs <<<"$(measure "$f" "$MLP" false)"
  printf "%s\t%s\t%s\t%s\t%s\n" "$id" "$wa" "$ca" "$ws" "$cs"
done
