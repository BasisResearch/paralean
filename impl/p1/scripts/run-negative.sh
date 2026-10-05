#!/usr/bin/env bash
# Negative fixtures N1–N6 (corpus/fixtures/negative) plus a transitive version conflict.
set -u
here="$(cd "$(dirname "$0")/.." && pwd)"
repo="$(cd "$here/../.." && pwd)"
work="${1:-$HOME/tmp/p1/negative}"
export TMPDIR="${TMPDIR:-$HOME/tmp}"
P="${PARALEAN_BIN:-$HOME/tmp/p1/bin/paralean}"
N="$repo/corpus/fixtures/negative"
rm -rf "$work"; mkdir -p "$work"
for n in N1Sorry N2Axiom N3SkipKernel N6NativeDecide; do
  echo "### $n"; "$P" capture --store "$work/$n" --ws "$n" --root "$N" "$n.lean"; echo "exit=$?"
done
echo "### N3 audit: kernel re-check of the rejected group by the validator"
"$P" replay --store "$work/N3SkipKernel" --include-rejected 1
echo "### N4ChangedTarget"
"$P" capture --store "$work/N4ref" --ws ref --root "$here/fixtures/negative-ref" N4Ref.lean
"$P" contract --store "$work/N4ref" --names N4.target > "$work/N4-targets.json"; cat "$work/N4-targets.json"
"$P" capture --store "$work/N4" --ws N4 --root "$N" --targets "$work/N4-targets.json" N4ChangedTarget.lean; echo "exit=$?"
echo "### N5ChangedDep"
"$P" capture --store "$work/N5" --ws N5 --root "$N" N5ChangedDep.lean
"$P" contract --store "$work/N5" --names N5.value_zero > "$work/N5-targets.json"; cat "$work/N5-targets.json"
echo "-- upstream revision value := 1, same file re-captured:"
"$P" capture --store "$work/N5" --ws N5 --root "$here/fixtures/n5rev" --targets "$work/N5-targets.json" N5ChangedDep.lean; echo "exit=$?"
echo "### version conflict (concurrent: ws1 and ws2 partitioned, then merged)"
C="$here/fixtures/conflict"
"$P" capture --store "$work/conf1" --ws ws1 --root "$C/ws1" C1.lean
"$P" capture --store "$work/conf2" --ws ws2 --root "$C/ws2" C2.lean
"$P" merge --into "$work/conf" --from "$work/conf1"
"$P" merge --into "$work/conf" --from "$work/conf2"
"$P" capture --store "$work/conf" --ws ws3 --root "$C/ws3" Use.lean; echo "exit=$?"
"$P" export --store "$work/conf" --out "$work/conf-export"; echo "export exit=$?"
