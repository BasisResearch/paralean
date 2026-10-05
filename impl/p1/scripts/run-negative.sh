#!/usr/bin/env bash
# Negative fixtures N1–N6 (corpus/fixtures/negative), a transitive version conflict, and a
# duplicate instance in two workspaces. Usage: scripts/run-negative.sh [WORKDIR]
# (default $PARALEAN_RUNS/negative)
set -u
source "$(dirname "$0")/env.sh"
require_bin
here="$P1_DIR"
work="${1:-$PARALEAN_RUNS/negative}"
P="$PARALEAN_BIN"
N="$REPO/corpus/fixtures/negative"
rm -rf "$work"; mkdir -p "$work"
# G5: a rejected group must not be staged in the publishable namespace (objects/, meta/);
# it is kept for audit in audit/ only
staged() { # store -> "publishable objects N (published M); audit objects K"
  local s=$1 n=0 a=0 pub=0
  [ -d "$s/objects" ] && n=$(find "$s/objects" -name '*.grp' | wc -l | tr -d ' ')
  [ -d "$s/audit/objects" ] && a=$(find "$s/audit/objects" -name '*.grp' | wc -l | tr -d ' ')
  pub=$(python3 -c 'import json,glob,sys; print(sum(len(json.load(open(f))["groups"]) for f in glob.glob(sys.argv[1]+"/files/*.json")))' "$s")
  echo "  store: publishable objects $n (published groups $pub); audit objects $a"
}
for n in N1Sorry N2Axiom N3SkipKernel N6NativeDecide; do
  echo "### $n"; "$P" capture --store "$work/$n" --ws "$n" --root "$N" "$n.lean"; echo "exit=$?"
  staged "$work/$n"
done
echo "### N3 audit: kernel re-check of the rejected group by the validator"
"$P" replay --store "$work/N3SkipKernel" --include-rejected 1
echo "### N4ChangedTarget"
"$P" capture --store "$work/N4ref" --ws ref --root "$here/fixtures/negative-ref" N4Ref.lean
"$P" contract --store "$work/N4ref" --names N4.target > "$work/N4-targets.json"; cat "$work/N4-targets.json"
"$P" capture --store "$work/N4" --ws N4 --root "$N" --targets "$work/N4-targets.json" N4ChangedTarget.lean; echo "exit=$?"
staged "$work/N4"
echo "### N5ChangedDep"
"$P" capture --store "$work/N5" --ws N5 --root "$N" N5ChangedDep.lean
"$P" contract --store "$work/N5" --names N5.value_zero > "$work/N5-targets.json"; cat "$work/N5-targets.json"
echo "-- upstream revision value := 1, same file re-captured:"
"$P" capture --store "$work/N5" --ws N5 --root "$here/fixtures/n5rev" --targets "$work/N5-targets.json" N5ChangedDep.lean; echo "exit=$?"
staged "$work/N5"
echo "### version conflict (concurrent: ws1 and ws2 partitioned, then merged)"
C="$here/fixtures/conflict"
"$P" capture --store "$work/conf1" --ws ws1 --root "$C/ws1" C1.lean
"$P" capture --store "$work/conf2" --ws ws2 --root "$C/ws2" C2.lean
"$P" merge --into "$work/conf" --from "$work/conf1"
"$P" merge --into "$work/conf" --from "$work/conf2"
"$P" capture --store "$work/conf" --ws ws3 --root "$C/ws3" Use.lean; echo "exit=$?"
"$P" export --store "$work/conf" --out "$work/conf-export"; echo "export exit=$?"
echo "### duplicate instance (canonical instance names; concurrent ws1 and ws2, then merged)"
D="$here/fixtures/instdup"
"$P" capture --store "$work/inst1" --ws ws1 --root "$D/ws1" I1.lean
"$P" capture --store "$work/inst2" --ws ws2 --root "$D/ws2" I2.lean
"$P" merge --into "$work/inst" --from "$work/inst1"
"$P" merge --into "$work/inst" --from "$work/inst2"
python3 - "$work/inst" <<'PY'
import json, glob, sys
for f in sorted(glob.glob(sys.argv[1] + "/meta/*.json")):
    g = json.load(open(f))
    for m in g["members"]:
        if m.get("stock"):
            print("  %s: %s (stock spelling %s)" % (g["gid"][:12], ".".join(map(str, m["name"])), ".".join(map(str, m["stock"]))))
PY
"$P" capture --store "$work/inst" --ws ws3 --root "$D/ws3" UseI.lean; echo "exit=$?"
"$P" export --store "$work/inst" --out "$work/inst-export"; echo "export exit=$?"
echo "-- the same two files captured sequentially in one workspace:"
"$P" capture --store "$work/instseq" --ws ws1 --root "$D/ws1" I1.lean
"$P" capture --store "$work/instseq" --ws ws1 --root "$D/ws2" I2.lean; echo "exit=$?"
