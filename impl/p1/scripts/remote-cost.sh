#!/usr/bin/env bash
# Track B measurements: publish every group of a Mathlib corpus module as one shared file,
# elaborate the projection (all `remote%`) standalone, and compare with local elaboration.
set -u
here="$(cd "$(dirname "$0")/.." && pwd)"; repo="$(cd "$here/../.." && pwd)"
G="${GATE:-$HOME/tmp/p1/gate/mathlib}"; W="${1:-$HOME/tmp/p1/remote-cost}"
export TMPDIR="${TMPDIR:-$HOME/tmp}" PARALEAN_RECEIPT_KEY="p1-demo-validator-key" PARALEAN_VISIBILITY=1
export PARALEAN_LIB="$here/.lake/build/lib/lean" PARALEAN_MATHLIB="$repo/.deps/mathlib"
export LEAN_PATH="$(cd "$repo/.deps/mathlib" && lake env printenv LEAN_PATH)"
P="${PARALEAN_BIN:-$here/.lake/build/bin/paralean}"
rm -rf "$W"; mkdir -p "$W"
printf "module\tgroups\tremote_elab_s\tlocal_capture_s\tstock_sync_s\tloads_statement\tloads_full\tplaceholders\tobject_reads\terrors\n"
for m in ${MODS:-M18 M01 M16 M13 M03 M14 M15}; do
  d="$W/$m"; mkdir -p "$d"; cp -r "$G/$m/store" "$d/store"
  "$P" validate --store "$d/store" > "$d/validate.log" 2>&1
  "$P" publish-all --store "$d/store" --file Proj.lean --out "$d/Proj.lean" > /dev/null
  rm -f "$d/remote.log"
  /usr/bin/time -o "$d/time.txt" -f "%e" env PARALEAN_STORE="$d/store" PARALEAN_REMOTE_LOG="$d/remote.log" \
    "$P" capture --store "$d/elab" --ws check --root "$d" --remote 1 Proj.lean > "$d/elab.log" 2>&1
  t=$(tail -1 "$d/time.txt")
  ng=$(grep -c "paralean:published" "$d/Proj.lean")
  ls=$(grep -c " statement " "$d/remote.log" 2>/dev/null); lf=$(grep -c " full " "$d/remote.log" 2>/dev/null)
  ph=$(grep -c "^placeholder" "$d/remote.log" 2>/dev/null)
  er=$(grep -c "\[reject" "$d/elab.log")
  lc=$(grep -o "capture-time [0-9.]*" "$here/results/mathlib-$m.log" | awk '{print $2}')
  st=$(awk -F'\t' -v id="$m" '$1==id {print $4}' "$here/results/async-cost.tsv")
  printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$m" "$ng" "$t" "$lc" "$st" "$ls" "$lf" "$ph" 0 "$er"
done
