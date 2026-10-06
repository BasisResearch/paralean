#!/usr/bin/env bash
# Cost of the fork's native `simp` used-lemma record (fork hook 4) against the library's dry-run
# replay (Paralean/Hooks.lean), on one fork binary: capture with every fork hook, and with every
# fork hook except `simp` (PARALEAN_FORK_HOOKS=sync,noaxiom,instnames,collector, so the dry-run
# replay records the lemmas). Best of N CPU times (user+sys; wall time is too noisy on a shared
# machine for 2-5 s captures) per module, and a check that both modes produce identical package
# IDs (which hash the simp-derived frontend dependencies).
# Usage: PARALEAN_LEAN=fork scripts/simp-cost.sh [WORKDIR] [IDS...]  (default M01 M03 M13 M16 M18, N=5)
# Output: TSV on stdout (module, groups, simp/simp_all call sites in the source, native CPU s,
# dry-run CPU s, dry-run - native, dry-run/native, package IDs equal).
set -u
source "$(dirname "$0")/env.sh"
require_bin
require_mathlib
work="${1:-$PARALEAN_RUNS/simp-cost}"; shift || true
ids="${*:-M01 M03 M13 M16 M18}"
N="${PARALEAN_SIMP_COST_N:-5}"
ML="$PARALEAN_MATHLIB"
LEAN_PATH="$(mathlib_lean_path)" || die "cannot compute Mathlib's LEAN_PATH"
export LEAN_PATH
P="$PARALEAN_BIN"
mkdir -p "$work"
best() { # mode-env store file -> best CPU seconds
  local envs=$1 store=$2 f=$3 b="" t
  for _ in $(seq "$N"); do
    rm -rf "$store"
    /usr/bin/time -f "%U %S" -o "$work/.t" env $envs "$P" capture --store "$store" --ws W --root "$ML" "$f" >/dev/null 2>&1
    t=$(tail -1 "$work/.t" | awk '{printf "%.2f", $1 + $2}')
    if [ -z "$b" ] || python3 -c "import sys; sys.exit(0 if float('$t') < float('$b') else 1)"; then b=$t; fi
  done
  echo "$b"
}
groups() { python3 -c 'import json,glob,sys; print(" ".join(g for f in sorted(glob.glob(sys.argv[1]+"/files/*.json")) for g in json.load(open(f))["groups"]))' "$1"; }
printf "module\tgroups\tsimp_sites\tnative_cpu_s\tdryrun_cpu_s\tdelta_s\tratio\tpackage_ids_equal\n"
for id in $ids; do
  mod=$(awk -v i="$id" '$1==i {print $2}' "$REPO/corpus/modules.txt")
  f="$(echo "$mod" | tr . /).lean"
  a=$(best "PARALEAN_FORK_HOOKS=all" "$work/$id-native" "$f")
  b=$(best "PARALEAN_FORK_HOOKS=sync,noaxiom,instnames,collector" "$work/$id-dryrun" "$f")
  ga=$(groups "$work/$id-native"); gb=$(groups "$work/$id-dryrun")
  n=$(echo "$ga" | wc -w | tr -d ' ')
  eq=$([ "$ga" = "$gb" ] && echo yes || echo NO)
  sites=$(grep -cE '(^|[^_[:alnum:]])simp(_all)?([^_[:alnum:]?!]|$)' "$ML/$f" || true)
  printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$id" "$n" "$sites" "$a" "$b" "$(python3 -c "print(f'{$b-$a:.2f}')")" "$(python3 -c "print(f'{$b/$a:.3f}')")" "$eq"
done
