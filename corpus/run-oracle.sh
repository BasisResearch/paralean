#!/usr/bin/env bash
# Run the P0 reference oracle (stock Lean, synchronous) over the P1 extraction corpus.
# Writes corpus/reference/<id>.jsonl and corpus/reference/summary.tsv.
set -euo pipefail
cd -- "$(dirname -- "$0")/.."
root=$PWD
mathlib=${MATHLIB:-$root/.deps/mathlib}
out=$root/corpus/reference
tool=$root/corpus/tools/CommandDecls.lean
mkdir -p "$out"
export TMPDIR=${TMPDIR:-$HOME/tmp}
(cd corpus/fixtures && lake build -q)

summ() { # id file jsonl rc secs
  python3 - "$@" <<'PY'
import json,sys,collections
i,f,j,rc,secs=sys.argv[1:]
rows=[json.loads(l) for l in open(j) if l.startswith('{')]
c=collections.Counter(a['class'] for r in rows for a in r['added'])
zero=sum(1 for r in rows if not r['added'])
src=sum(r.get('bytes',0) for r in rows); grp=sum(1 for r in rows if r['added'])
print('\t'.join(map(str,[i,f.split('/')[-1],rc,len(rows),grp,src,sum(c.values()),c['public'],c['scoped-generated'],c['scoped-private'],c['reserved'],zero,sum(r['errors'] for r in rows),secs])))
PY
}
printf 'id\tsource\toracle_rc\tcommands\tgroups\tsrc_bytes\tconstants\tpublic\tscoped_generated\tscoped_private\treserved\tzero_const_cmds\terrors\tsecs\n' > "$out/summary.tsv"
run() { # id dir file module
  local id=$1 dir=$2 file=$3 mod=$4 rc=0 t0 t1
  t0=$(date +%s.%N)
  (cd "$dir" && lake env lean --run "$tool" "$file" "$mod") > "$out/$id.jsonl" 2> "$out/$id.stderr" || rc=$?
  t1=$(date +%s.%N)
  summ "$id" "$file" "$out/$id.jsonl" "$rc" "$(printf '%.1f' "$(echo "$t1 - $t0" | bc)")" >> "$out/summary.tsv"
}
for f in $(cd corpus/fixtures && find Fixtures -name '*.lean' | sort); do
  m=${f%.lean}; m=${m//\//.}
  id=${f#Fixtures/}; id=${id%.lean}; id=${id//\//-}
  run "$id" "$root/corpus/fixtures" "$f" "$m"
done
run F16MathlibAttrs "$mathlib" "$root/corpus/mathlib-fixtures/F16MathlibAttrs.lean" F16MathlibAttrs
grep -v '^#' corpus/modules.txt | while read -r id mod _; do
  [ -n "$id" ] || continue
  run "$id" "$mathlib" "$mathlib/${mod//.//}.lean" "$mod"
done
column -t -s $'\t' "$out/summary.tsv"
