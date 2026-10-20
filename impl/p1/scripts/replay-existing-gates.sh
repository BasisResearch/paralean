#!/usr/bin/env bash
# Re-run G1 from existing private gate stores with the selected P1 binary.
# Usage: replay-existing-gates.sh GATE_WORKDIR RESULT_DIR [SET ...]
# Defaults to all 22 corpus sets plus the eight-group G4 diagnostic probe.
set -u
source "$(dirname "$0")/env.sh"
require_bin
require_mathlib
W="${1:?gate work directory required}"
R="${2:?result directory required}"
shift 2
if [ "$#" -eq 0 ]; then
  set -- core crossws f15 f16 $(seq -f 'M%02g' 1 18) diagmap
fi
mkdir -p "$R"
snapshot="${PARALEAN_LIB%/.lake/build/lib/lean}"
sha256sum "$PARALEAN_BIN" "$snapshot/Paralean/Replay.lean" \
  "$PARALEAN_LIB/Paralean/Replay.olean" "$PARALEAN_LIB/Paralean/Materialize.olean" \
  "$PARALEAN_LIB/Paralean/Export.olean" > "$R/source-hashes.txt" || exit 2
{ printf 'lean_githash\t%s\n' "$(lean --githash)"
  printf 'mathlib_commit\t%s\n' "$(git -C "$PARALEAN_MATHLIB" rev-parse HEAD)"
  printf 'binary\t%s\n' "$PARALEAN_BIN"
  printf 'library\t%s\n' "$PARALEAN_LIB"; } > "$R/run-env.tsv"
ml_path="$(mathlib_lean_path)" || exit 2
printf 'set\texit\tsource_ok\tsource_total\tkernel_ok\tkernel_total\tisolated_ok\tisolated_total\n' > "$R/status.tsv"
for label in "$@"; do
  case "$label" in
    M[0-9][0-9]) base="$W/mathlib/$label"; use_ml=1 ;;
    f16) base="$W/f16"; use_ml=1 ;;
    core|crossws|f15|diagmap) base="$W/$label"; use_ml=0 ;;
    *) echo "unknown set: $label" >&2; exit 2 ;;
  esac
  [ -d "$base/store/files" ] || { echo "missing store: $base" >&2; exit 2; }
  if [ "$use_ml" -eq 1 ]; then
    env -u LEAN_PARALEAN LEAN_PATH="$ml_path" "$PARALEAN_BIN" replay \
      --store "$base/store" --isolated 1 > "$R/$label.log" 2>&1
  else
    env -u LEAN_PARALEAN -u LEAN_PATH "$PARALEAN_BIN" replay \
      --store "$base/store" --isolated 1 > "$R/$label.log" 2>&1
  fi
  rc=$?
  nums="$(python3 - "$R/$label.log" <<'PY'
import re, sys
s = open(sys.argv[1]).read()
patterns = [r'^source replay: (\d+)/(\d+)', r'^kernel replay: (\d+)/(\d+)',
            r'^isolated replay \(exact deps only\): (\d+)/(\d+)']
values = []
for pat in patterns:
    m = re.search(pat, s, re.M)
    values += list(m.groups()) if m else ['-', '-']
print('\t'.join(values))
PY
)"
  printf '%s\t%s\t%s\n' "$label" "$rc" "$nums" >> "$R/status.tsv"
done
python3 - "$R/status.tsv" > "$R/summary.txt" <<'PY'
import csv, sys
rows = list(csv.DictReader(open(sys.argv[1]), delimiter='\t'))
total = {k: [0, 0] for k in ('source', 'kernel', 'isolated')}
bad = []
for r in rows:
    for k in total:
        try: a, b = int(r[f'{k}_ok']), int(r[f'{k}_total'])
        except ValueError:
            bad.append(f"{r['set']}: missing {k} count")
            continue
        if r['set'] != 'diagmap':
            total[k][0] += a; total[k][1] += b
        if a != b: bad.append(f"{r['set']}: {k} {a}/{b}")
    if int(r['exit']) != 0: bad.append(f"{r['set']}: exit {r['exit']}")
for k, (a, b) in total.items(): print(f'{k}: {a}/{b}')
print(f'corpus_sets: {sum(r["set"] != "diagmap" for r in rows)}')
print(f'diagnostic_probe: {sum(r["set"] == "diagmap" for r in rows)}')
for item in bad: print(f'failure: {item}')
sys.exit(0 if not bad else 1)
PY
rc=$?
cat "$R/summary.txt"
exit "$rc"
