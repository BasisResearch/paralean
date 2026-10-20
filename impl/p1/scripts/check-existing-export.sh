#!/usr/bin/env bash
# Invoke production verifyExport against already-built export OLeans without writing them.
# Usage: check-existing-export.sh GATE_WORKDIR RESULT_DIR [SET ...]
# SET is core, crossws, f15, f16, diagmap, or M01..M18; default is all 23.
# Set PARALEAN_BIN/LIB, PARALEAN_LEAN, PARALEAN_MATHLIB, and fork prefix as for run-all.sh.
set -u
source "$(dirname "$0")/env.sh"
require_bin
require_mathlib
W="${1:?gate work directory required}"
R="${2:?result directory required}"
shift 2
if [ "$#" -eq 0 ]; then
  set -- core crossws f15 f16 diagmap $(seq -f 'M%02g' 1 18)
fi
mkdir -p "$R"
sysroot="${PARALEAN_SYSROOT:-$(lean --print-prefix)}"
snapshot="${PARALEAN_LIB%/.lake/build/lib/lean}"
test_file="$P1_DIR/tests/VerifyExistingExport.lean"
sha256sum "$snapshot/Paralean/Export.lean" "$snapshot/Paralean/Replay.lean" \
  "$snapshot/.lake/build/lib/lean/Paralean/Export.olean" \
  "$PARALEAN_BIN" "$test_file" "$P1_DIR/scripts/hash-export-artifacts.py" \
  > "$R/source-hashes.txt" || exit 2
python3 "$P1_DIR/scripts/hash-export-artifacts.py" "$W" > "$R/artifacts-before.tsv" || exit 2
ml_path="$(mathlib_lean_path)" || exit 2
printf 'set\texit\tverified\tdenominator\teffect_only\n' > "$R/status.tsv"
for label in "$@"; do
  case "$label" in
    M[0-9][0-9]) base="$W/mathlib/$label"; lp="$PARALEAN_LIB:$ml_path" ;;
    core|crossws|f15|f16|diagmap) base="$W/$label"; lp="$PARALEAN_LIB" ;;
    *) echo "unknown set: $label" >&2; exit 2 ;;
  esac
  case "$label" in f16) lp="$PARALEAN_LIB:$ml_path" ;; esac
  [ -d "$base/store/files" ] && [ -d "$base/export/.lake/build/lib/lean" ] || {
    echo "missing built package: $base" >&2; exit 2;
  }
  env -u PARALEAN_STORE LEAN_PATH="$lp" lean --run "$test_file" \
    "$base/store" "$base/export" "$PARALEAN_LIB" "$sysroot" \
    > "$R/$label.log" 2>&1
  rc=$?
  read -r verified denominator effect_only < <(python3 - "$R/$label.log" <<'PY'
import re, sys
s = open(sys.argv[1]).read()
m = re.search(r'^verify: (\d+)/(\d+) declaration groups identical in the stock-built oleans; (\d+) effect-only', s, re.M)
print(*m.groups() if m else ('-', '-', '-'))
PY
  )
  printf '%s\t%s\t%s\t%s\t%s\n' "$label" "$rc" "$verified" "$denominator" "$effect_only" >> "$R/status.tsv"
  if [ "$rc" -gt 1 ] || [ "$verified" = - ]; then
    echo "verification did not complete for $label (exit $rc)" >&2
    exit 2
  fi
done
python3 "$P1_DIR/scripts/hash-export-artifacts.py" "$W" > "$R/artifacts-after.tsv" || exit 2
if ! cmp -s "$R/artifacts-before.tsv" "$R/artifacts-after.tsv"; then
  echo 'export artifacts changed during read-only verification' >&2
  exit 2
fi
sha256sum "$R/artifacts-before.tsv" "$R/artifacts-after.tsv" > "$R/artifact-manifest-hashes.txt"
cat "$R/status.tsv"
