#!/usr/bin/env bash
# Compile private Export.lean copies with each residual lookup guard removed.
# Use PARALEAN_LIB to select the library under test; production files stay intact.
set -euo pipefail
source "$(dirname "$0")/env.sh"
require_toolchain
work="${1:-$PARALEAN_RUNS/export-lookup-residual-mutations}"
mkdir -p "$work"
work="$(realpath "$work")"
source_dir="${PARALEAN_LIB%/.lake/build/lib/lean}"
test_file="$P1_DIR/tests/ExportLookupResidualCheck.lean"
fixture="$work/ExportLookupResidualFixture.olean"
lean_binary="$(command -v lean)"

"$lean_binary" -R "$P1_DIR/tests" -o "$fixture" \
  "$P1_DIR/tests/ExportLookupResidualFixture.lean" > "$work/fixture-build.log" 2>&1
LEAN_PATH="$PARALEAN_LIB${LEAN_PATH:+:$LEAN_PATH}" "$lean_binary" --run \
  "$test_file" "$fixture" > "$work/baseline.log" 2>&1

prepare_mutant() {
  local label="$1" old="$2" replacement="$3"
  local mutant="$work/$label"
  mkdir -p "$mutant/Paralean"
  cp "$source_dir/Paralean/Export.lean" "$mutant/Paralean/Export.lean"
  python3 - "$mutant/Paralean/Export.lean" "$old" "$replacement" "$PARALEAN_LIB/Paralean" <<'PY'
from pathlib import Path
import sys
target, old, replacement, libdir = sys.argv[1:]
p = Path(target)
s = p.read_text()
if s.count(old) != 1:
    raise SystemExit(f"expected exactly one mutation site: {old!r}")
p.write_text(s.replace(old, replacement))
for source in Path(libdir).iterdir():
    if source.name.startswith("Export."):
        continue
    link = p.parent / source.name
    if link.is_symlink():
        link.unlink()
    elif link.exists():
        raise SystemExit(f"refusing unexpected mutant artifact: {link}")
    link.symlink_to(source.resolve())
PY
  LEAN_PATH="$mutant:$PARALEAN_LIB${LEAN_PATH:+:$LEAN_PATH}" "$lean_binary" \
    -R "$mutant" -o "$mutant/Paralean/Export.olean" \
    "$mutant/Paralean/Export.lean" > "$work/$label-build.log" 2>&1
}

expect_failure() {
  local label="$1" expected="$2"
  local mutant="$work/$label"
  if LEAN_PATH="$mutant:$PARALEAN_LIB${LEAN_PATH:+:$LEAN_PATH}" "$lean_binary" --run \
      "$test_file" "$fixture" > "$work/$label-test.log" 2>&1; then
    cat "$work/$label-test.log" >&2
    echo "$label mutant unexpectedly passed" >&2
    exit 1
  fi
  if ! grep -Fq "$expected" "$work/$label-test.log"; then
    cat "$work/$label-test.log" >&2
    echo "$label mutant failed for an unexpected reason" >&2
    exit 1
  fi
  echo "$label: expected runtime test failure"
}

prepare_mutant no-exact-reservation \
  '(fun n => !exactClaimed.contains n)' '(fun _ => true)'
expect_failure no-exact-reservation 'F10-like scope drift was not uniquely associated'
prepare_mutant no-capture-uniqueness \
  'if residualCount.getD stem 0 != 1 then none' 'if false then none'
expect_failure no-capture-uniqueness 'twoA incorrectly claimed an exported candidate'
prepare_mutant no-candidate-uniqueness \
  'if unused.size == 1 then unused[0]? else none' \
  'if !unused.isEmpty then unused[0]? else none'
expect_failure no-candidate-uniqueness 'multi incorrectly claimed an exported candidate'
prepare_mutant no-fullkey-guard \
  'else if q.isEmpty then' 'else if true then'
expect_failure no-fullkey-guard 'residual of ambiguous owner did not match the third candidate'

sha256sum "$source_dir/Paralean/Export.lean" \
  "$P1_DIR/tests/ExportLookupResidualFixture.lean" "$test_file" \
  "$work"/*.log > "$work/MANIFEST.sha256"
echo "PASS: baseline residual lookup and four source-removal mutations"
