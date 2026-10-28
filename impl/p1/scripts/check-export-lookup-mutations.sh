#!/usr/bin/env bash
# Compile private copies of Export.lean with each new lookup guard removed.
# Each mutant must fail the corresponding executable .olean test.
set -euo pipefail
source "$(dirname "$0")/env.sh"
if [[ $# != 2 && $# != 3 ]]; then
  echo "usage: $0 F13_STORE F13_EXPORTED_OLEAN [WORKDIR]" >&2
  exit 2
fi
store_dir="$(realpath "$1")"
f13_olean="$(realpath "$2")"
work="${3:-$PARALEAN_RUNS/export-lookup-mutations}"
mkdir -p "$work"
work="$(realpath "$work")"
require_toolchain
cd "$P1_DIR"
dependency_path="$(lake env printenv LEAN_PATH)"
lean_binary="$(lake env which lean)"

"$lean_binary" -R "$P1_DIR/tests" -o "$work/ExportLookupAmbiguous.olean" \
  "$P1_DIR/tests/ExportLookupAmbiguous.lean" > "$work/fixture.log" 2>&1
LEAN_PATH="$PARALEAN_LIB:$dependency_path" "$lean_binary" --run \
  "$P1_DIR/tests/ExportLookup.lean" "$store_dir" "$f13_olean" \
  > "$work/baseline-f13.log" 2>&1
LEAN_PATH="$PARALEAN_LIB:$dependency_path" "$lean_binary" --run \
  "$P1_DIR/tests/ExportLookupAmbiguousCheck.lean" "$work/ExportLookupAmbiguous.olean" \
  > "$work/baseline-ambiguous.log" 2>&1

prepare_mutant() {
  local label="$1" old="$2" replacement="$3"
  local mutant="$work/$label"
  mkdir -p "$mutant/Paralean"
  cp "$P1_DIR/Paralean/Export.lean" "$mutant/Paralean/Export.lean"
  python3 - "$mutant/Paralean/Export.lean" "$old" "$replacement" "$PARALEAN_LIB/Paralean" <<'PY'
from pathlib import Path
import sys
target, old, new, libdir = sys.argv[1:]
p = Path(target)
s = p.read_text()
if s.count(old) != 1:
    raise SystemExit(f"expected exactly one mutation site: {old!r}")
p.write_text(s.replace(old, new))
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
  LEAN_PATH="$mutant:$PARALEAN_LIB:$dependency_path" "$lean_binary" \
    -R "$mutant" -o "$mutant/Paralean/Export.olean" \
    "$mutant/Paralean/Export.lean" > "$work/$label-build.log" 2>&1
}

expect_failure() {
  local label="$1" testfile="$2" expected="$3" testarg="$4"
  local mutant="$work/$label" log="$work/$label-test.log"
  if LEAN_PATH="$mutant:$PARALEAN_LIB:$dependency_path" "$lean_binary" --run \
      "$P1_DIR/tests/$testfile" "$testarg" ${5:+"$5"} > "$log" 2>&1; then
    cat "$log" >&2
    echo "$label mutant unexpectedly passed" >&2
    exit 1
  fi
  if ! grep -Fq "$expected" "$log"; then
    cat "$log" >&2
    echo "$label mutant failed for an unexpected reason" >&2
    exit 1
  fi
  echo "$label: expected runtime test failure"
}

prepare_mutant no-reuse 'if used.contains n then' 'if false then'
expect_failure no-reuse ExportLookup.lean 'duplicate captured group not rejected' \
  "$store_dir" "$f13_olean"
prepare_mutant no-singleton 'if q.size == 1 then q[0]?' \
  'if !q.isEmpty then q[0]?'
expect_failure no-singleton ExportLookupAmbiguousCheck.lean \
  'ambiguous hygiene key was not rejected' "$work/ExportLookupAmbiguous.olean"

sha256sum "$P1_DIR/Paralean/Export.lean" "$P1_DIR/tests/ExportLookup.lean" \
  "$P1_DIR/tests/ExportLookupAmbiguous.lean" \
  "$P1_DIR/tests/ExportLookupAmbiguousCheck.lean" \
  "$work"/*.log > "$work/MANIFEST.sha256"
echo "PASS: baseline lookups and both source-removal mutations"
