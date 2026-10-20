#!/usr/bin/env bash
# Build an intentionally ambiguous stock .olean and require exporter lookup to
# reject two candidate constants with the same raw hygiene key.
set -euo pipefail
source "$(dirname "$0")/env.sh"
require_toolchain
work="${1:-$PARALEAN_RUNS/export-lookup-ambiguous}"
mkdir -p "$work"
work="$(realpath "$work")"
cd "$P1_DIR"
dependency_path="$(lake env printenv LEAN_PATH)"
lean_binary="$(lake env which lean)"
"$lean_binary" -R "$P1_DIR/tests" -o "$work/ExportLookupAmbiguous.olean" \
  "$P1_DIR/tests/ExportLookupAmbiguous.lean"
LEAN_PATH="$PARALEAN_LIB:$dependency_path" "$lean_binary" --run \
  "$P1_DIR/tests/ExportLookupAmbiguousCheck.lean" "$work/ExportLookupAmbiguous.olean"
