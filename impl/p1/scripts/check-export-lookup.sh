#!/usr/bin/env bash
# Check raw-hygiene F13 lookup and one-to-one assignment against a captured
# store and its stock-built exported module.
set -euo pipefail
source "$(dirname "$0")/env.sh"
if [[ $# != 2 ]]; then
  echo "usage: $0 F13_STORE F13_EXPORTED_OLEAN" >&2
  exit 2
fi
store_dir="$(realpath "$1")"
olean_path="$(realpath "$2")"
require_toolchain
cd "$P1_DIR"
dependency_path="$(lake env printenv LEAN_PATH)"
lean_binary="$(lake env which lean)"
LEAN_PATH="$PARALEAN_LIB:$dependency_path" "$lean_binary" --run \
  "$P1_DIR/tests/ExportLookup.lean" "$store_dir" "$olean_path"
