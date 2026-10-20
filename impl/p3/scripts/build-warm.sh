#!/usr/bin/env bash
# Build the warm checker with the same Lean toolchain as P1.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
require_toolchain
cd "$PARALEAN_P3_ROOT/lean"
lake build
echo "Set PARALEAN_P3_WARM_BIN=$PARALEAN_P3_ROOT/lean/.lake/build/bin/paralean-warm before generating checker pins."
