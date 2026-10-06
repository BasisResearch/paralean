#!/usr/bin/env bash
# Run the P2 test suite against the cluster started by up.sh. Extra arguments go to
# `cargo test` (e.g. `scripts/test.sh --test fixtures`).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
cd "$here/.."
exec cargo test --workspace "$@"
