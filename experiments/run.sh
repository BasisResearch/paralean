#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")/.."

paralean_lean=${1:-lean}
paralean_sysroot=$("$paralean_lean" --print-prefix)
"$paralean_lean" --version
env -u LEAN_PATH -u LEAN_SYSROOT "$paralean_lean" --run experiments/KernelBoundary.lean "$paralean_sysroot"
env -u LEAN_PATH -u LEAN_SYSROOT "$paralean_lean" --run experiments/ProofGraph.lean
