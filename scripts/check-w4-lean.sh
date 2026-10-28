#!/usr/bin/env bash
# Check the standalone W4 local transition lemmas with a private output path.
set -euo pipefail
cd "$(dirname "$0")/../verification/veil"
repo_root="$(cd ../.. && pwd)"
mkdir -p "$repo_root/.runs/w4"
lean -R . -o "$repo_root/.runs/w4/ControllerGc.olean" \
  Paralean/ControllerGc.lean
lean --version
echo "ControllerGc: reachability, recovery roots, term fencing and atomic history-compaction lemmas checked"
