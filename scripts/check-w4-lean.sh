#!/usr/bin/env bash
# Check the standalone W4 and W4-rest local transition lemmas with a private
# output path.
set -euo pipefail
cd "$(dirname "$0")/../verification/veil"
repo_root="$(cd ../.. && pwd)"
mkdir -p "$repo_root/.runs/w4"
lean -R . -o "$repo_root/.runs/w4/ControllerGc.olean" \
  Paralean/ControllerGc.lean
lean -R . -o "$repo_root/.runs/w4/StoreGc.olean" \
  Paralean/StoreGc.lean
lean --version
echo "ControllerGc: reachability, recovery roots, term fencing and atomic history-compaction lemmas checked"
echo "StoreGc: doom, guard admission, Garage execution, quiescent Gone and an all-member batch commit preserve named-object safety and LivePresent; references refuse collected states; revival needs the exact Gone; dead records never commit"
