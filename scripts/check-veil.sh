#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
root="$PWD"
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p .runs/veil/Paralean
expected=d05518f22076b8cc84fb2d2b74d196aa979bfe8f
[[ "$(git -C .deps/veil rev-parse HEAD)" == "$expected" ]]
git -C .deps/veil diff --quiet
git -C .deps/veil diff --cached --quiet
export LEAN_PATH="$root/.runs/veil${LEAN_PATH:+:$LEAN_PATH}"
cd .deps/veil
for module in Registry Durability Convergence Composition EndToEnd; do
  echo "Checking $module"
  lake env lean -R "$root/verification/veil" -o "$root/.runs/veil/Paralean/$module.olean" \
    "$root/verification/veil/Paralean/$module.lean" \
    > "$root/.runs/veil/$module.log" 2>&1
  cat "$root/.runs/veil/$module.log"
done
lake env lean -R "$root/verification/veil" -o "$root/.runs/veil/Paralean.olean" \
  "$root/verification/veil/Paralean.lean"
lake env lean -R "$root/verification/veil" "$root/verification/veil/Audit.lean" \
  > "$root/.runs/veil/Audit.log" 2>&1
cat "$root/.runs/veil/Audit.log"
