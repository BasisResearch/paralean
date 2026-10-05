#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
root="$PWD"
mkdir -p .runs/tla
workers="${TLC_WORKERS:-8}"
for model in "${@:-Chain Collision Revision Revert Rejected Quorums Integrated CheckpointReuse ExportRejected Receipts Targets Fencing Certificates Workspace}"; do
  for scenario in $model; do
    echo "Checking $scenario"
    java -Xmx12g -cp "$root/.deps/tla2tools.jar" tlc2.TLC \
      -workers "$workers" -metadir "$root/.runs/tla/states-$scenario" \
      -config "$root/verification/tla/$scenario.cfg" \
      "$root/verification/tla/$scenario.tla" \
      > "$root/.runs/tla/$scenario.log" 2>&1
    tail -8 "$root/.runs/tla/$scenario.log"
  done
done
