#!/usr/bin/env bash
# Positive TLC scenarios. Each run checks copies of the sources in
# .runs/tla/run/<scenario>/ and appends the hashes of exactly the files TLC
# parsed (and the config) to its log. With arguments, only the named
# scenarios run and no manifest is written, so the results cannot be archived.
set -euo pipefail
cd "$(dirname "$0")/.."
root="$PWD"
# shellcheck source=scripts/tla-common.sh
source scripts/tla-common.sh
mkdir -p .runs/tla
workers="${TLC_WORKERS:-8}"
heap="${TLC_HEAP:-12g}"

selected=()
if [[ $# == 0 ]]; then
  selected=("${TLA_SCENARIOS[@]}")
  rm -f .runs/tla/MANIFEST
else
  for want in "$@"; do
    found=
    for entry in "${TLA_SCENARIOS[@]}"; do
      [[ $(scenario_name "$entry") == "$want" ]] && { selected+=("$entry"); found=1; }
    done
    [[ -n $found ]] || { echo "Unknown scenario: $want" >&2; exit 2; }
  done
fi

for entry in "${selected[@]}"; do
  scenario="$(scenario_name "$entry")"
  module="$(scenario_module "$entry")"
  dir="$root/.runs/tla/run/$scenario"
  echo "Checking $scenario ($module.tla)"
  stage_sources "$dir"
  status=0
  java -XX:+UseParallelGC -Xmx"$heap" -cp "$root/.deps/tla2tools.jar" tlc2.TLC \
    -workers "$workers" -metadir "$dir/states" \
    -config "$dir/$scenario.cfg" "$dir/$module.tla" \
    > "$dir/result.log" 2>&1 || status=$?
  rm -rf "$dir/states"
  if [[ $status != 0 ]] ||
     ! grep -Fq 'Model checking completed. No error has been found.' "$dir/result.log"; then
    tail -40 "$dir/result.log"
    echo "TLC failed: $scenario (exit $status)" >&2
    exit 1
  fi
  record_provenance "$dir" "$module" "$scenario" "$dir/result.log" pass
  cp "$dir/result.log" "$root/.runs/tla/$scenario.log"
  grep -E 'distinct states found|Finished in' "$dir/result.log" | tail -2
done

if [[ $# == 0 ]]; then
  for entry in "${TLA_SCENARIOS[@]}"; do scenario_name "$entry"; done > .runs/tla/MANIFEST
fi
