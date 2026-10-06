#!/usr/bin/env bash
# Positive TLC scenarios. Each run checks copies of the sources in
# .runs/tla/run/<scenario>/ and appends the hashes of exactly the files TLC
# parsed (and the config) to its log.
#
#   bash scripts/check-tla.sh            # default suite; writes .runs/tla/MANIFEST
#   bash scripts/check-tla.sh --wide     # larger scopes; writes .runs/tla/wide/MANIFEST
#   bash scripts/check-tla.sh a b ...    # only these scenarios; no manifest
#
# Without a manifest the results cannot be archived.
set -euo pipefail
cd "$(dirname "$0")/.."
root="$PWD"
# shellcheck source=scripts/tla-common.sh
source scripts/tla-common.sh
mkdir -p .runs/tla/wide
workers="${TLC_WORKERS:-8}"
heap="${TLC_HEAP:-12g}"

is_wide() {
  local entry
  for entry in "${TLA_WIDE_SCENARIOS[@]}"; do
    [[ $(scenario_name "$entry") == "$1" ]] && return 0
  done
  return 1
}

selected=()
manifest=
if [[ $# == 0 ]]; then
  selected=("${TLA_SCENARIOS[@]}")
  manifest=.runs/tla/MANIFEST
elif [[ $# == 1 && $1 == --wide ]]; then
  selected=("${TLA_WIDE_SCENARIOS[@]}")
  manifest=.runs/tla/wide/MANIFEST
else
  for want in "$@"; do
    found=
    for entry in "${TLA_SCENARIOS[@]}" "${TLA_WIDE_SCENARIOS[@]}"; do
      [[ $(scenario_name "$entry") == "$want" ]] && { selected+=("$entry"); found=1; }
    done
    [[ -n $found ]] || { echo "Unknown scenario: $want" >&2; exit 2; }
  done
fi
[[ -z $manifest ]] || rm -f "$manifest"

for entry in "${selected[@]}"; do
  scenario="$(scenario_name "$entry")"
  module="$(scenario_module "$entry")"
  dir="$root/.runs/tla/run/$scenario"
  if is_wide "$scenario"; then logdir="$root/.runs/tla/wide"; else logdir="$root/.runs/tla"; fi
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
  cp "$dir/result.log" "$logdir/$scenario.log"
  grep -E 'distinct states found|Finished in' "$dir/result.log" | tail -2
done

if [[ -n $manifest ]]; then
  for entry in "${selected[@]}"; do scenario_name "$entry"; done > "$manifest"
fi
