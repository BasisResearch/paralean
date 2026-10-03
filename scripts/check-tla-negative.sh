#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
root="$PWD"
mkdir -p .runs/tla/negative

run_expected_failure() {
  local label="$1" model="$2" expected="$3"
  local dir="$root/.runs/tla/negative/$label"
  set +e
  java -Xmx4g -cp "$root/.deps/tla2tools.jar" tlc2.TLC \
    -workers 1 -metadir "$dir/states" -config "$dir/$model.cfg" \
    "$dir/$model.tla" > "$dir/result.log" 2>&1
  local code=$?
  set -e
  if [[ $code == 0 ]] || ! grep -q "$expected" "$dir/result.log"; then
    cat "$dir/result.log"
    echo "Expected counterexample missing: $label (exit $code)" >&2
    exit 1
  fi
  echo "$label: expected counterexample found"
}

prepare_case() {
  mkdir -p ".runs/tla/negative/$1"
  cp verification/tla/*.tla verification/tla/*.cfg ".runs/tla/negative/$1/"
}

for item in 'work Chain NeverCommitted' 'collision Collision NeverCollided' 'durable Quorums NeverAcked' 'loss Quorums NeverLost' 'integrated_work Integrated NeverCommitted'; do
  read -r label model invariant <<< "$item"
  prepare_case "$label"
  # Remove temporal properties for finite reachability witnesses.
  sed -i '/^PROPERTIES /d;s/SPECIFICATION FairSpec/SPECIFICATION Spec/' ".runs/tla/negative/$label/$model.cfg"
  echo "INVARIANT $invariant" >> ".runs/tla/negative/$label/$model.cfg"
  run_expected_failure "$label" "$model" "Invariant $invariant is violated"
done

prepare_case unchecked
sed -i '/    \/\\ d \\in Valid/d' .runs/tla/negative/unchecked/Registry.tla
run_expected_failure unchecked Rejected 'Invariant AdmissionSafety is violated'

prepare_case premature_ack
sed -i '/             \/\\ \\A r \\in w : o \\in stored\[r\]/d' .runs/tla/negative/premature_ack/Durability.tla
run_expected_failure premature_ack Quorums 'Invariant WitnessSurvives is violated'

prepare_case no_fair_recovery
sed -i 's/Spec \/\\ WF_vars(Heal)/Spec/' .runs/tla/negative/no_fair_recovery/Registry.tla
run_expected_failure no_fair_recovery Collision 'Temporal properties were violated'

prepare_case unbacked_publication
sed -i 's/Publish(n,d) == \/\\ Payload\[d\] \\in acknowledged/Publish(n,d) == \/\\ TRUE/' .runs/tla/negative/unbacked_publication/Publication.tla
run_expected_failure unbacked_publication Integrated 'Invariant PublicationGuard is violated'

prepare_case unbacked_checkpoint
sed -i 's/Commit(n,S) == \/\\ Manifest\[S\] \\in acknowledged/Commit(n,S) == \/\\ TRUE/' .runs/tla/negative/unbacked_checkpoint/Publication.tla
run_expected_failure unbacked_checkpoint Integrated 'Invariant CheckpointGuard is violated'

prepare_case silent_winner
# Replace the set of causal heads by an arbitrary singleton. Convergence alone
# still holds; eventual collision detection must reject this mutation.
sed -i 's/^Heads(K, name) ==/RawHeads(K, name) ==/' .runs/tla/negative/silent_winner/Registry.tla
sed -i '/^Conflict(K, name)/i Heads(K, name) == IF RawHeads(K,name) = {} THEN {} ELSE {CHOOSE d \\in RawHeads(K,name) : TRUE}' .runs/tla/negative/silent_winner/Registry.tla
run_expected_failure silent_winner Collision 'Temporal properties were violated'
