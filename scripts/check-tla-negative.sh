#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
root="$PWD"
mkdir -p .runs/tla/negative

# Literal edits are portable across macOS and Linux. An exact match count also
# prevents a changed source file from silently defeating a mutation.
edit_once() {
  python3 - "$1" "$2" "$3" <<'PY'
from pathlib import Path
import sys
path, old, new = sys.argv[1:]
p = Path(path)
text = p.read_text()
if text.count(old) != 1:
    raise SystemExit(f"Expected exactly one mutation site in {path}: {old!r}")
p.write_text(text.replace(old, new))
PY
}

finite_witness_config() {
  local file="$1" invariant="$2"
  python3 - "$file" "$invariant" <<'PY'
from pathlib import Path
import sys
p = Path(sys.argv[1])
lines = [line.replace('SPECIFICATION FairSpec', 'SPECIFICATION Spec')
         for line in p.read_text().splitlines()
         if not line.startswith('PROPERTIES ')]
lines.append('INVARIANT ' + sys.argv[2])
p.write_text('\n'.join(lines) + '\n')
PY
}

run_tlc() {
  local label="$1" model="$2"
  local dir="$root/.runs/tla/negative/$label"
  mkdir -p "$dir/states"
  if java -Xmx4g -cp "$root/.deps/tla2tools.jar" tlc2.TLC \
    -workers 1 -metadir "$dir/states" -config "$dir/$model.cfg" \
    "$dir/$model.tla" > "$dir/result.log" 2>&1; then
    tlc_exit=0
  else
    tlc_exit=$?
  fi
}

run_expected_failure() {
  local label="$1" model="$2" expected="$3"
  local dir="$root/.runs/tla/negative/$label"
  run_tlc "$label" "$model"
  if [[ $tlc_exit == 0 ]] || ! grep -Fq "$expected" "$dir/result.log"; then
    cat "$dir/result.log"
    echo "Expected counterexample missing: $label (exit $tlc_exit)" >&2
    exit 1
  fi
  echo "$label: expected counterexample found"
}

run_expected_missing_witness() {
  local label="$1" model="$2"
  local dir="$root/.runs/tla/negative/$label"
  run_tlc "$label" "$model"
  if [[ $tlc_exit != 0 ]] ||
     ! grep -Fq 'Model checking completed. No error has been found.' "$dir/result.log"; then
    cat "$dir/result.log"
    echo "Expected rejection of useful-work coverage missing: $label" >&2
    exit 1
  fi
  # These coverage invariants must FAIL in the ordinary model. Their survival
  # under this mutation establishes that the usual witness gate rejects it.
  echo "$label: expected missing useful-work witness confirmed"
}

prepare_case() {
  mkdir -p ".runs/tla/negative/$1"
  cp verification/tla/*.tla verification/tla/*.cfg ".runs/tla/negative/$1/"
}

for item in 'work Chain NeverChainCommitted' 'dependent_work Chain NeverDependentPublished' 'collision Collision NeverCollided' 'durable Quorums NeverAcked' 'loss Quorums NeverLost' 'integrated_work Integrated NeverCommitted' 'checkpoint_reuse CheckpointReuse NeverReusedAfterLoss' 'export_rejection_work ExportRejected NeverPublished'; do
  read -r label model invariant <<< "$item"
  prepare_case "$label"
  finite_witness_config ".runs/tla/negative/$label/$model.cfg" "$invariant"
  if [[ $model == Chain ]]; then
    edit_once ".runs/tla/negative/$label/$model.cfg" 'SPECIFICATION Spec' 'SPECIFICATION ChainWorkSpec'
  fi
  run_expected_failure "$label" "$model" "Invariant $invariant is violated"
done

prepare_case unchecked
edit_once .runs/tla/negative/unchecked/Registry.tla '    /\ d \in Valid' '    /\ TRUE'
run_expected_failure unchecked Rejected 'Invariant AdmissionSafety is violated'

prepare_case unknown_dependency
edit_once .runs/tla/negative/unknown_dependency/Registry.tla '    /\ Deps[d] \subseteq known[n]' '    /\ TRUE'
run_expected_failure unknown_dependency Rejected 'Invariant AdmissionSafety is violated'

prepare_case unprepared_publication
edit_once .runs/tla/negative/unprepared_publication/Registry.tla '    /\ d \in pending[n]' '    /\ TRUE'
run_expected_failure unprepared_publication Rejected 'Invariant AdmissionSafety is violated'

prepare_case unpublished_receive
edit_once .runs/tla/negative/unpublished_receive/Registry.tla '    /\ d \in published' '    /\ TRUE'
run_expected_failure unpublished_receive Rejected 'Invariant AdmissionSafety is violated'

prepare_case unknown_ancestor
edit_once .runs/tla/negative/unknown_ancestor/Registry.tla '    /\ Ancestors[d] \subseteq known[n]' '    /\ TRUE'
run_expected_failure unknown_ancestor Revision 'Invariant CausalAdmissionSafety is violated'

prepare_case unclosed_ancestors
edit_once .runs/tla/negative/unclosed_ancestors/Registry.tla '    /\ Ancestors[d] \subseteq known[n]' '    /\ TRUE'
edit_once .runs/tla/negative/unclosed_ancestors/Revision.cfg 'CausalAdmissionSafety' 'PublishedAncestorSafety'
run_expected_failure unclosed_ancestors Revision 'Invariant PublishedAncestorSafety is violated'

prepare_case stale_commit
edit_once .runs/tla/negative/stale_commit/Registry.tla '    /\ Current(known[n], S)' '    /\ TRUE'
run_expected_failure stale_commit Revision 'Invariant CommitFreshness is violated'

prepare_case stale_recommit
edit_once .runs/tla/negative/stale_recommit/Registry.tla '    /\ Current(known[n], S)' '    /\ (Current(known[n], S) \/ head[n] = S)'
run_expected_failure stale_recommit Revision 'Invariant CommitFreshness is violated'

prepare_case unbuildable_commit
edit_once .runs/tla/negative/unbuildable_commit/Registry.tla '    /\ Buildable(S)' '    /\ TRUE'
run_expected_failure unbuildable_commit Revision 'Invariant SnapshotSafety is violated'

prepare_case unclosed_snapshot
edit_once .runs/tla/negative/unclosed_snapshot/Registry.tla '                /\ Closed(S)' '                /\ TRUE'
run_expected_failure unclosed_snapshot Revision 'Invariant NoRetargeting is violated'

prepare_case unexportable_snapshot
edit_once .runs/tla/negative/unexportable_snapshot/Registry.tla '                /\ S \in Exportable' '                /\ TRUE'
run_expected_failure unexportable_snapshot ExportRejected 'Invariant NoUnexportableCheckpoint is violated'

prepare_case dependent_work_blocked
edit_once .runs/tla/negative/dependent_work_blocked/Registry.tla '    /\ d \in Valid' '    /\ d \in Valid /\ Deps[d] = {}'
finite_witness_config .runs/tla/negative/dependent_work_blocked/Chain.cfg NeverChainCommitted
printf '%s\n' 'INVARIANT NeverDependentPublished' >> .runs/tla/negative/dependent_work_blocked/Chain.cfg
edit_once .runs/tla/negative/dependent_work_blocked/Chain.cfg 'SPECIFICATION Spec' 'SPECIFICATION ChainWorkSpec'
run_expected_missing_witness dependent_work_blocked Chain

prepare_case checkpoint_loss_blocked
edit_once .runs/tla/negative/checkpoint_loss_blocked/Durability.tla 'Lose(r) == /\ r \in live' 'Lose(r) == /\ r \in live /\ acknowledged = {}'
finite_witness_config .runs/tla/negative/checkpoint_loss_blocked/CheckpointReuse.cfg NeverReusedAfterLoss
run_expected_missing_witness checkpoint_loss_blocked CheckpointReuse

prepare_case premature_ack
edit_once .runs/tla/negative/premature_ack/Durability.tla '             /\ \A r \in w : o \in stored[r]' '             /\ TRUE'
run_expected_failure premature_ack Quorums 'Invariant WitnessSurvives is violated'

prepare_case no_fair_recovery
edit_once .runs/tla/negative/no_fair_recovery/Registry.tla 'Spec /\ WF_vars(Heal)' 'Spec'
run_expected_failure no_fair_recovery Collision 'Temporal properties were violated'

prepare_case no_fair_receive
edit_once .runs/tla/negative/no_fair_receive/Registry.tla '/\ \A n \in Nodes, d \in Decls : WF_vars(Receive(n, d))' '/\ TRUE'
run_expected_failure no_fair_receive Collision 'Temporal properties were violated'

prepare_case unbacked_publication
edit_once .runs/tla/negative/unbacked_publication/Publication.tla 'Publish(n,d) == /\ Payload[d] \in acknowledged' 'Publish(n,d) == /\ TRUE'
run_expected_failure unbacked_publication Integrated 'Invariant PublicationGuard is violated'

prepare_case staged_publication
edit_once .runs/tla/negative/staged_publication/Publication.tla 'Publish(n,d) == /\ Payload[d] \in acknowledged' 'Publish(n,d) == /\ \E r \in live : Payload[d] \in stored[r]'
run_expected_failure staged_publication Integrated 'Invariant PublicationGuard is violated'

prepare_case unbacked_checkpoint
edit_once .runs/tla/negative/unbacked_checkpoint/Publication.tla 'Commit(n,S) == /\ Manifest[S] \in acknowledged' 'Commit(n,S) == /\ TRUE'
run_expected_failure unbacked_checkpoint Integrated 'Invariant CheckpointGuard is violated'

prepare_case silent_winner
# Replace the set of causal heads by an arbitrary singleton. Convergence alone
# still holds; eventual collision detection must reject this mutation.
edit_once .runs/tla/negative/silent_winner/Registry.tla 'Heads(K, name) ==' 'RawHeads(K, name) =='
edit_once .runs/tla/negative/silent_winner/Registry.tla 'Conflict(K, name) ==' 'Heads(K, name) == IF RawHeads(K,name) = {} THEN {} ELSE {CHOOSE d \in RawHeads(K,name) : TRUE}
Conflict(K, name) =='
run_expected_failure silent_winner Collision 'Temporal properties were violated'

# Redundant checks and the independent failure oracle for each effective guard
# are documented in verification/TLA-GUARDS.md.
