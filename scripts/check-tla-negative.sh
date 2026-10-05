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

for item in 'work Chain NeverChainCommitted' 'dependent_work Chain NeverDependentPublished' 'collision Collision NeverCollided' 'durable Quorums NeverAcked' 'loss Quorums NeverLost' 'integrated_work Integrated NeverCommitted' 'checkpoint_reuse CheckpointReuse NeverReusedAfterLoss' 'export_rejection_work ExportRejected NeverPublished' 'receipt_work Receipts NeverValidPublished' 'receipt_dependent_work Receipts NeverDependentPublished' 'target_alternatives Targets NeverAlternativeCommitted' 'target_handover Targets NeverHandover' 'workspace_concurrent_converged Workspace NeverConcurrentConverged' 'workspace_collision_resolved Workspace NeverCollisionResolved' 'workspace_winner_revised Workspace NeverWinnerRevised' 'workspace_deleted Workspace NeverDeleted'; do
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

# Hardening guards. Each removal must produce its named counterexample.
prepare_case unreceipted_publication
edit_once .runs/tla/negative/unreceipted_publication/Receipts.tla '  /\ g \in held[w]' '  /\ TRUE'
edit_once .runs/tla/negative/unreceipted_publication/Receipts.cfg 'PublishedValid PublishedReceipted DepsClosed' 'PublishedValid DepsClosed'
edit_once .runs/tla/negative/unreceipted_publication/Receipts.cfg 'INVARIANTS StagedReceipted StagedValid' ''
run_expected_failure unreceipted_publication Receipts 'Invariant PublishedValid is violated'

prepare_case unreceipted_staging
edit_once .runs/tla/negative/unreceipted_staging/Receipts.tla '  /\ g \in held[w]' '  /\ TRUE'
edit_once .runs/tla/negative/unreceipted_staging/Receipts.cfg 'INVARIANTS StagedReceipted StagedValid' 'INVARIANTS StagedValid'
run_expected_failure unreceipted_staging Receipts 'Invariant StagedValid is violated'

prepare_case target_no_owner_check
edit_once .runs/tla/negative/target_no_owner_check/Targets.tla 'OwnerOK(w) == w = owner' 'OwnerOK(w) == TRUE'
run_expected_failure target_no_owner_check Targets 'Invariant TargetChain is violated'

prepare_case target_no_revise_head
edit_once .runs/tla/negative/target_no_revise_head/Targets.tla 'RevisesHead(R) == recHead = None \/ recHead \in R' 'RevisesHead(R) == TRUE'
run_expected_failure target_no_revise_head Targets 'Invariant TargetChain is violated'

# Reading a publication scan instead of the head record: any subset of the
# published set (a certificate scan only guarantees CertQuorum <= S <= published).
prepare_case target_scan_subset
edit_once .runs/tla/negative/target_scan_subset/Targets.tla 'RevisesHead(R) == recHead = None \/ recHead \in R' 'RevisesHead(R) == \E S \in SUBSET published : S \subseteq R'
run_expected_failure target_scan_subset Targets 'Invariant TargetChain is violated'

prepare_case target_no_head_update
edit_once .runs/tla/negative/target_no_head_update/Targets.tla 'HeadUpdate(p) == p' 'HeadUpdate(p) == recHead'
edit_once .runs/tla/negative/target_no_head_update/Targets.cfg 'INVARIANTS TypeOK TargetChain HeadUnique RecordTopsChain' 'INVARIANTS TypeOK TargetChain HeadUnique'
run_expected_failure target_no_head_update Targets 'Invariant TargetChain is violated'

prepare_case target_no_single_pending
edit_once .runs/tla/negative/target_no_single_pending/Targets.tla 'NoOtherPending(w) == pending[w] = {}' 'NoOtherPending(w) == TRUE'
run_expected_failure target_no_single_pending Targets 'Invariant TargetChain is violated'

prepare_case target_no_epoch_fence
edit_once .runs/tla/negative/target_no_epoch_fence/Targets.tla 'EpochOK(w, p) == prepEpoch[w][p] = epoch' 'EpochOK(w, p) == TRUE'
run_expected_failure target_no_epoch_fence Targets 'Invariant TargetChain is violated'

prepare_case fencing_unfenced_put
edit_once .runs/tla/negative/fencing_unfenced_put/Fencing.tla 'FenceOK(w) == holds[w] = fence' 'FenceOK(w) == TRUE'
run_expected_failure fencing_unfenced_put Fencing 'Invariant StaleNeverStored is violated'

# The commit certificate is the fenced write; without its check an old writer
# commits after rotation.
prepare_case fencing_unfenced_commit
edit_once .runs/tla/negative/fencing_unfenced_commit/Fencing.tla 'CertFenceOK(w) == fence = holds[w]' 'CertFenceOK(w) == TRUE'
run_expected_failure fencing_unfenced_commit Fencing 'Invariant CertFenced is violated'

prepare_case fencing_unfenced_commit_selected
edit_once .runs/tla/negative/fencing_unfenced_commit_selected/Fencing.tla 'CertFenceOK(w) == fence = holds[w]' 'CertFenceOK(w) == TRUE'
edit_once .runs/tla/negative/fencing_unfenced_commit_selected/Fencing.cfg 'INVARIANTS TypeOK StaleNeverStored CertFenced KnownFenced SelectedFenced NoLateAckedKnown ScanFindsCertified' 'INVARIANTS TypeOK SelectedFenced'
run_expected_failure fencing_unfenced_commit_selected Fencing 'Invariant SelectedFenced is violated'

# Adoption on physical byte quorums (the old Scan) instead of certificates
# adopts a late-acknowledged stale record.
prepare_case fencing_stale_selected
edit_once .runs/tla/negative/fencing_stale_selected/Fencing.tla '           ready == {c \in found : CertDurable(c)}' '           ready == {c \in found : OnLiveQuorum(c)}'
edit_once .runs/tla/negative/fencing_stale_selected/Fencing.cfg 'INVARIANTS TypeOK StaleNeverStored CertFenced KnownFenced SelectedFenced NoLateAckedKnown ScanFindsCertified' 'INVARIANTS TypeOK NoLateAckedKnown'
run_expected_failure fencing_stale_selected Fencing 'Invariant NoLateAckedKnown is violated'

prepare_case fencing_recovery_witness
printf '%s\n' 'INVARIANT NeverRecoveredAfterRotation' >> .runs/tla/negative/fencing_recovery_witness/Fencing.cfg
run_expected_failure fencing_recovery_witness Fencing 'Invariant NeverRecoveredAfterRotation is violated'

prepare_case fencing_reacquire_witness
printf '%s\n' 'INVARIANT NeverReacquiredRecovered' >> .runs/tla/negative/fencing_reacquire_witness/Fencing.cfg
run_expected_failure fencing_reacquire_witness Fencing 'Invariant NeverReacquiredRecovered is violated'

# A commit certificate written before the writer's Ack can outlive the bytes.
prepare_case fencing_cert_unacked
edit_once .runs/tla/negative/fencing_cert_unacked/Fencing.tla '    /\ c \in acked' '    /\ TRUE'
run_expected_failure fencing_cert_unacked Fencing 'Invariant ScanFindsCertified is violated'

prepare_case fencing_repair_disguised
edit_once .runs/tla/negative/fencing_repair_disguised/Fencing.tla '    /\ src \in live /\ c \in stored[src]   \* repair copies existing bytes' '    /\ TRUE'
run_expected_failure fencing_repair_disguised Fencing 'Invariant StaleNeverStored is violated'

prepare_case fencing_late_ack_witness
printf '%s\n' 'INVARIANT NeverLateAck' >> .runs/tla/negative/fencing_late_ack_witness/Fencing.cfg
run_expected_failure fencing_late_ack_witness Fencing 'Invariant NeverLateAck is violated'

prepare_case fencing_late_repair_witness
printf '%s\n' 'INVARIANT NeverLateRepair' >> .runs/tla/negative/fencing_late_repair_witness/Fencing.cfg
run_expected_failure fencing_late_repair_witness Fencing 'Invariant NeverLateRepair is violated'

prepare_case cert_scan_raw_marker
edit_once .runs/tla/negative/cert_scan_raw_marker/Certificates.tla '                        /\ \E r \in q : g \in cert[r]' '                        /\ \E r \in q : g \in marker[r]'
run_expected_failure cert_scan_raw_marker Certificates 'Invariant ReceivedPublished is violated'

prepare_case cert_commit_unguarded
edit_once .runs/tla/negative/cert_commit_unguarded/Certificates.tla '                /\ \A g \in S : CertQuorumBy(n, g)' '                /\ TRUE'
edit_once .runs/tla/negative/cert_commit_unguarded/Certificates.cfg ' CheckpointCertified CheckpointDiscoverable' ' CheckpointDiscoverable'
run_expected_failure cert_commit_unguarded Certificates 'Invariant CheckpointDiscoverable is violated'

prepare_case cert_put_unknown
edit_once .runs/tla/negative/cert_put_unknown/Certificates.tla '                    /\ g \in known[n]' '                    /\ TRUE'
run_expected_failure cert_put_unknown Certificates 'Invariant CertSound is violated'

prepare_case cert_rediscovery_work
printf '%s\n' 'INVARIANT NeverRediscoveredAfterLoss' >> .runs/tla/negative/cert_rediscovery_work/Certificates.cfg
run_expected_failure cert_rediscovery_work Certificates 'Invariant NeverRediscoveredAfterLoss is violated'

prepare_case cert_lost_replier_work
printf '%s\n' 'PROPERTY NeverCommitWithLostReplier' >> .runs/tla/negative/cert_lost_replier_work/Certificates.cfg
run_expected_failure cert_lost_replier_work Certificates 'Action property NeverCommitWithLostReplier is violated'

prepare_case workspace_arrival_order
edit_once .runs/tla/negative/workspace_arrival_order/Workspace.tla "    /\\ doc' = [doc EXCEPT ![x][File[d]] = Render(known'[x], File[d])]" "    /\\ doc' = [doc EXCEPT ![x][File[d]] = Append(doc[x][File[d]], d)]"
run_expected_failure workspace_arrival_order Workspace 'Invariant SameKnownSameRender is violated'

prepare_case workspace_first_seen_winner
edit_once .runs/tla/negative/workspace_first_seen_winner/Workspace.tla 'Winner(x, K, n) == LinMin(Heads(K, n))' 'Winner(x, K, n) == IF firstSeen[x][n] \in Heads(K, n) THEN firstSeen[x][n] ELSE LinMin(Heads(K, n))'
run_expected_failure workspace_first_seen_winner Workspace 'Invariant SameKnownSameRender is violated'

prepare_case workspace_counter_clock
edit_once .runs/tla/negative/workspace_counter_clock/Workspace.tla 'Clock(x) == 1 + KnownMax(known[x])' 'Clock(x) == 1 + Cardinality({d \in known[x] : Author[d] = x})'
run_expected_failure workspace_counter_clock Workspace 'Action property IntentionPreserved is violated'

prepare_case workspace_own_key_winner
edit_once .runs/tla/negative/workspace_own_key_winner/Workspace.tla 'Winner(x, K, n) == LinMin(Heads(K, n))' 'Winner(x, K, n) == Oldest(Heads(K, n))'
run_expected_failure workspace_own_key_winner Workspace 'Action property WinnerLineageKeepsName is violated'

prepare_case workspace_render_superseded
edit_once .runs/tla/negative/workspace_render_superseded/Workspace.tla 'LiveIn(K, f) == {d \in K : File[d] = f /\ Live(K, d)}' 'LiveIn(K, f) == {d \in K : File[d] = f}'
run_expected_failure workspace_render_superseded Workspace 'Invariant NoSupersededRendered is violated'

# A partial revision (a3 revises a1 for foo only) retires a1 for bar as well.
prepare_case workspace_partial_revision_witness
printf '%s\n' 'INVARIANT NeverPartialRevisionFreed' >> .runs/tla/negative/workspace_partial_revision_witness/Workspace.cfg
run_expected_failure workspace_partial_revision_witness Workspace 'Invariant NeverPartialRevisionFreed is violated'

prepare_case workspace_superseded_holds_name
edit_once .runs/tla/negative/workspace_superseded_holds_name/Workspace.tla 'Heads(K, n) == {d \in K : n \in NameSet(d) /\ Live(K, d)}' 'Heads(K, n) == {d \in K : n \in NameSet(d) /\ ~Tomb[d] /\ ~\E e \in K : d \in Anc(e) /\ Name[e] = n}'
run_expected_failure workspace_superseded_holds_name Workspace 'Invariant NameHeld is violated'

# Redundant checks and the independent failure oracle for each effective guard
# are documented in verification/TLA-GUARDS.md.
