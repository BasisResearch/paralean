#!/usr/bin/env bash
# Negative TLC suite: reachability witnesses, guard mutations and liveness
# counterexamples. A case passes only with its named outcome. Each case runs
# on copies in .runs/tla/negative/<label>/; its log ends with the hashes of the
# pristine sources and of the (possibly mutated) files TLC actually parsed.
#
#   bash scripts/check-tla-negative.sh            # every case; writes MANIFEST
#   bash scripts/check-tla-negative.sh a b ...    # only these labels; no MANIFEST
set -euo pipefail
cd "$(dirname "$0")/.."
root="$PWD"
# shellcheck source=scripts/tla-common.sh
source scripts/tla-common.sh
neg="$root/.runs/tla/negative"
workers="${TLC_NEG_WORKERS:-1}"

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
         if not line.startswith(('PROPERTIES ', 'PROPERTY '))]
lines.append('INVARIANT ' + sys.argv[2])
p.write_text('\n'.join(lines) + '\n')
PY
}

# Check exactly one temporal property, so "Temporal properties were violated"
# names it unambiguously.
single_property() {
  local file="$1" property="$2"
  python3 - "$file" "$property" <<'PY'
from pathlib import Path
import sys
p = Path(sys.argv[1])
lines = [line for line in p.read_text().splitlines()
         if not line.startswith(('PROPERTIES ', 'PROPERTY '))]
lines.append('PROPERTY ' + sys.argv[2])
p.write_text('\n'.join(lines) + '\n')
PY
}

# Fresh copies of the sources for one case.
prepare_case() {
  stage_sources "$neg/$1"
}

# run_tlc label module cfg expect-tag
run_tlc() {
  local label="$1" module="$2" cfg="$3" expect="$4"
  local dir="$neg/$label"
  if java -XX:+UseParallelGC -Xmx4g -cp "$root/.deps/tla2tools.jar" tlc2.TLC \
    -workers "$workers" -metadir "$dir/states" -config "$dir/$cfg.cfg" \
    "$dir/$module.tla" > "$dir/result.log" 2>&1; then
    tlc_exit=0
  else
    tlc_exit=$?
  fi
  rm -rf "$dir/states"
  record_provenance "$dir" "$module" "$cfg" "$dir/result.log" "$expect"
}

# TLC's own output, without the provenance block (whose "expect" line would
# otherwise match the expected text).
tlc_has() {
  sed '/^==== Paralean TLC provenance ====$/,$d' "$1" | grep -F -- "$2" > /dev/null
}

# run_expected_failure label module expected-text [cfg]
run_expected_failure() {
  local label="$1" model="$2" expected="$3" cfg="${4:-$2}"
  local dir="$neg/$label"
  run_tlc "$label" "$model" "$cfg" "failure: $expected"
  if [[ $tlc_exit == 0 ]] || ! tlc_has "$dir/result.log" "$expected"; then
    cat "$dir/result.log"
    echo "Expected counterexample missing: $label (exit $tlc_exit)" >&2
    exit 1
  fi
  echo "$label: expected counterexample found"
}

# The model must pass. For over-restrictive models the configured witnesses
# must survive (useful work is lost); for redundant guards every safety
# invariant must survive the deletion.
run_expected_pass() {
  local label="$1" model="$2" kind="$3" cfg="${4:-$2}"
  local dir="$neg/$label"
  run_tlc "$label" "$model" "$cfg" "pass: $kind"
  if [[ $tlc_exit != 0 ]] ||
     ! tlc_has "$dir/result.log" 'Model checking completed. No error has been found.'; then
    cat "$dir/result.log"
    echo "Expected passing run missing: $label ($kind)" >&2
    exit 1
  fi
  echo "$label: expected pass ($kind) confirmed"
}

# These coverage invariants must FAIL in the ordinary model. Their survival
# under this mutation establishes that the usual witness gate rejects it.
run_expected_missing_witness() {
  run_expected_pass "$1" "$2" "missing useful-work witness" "${3:-$2}"
}

cases=()
defcase() { cases+=("$1"); }

# ---------------------------------------------------------------------------
# Reachability witnesses: each invariant must be violated.
witness_items=(
  'work Chain NeverChainCommitted'
  'dependent_work Chain NeverDependentPublished'
  'collision Collision NeverCollided'
  'durable Quorums NeverAcked'
  'loss Quorums NeverLost'
  'integrated_work Integrated NeverCommitted'
  'checkpoint_reuse CheckpointReuse NeverReusedAfterLoss'
  'export_rejection_work ExportRejected NeverPublished'
  'receipt_work Receipts NeverValidPublished'
  'receipt_dependent_work Receipts NeverDependentPublished'
  'target_alternatives Targets NeverAlternativeCommitted'
  'target_handover Targets NeverHandover'
  'workspace_concurrent_converged Workspace NeverConcurrentConverged'
  'workspace_collision_resolved Workspace NeverCollisionResolved'
  'workspace_winner_revised Workspace NeverWinnerRevised'
  'workspace_deleted Workspace NeverDeleted'
)
witness_case() {
  local label="$1" model="$2" invariant="$3"
  prepare_case "$label"
  finite_witness_config "$neg/$label/$model.cfg" "$invariant"
  if [[ $model == Chain ]]; then
    edit_once "$neg/$label/$model.cfg" 'SPECIFICATION Spec' 'SPECIFICATION ChainWorkSpec'
  fi
  run_expected_failure "$label" "$model" "Invariant $invariant is violated"
}
for item in "${witness_items[@]}"; do
  read -r label _ _ <<< "$item"
  eval "case_$label() { witness_case $item; }"
  defcase "$label"
done

# ---------------------------------------------------------------------------
# Base protocol guards.
defcase unchecked
case_unchecked() {
  prepare_case unchecked
  edit_once "$neg/unchecked/Registry.tla" '    /\ d \in Valid' '    /\ TRUE'
  run_expected_failure unchecked Rejected 'Invariant AdmissionSafety is violated'
}

defcase unknown_dependency
case_unknown_dependency() {
  prepare_case unknown_dependency
  edit_once "$neg/unknown_dependency/Registry.tla" '    /\ Deps[d] \subseteq known[n]' '    /\ TRUE'
  run_expected_failure unknown_dependency Rejected 'Invariant AdmissionSafety is violated'
}

defcase unprepared_publication
case_unprepared_publication() {
  prepare_case unprepared_publication
  edit_once "$neg/unprepared_publication/Registry.tla" '    /\ d \in pending[n]' '    /\ TRUE'
  run_expected_failure unprepared_publication Rejected 'Invariant AdmissionSafety is violated'
}

defcase unpublished_receive
case_unpublished_receive() {
  prepare_case unpublished_receive
  edit_once "$neg/unpublished_receive/Registry.tla" '    /\ d \in published' '    /\ TRUE'
  run_expected_failure unpublished_receive Rejected 'Invariant AdmissionSafety is violated'
}

defcase unknown_ancestor
case_unknown_ancestor() {
  prepare_case unknown_ancestor
  edit_once "$neg/unknown_ancestor/Registry.tla" '    /\ Ancestors[d] \subseteq known[n]' '    /\ TRUE'
  run_expected_failure unknown_ancestor Revision 'Invariant CausalAdmissionSafety is violated'
}

defcase unclosed_ancestors
case_unclosed_ancestors() {
  prepare_case unclosed_ancestors
  edit_once "$neg/unclosed_ancestors/Registry.tla" '    /\ Ancestors[d] \subseteq known[n]' '    /\ TRUE'
  edit_once "$neg/unclosed_ancestors/Revision.cfg" 'CausalAdmissionSafety' 'PublishedAncestorSafety'
  run_expected_failure unclosed_ancestors Revision 'Invariant PublishedAncestorSafety is violated'
}

defcase stale_commit
case_stale_commit() {
  prepare_case stale_commit
  edit_once "$neg/stale_commit/Registry.tla" '    /\ Current(known[n], S)' '    /\ TRUE'
  run_expected_failure stale_commit Revision 'Invariant CommitFreshness is violated'
}

defcase stale_recommit
case_stale_recommit() {
  prepare_case stale_recommit
  edit_once "$neg/stale_recommit/Registry.tla" '    /\ Current(known[n], S)' '    /\ (Current(known[n], S) \/ head[n] = S)'
  run_expected_failure stale_recommit Revision 'Invariant CommitFreshness is violated'
}

defcase unbuildable_commit
case_unbuildable_commit() {
  prepare_case unbuildable_commit
  edit_once "$neg/unbuildable_commit/Registry.tla" '    /\ Buildable(S)' '    /\ TRUE'
  run_expected_failure unbuildable_commit Revision 'Invariant SnapshotSafety is violated'
}

defcase unclosed_snapshot
case_unclosed_snapshot() {
  prepare_case unclosed_snapshot
  edit_once "$neg/unclosed_snapshot/Registry.tla" '                /\ Closed(S)' '                /\ TRUE'
  run_expected_failure unclosed_snapshot Revision 'Invariant NoRetargeting is violated'
}

defcase unexportable_snapshot
case_unexportable_snapshot() {
  prepare_case unexportable_snapshot
  edit_once "$neg/unexportable_snapshot/Registry.tla" '                /\ S \in Exportable' '                /\ TRUE'
  run_expected_failure unexportable_snapshot ExportRejected 'Invariant NoUnexportableCheckpoint is violated'
}

defcase dependent_work_blocked
case_dependent_work_blocked() {
  local d="$neg/dependent_work_blocked"
  prepare_case dependent_work_blocked
  edit_once "$d/Registry.tla" '    /\ d \in Valid' '    /\ d \in Valid /\ Deps[d] = {}'
  finite_witness_config "$d/Chain.cfg" NeverChainCommitted
  printf '%s\n' 'INVARIANT NeverDependentPublished' >> "$d/Chain.cfg"
  edit_once "$d/Chain.cfg" 'SPECIFICATION Spec' 'SPECIFICATION ChainWorkSpec'
  run_expected_missing_witness dependent_work_blocked Chain
}

defcase checkpoint_loss_blocked
case_checkpoint_loss_blocked() {
  local d="$neg/checkpoint_loss_blocked"
  prepare_case checkpoint_loss_blocked
  edit_once "$d/Durability.tla" 'Lose(r) == /\ r \in live' 'Lose(r) == /\ r \in live /\ acknowledged = {}'
  finite_witness_config "$d/CheckpointReuse.cfg" NeverReusedAfterLoss
  run_expected_missing_witness checkpoint_loss_blocked CheckpointReuse
}

defcase premature_ack
case_premature_ack() {
  prepare_case premature_ack
  edit_once "$neg/premature_ack/Durability.tla" '             /\ \A r \in w : o \in stored[r]' '             /\ TRUE'
  run_expected_failure premature_ack Quorums 'Invariant WitnessSurvives is violated'
}

# Temporal mutations check exactly one property each.
defcase no_fair_recovery
case_no_fair_recovery() {
  prepare_case no_fair_recovery
  edit_once "$neg/no_fair_recovery/Registry.tla" 'Spec /\ WF_vars(Heal)' 'Spec'
  single_property "$neg/no_fair_recovery/Collision.cfg" Convergence
  run_expected_failure no_fair_recovery Collision 'Temporal properties were violated'
}

defcase no_fair_receive
case_no_fair_receive() {
  prepare_case no_fair_receive
  edit_once "$neg/no_fair_receive/Registry.tla" '/\ \A n \in Nodes, d \in Decls : WF_vars(Receive(n, d))' '/\ TRUE'
  single_property "$neg/no_fair_receive/Collision.cfg" EventualDelivery
  run_expected_failure no_fair_receive Collision 'Temporal properties were violated'
}

defcase unbacked_publication
case_unbacked_publication() {
  prepare_case unbacked_publication
  edit_once "$neg/unbacked_publication/Publication.tla" 'Publish(n,d) == /\ Payload[d] \in acknowledged' 'Publish(n,d) == /\ TRUE'
  run_expected_failure unbacked_publication Integrated 'Invariant PublicationGuard is violated'
}

defcase staged_publication
case_staged_publication() {
  prepare_case staged_publication
  edit_once "$neg/staged_publication/Publication.tla" 'Publish(n,d) == /\ Payload[d] \in acknowledged' 'Publish(n,d) == /\ \E r \in live : Payload[d] \in stored[r]'
  run_expected_failure staged_publication Integrated 'Invariant PublicationGuard is violated'
}

defcase unbacked_checkpoint
case_unbacked_checkpoint() {
  prepare_case unbacked_checkpoint
  edit_once "$neg/unbacked_checkpoint/Publication.tla" 'Commit(n,S) == /\ Manifest[S] \in acknowledged' 'Commit(n,S) == /\ TRUE'
  run_expected_failure unbacked_checkpoint Integrated 'Invariant CheckpointGuard is violated'
}

# Replace the set of causal heads by an arbitrary singleton. Convergence alone
# still holds; eventual collision detection must reject this mutation.
defcase silent_winner
case_silent_winner() {
  local d="$neg/silent_winner"
  prepare_case silent_winner
  edit_once "$d/Registry.tla" 'Heads(K, name) ==' 'RawHeads(K, name) =='
  edit_once "$d/Registry.tla" 'Conflict(K, name) ==' 'Heads(K, name) == IF RawHeads(K,name) = {} THEN {} ELSE {CHOOSE d \in RawHeads(K,name) : TRUE}
Conflict(K, name) =='
  single_property "$d/Collision.cfg" EventualCollision
  run_expected_failure silent_winner Collision 'Temporal properties were violated'
}

# ---------------------------------------------------------------------------
# Hardening guards. Each removal must produce its named counterexample.
defcase unreceipted_publication
case_unreceipted_publication() {
  local d="$neg/unreceipted_publication"
  prepare_case unreceipted_publication
  edit_once "$d/Receipts.tla" '  /\ g \in held[w]' '  /\ TRUE'
  edit_once "$d/Receipts.cfg" 'PublishedValid PublishedReceipted DepsClosed' 'PublishedValid DepsClosed'
  edit_once "$d/Receipts.cfg" 'INVARIANTS StagedReceipted StagedValid' ''
  run_expected_failure unreceipted_publication Receipts 'Invariant PublishedValid is violated'
}

defcase unreceipted_staging
case_unreceipted_staging() {
  local d="$neg/unreceipted_staging"
  prepare_case unreceipted_staging
  edit_once "$d/Receipts.tla" '  /\ g \in held[w]' '  /\ TRUE'
  edit_once "$d/Receipts.cfg" 'PublishedValid PublishedReceipted DepsClosed' 'DepsClosed'
  edit_once "$d/Receipts.cfg" 'INVARIANTS StagedReceipted StagedValid' 'INVARIANTS StagedValid'
  run_expected_failure unreceipted_staging Receipts 'Invariant StagedValid is violated'
}

# Redundant check: the receipt already certifies published dependencies and
# publication is monotone, so every invariant survives deleting Prepare's
# dependency check (see TLA-GUARDS.md, Redundant checks).
defcase receipt_prepare_no_deps
case_receipt_prepare_no_deps() {
  prepare_case receipt_prepare_no_deps
  edit_once "$neg/receipt_prepare_no_deps/Receipts.tla" $'  /\\ Deps[g] \\subseteq published\n  /\\ g \\in held[w]' '  /\ g \in held[w]'
  run_expected_pass receipt_prepare_no_deps Receipts 'redundant guard keeps every invariant'
}

defcase target_no_owner_check
case_target_no_owner_check() {
  prepare_case target_no_owner_check
  edit_once "$neg/target_no_owner_check/Targets.tla" 'OwnerOK(w) == w = owner' 'OwnerOK(w) == TRUE'
  run_expected_failure target_no_owner_check Targets 'Invariant TargetChain is violated'
}

defcase target_no_revise_head
case_target_no_revise_head() {
  prepare_case target_no_revise_head
  edit_once "$neg/target_no_revise_head/Targets.tla" 'RevisesHead(R) == recHead = None \/ recHead \in R' 'RevisesHead(R) == TRUE'
  run_expected_failure target_no_revise_head Targets 'Invariant TargetChain is violated'
}

# Revise what a certificate scan sees instead of the recorded head. The scan
# result S is any set with certified <= S <= published (a scan finds every
# certificate quorum and only published proofs). With certification lagging
# publication (TargetsLagging) a new owner misses an uncertified head.
defcase target_scan_subset
case_target_scan_subset() {
  prepare_case target_scan_subset
  edit_once "$neg/target_scan_subset/Targets.tla" 'RevisesHead(R) == recHead = None \/ recHead \in R' 'RevisesHead(R) == \E S \in SUBSET published : certified \subseteq S /\ S \subseteq R'
  run_expected_failure target_scan_subset Targets 'Invariant TargetChain is violated' TargetsLagging
}

# The same scan under atomic certification (Targets.cfg) sees every published
# proof, so this finite model keeps TargetChain; recorded in TLA-GUARDS.md.
defcase target_scan_subset_atomic
case_target_scan_subset_atomic() {
  prepare_case target_scan_subset_atomic
  edit_once "$neg/target_scan_subset_atomic/Targets.tla" 'RevisesHead(R) == recHead = None \/ recHead \in R' 'RevisesHead(R) == \E S \in SUBSET published : certified \subseteq S /\ S \subseteq R'
  run_expected_pass target_scan_subset_atomic Targets 'atomic certificates make an atomic scan complete'
}

defcase target_no_head_update
case_target_no_head_update() {
  local d="$neg/target_no_head_update"
  prepare_case target_no_head_update
  edit_once "$d/Targets.tla" 'HeadUpdate(p) == p' 'HeadUpdate(p) == recHead'
  edit_once "$d/Targets.cfg" 'INVARIANTS TypeOK TargetChain HeadUnique RecordTopsChain' 'INVARIANTS TypeOK TargetChain HeadUnique'
  run_expected_failure target_no_head_update Targets 'Invariant TargetChain is violated'
}

defcase target_no_single_pending
case_target_no_single_pending() {
  prepare_case target_no_single_pending
  edit_once "$neg/target_no_single_pending/Targets.tla" 'NoOtherPending(w) == pending[w] = {}' 'NoOtherPending(w) == TRUE'
  run_expected_failure target_no_single_pending Targets 'Invariant TargetChain is violated'
}

defcase target_no_epoch_fence
case_target_no_epoch_fence() {
  prepare_case target_no_epoch_fence
  edit_once "$neg/target_no_epoch_fence/Targets.tla" 'EpochOK(w, p) == prepEpoch[w][p] = epoch' 'EpochOK(w, p) == TRUE'
  run_expected_failure target_no_epoch_fence Targets 'Invariant TargetChain is violated'
}

# Stranded head: with certificates written after publication, a publisher
# that crashes first leaves a recorded head nobody can receive or revise.
defcase target_stranded_head
case_target_stranded_head() {
  local d="$neg/target_stranded_head"
  prepare_case target_stranded_head
  edit_once "$d/TargetsLive.cfg" 'AtomicCert = TRUE' 'AtomicCert = FALSE'
  edit_once "$d/TargetsLive.cfg" ' PublishedCertified' ''
  run_expected_failure target_stranded_head Targets 'Temporal properties were violated' TargetsLive
}

defcase fencing_unfenced_put
case_fencing_unfenced_put() {
  prepare_case fencing_unfenced_put
  edit_once "$neg/fencing_unfenced_put/Fencing.tla" 'FenceOK(w) == holds[w] = fence' 'FenceOK(w) == TRUE'
  run_expected_failure fencing_unfenced_put Fencing 'Invariant StaleNeverStored is violated'
}

# The commit certificate is the fenced write; without its check an old writer
# commits after rotation.
defcase fencing_unfenced_commit
case_fencing_unfenced_commit() {
  prepare_case fencing_unfenced_commit
  edit_once "$neg/fencing_unfenced_commit/Fencing.tla" 'CertFenceOK(w) == fence = holds[w]' 'CertFenceOK(w) == TRUE'
  run_expected_failure fencing_unfenced_commit Fencing 'Invariant CertFenced is violated'
}

defcase fencing_unfenced_commit_selected
case_fencing_unfenced_commit_selected() {
  local d="$neg/fencing_unfenced_commit_selected"
  prepare_case fencing_unfenced_commit_selected
  edit_once "$d/Fencing.tla" 'CertFenceOK(w) == fence = holds[w]' 'CertFenceOK(w) == TRUE'
  edit_once "$d/Fencing.cfg" 'INVARIANTS TypeOK StaleNeverStored CertFenced KnownFenced SelectedFenced NoLateAckedKnown ScanFindsCertified' 'INVARIANTS TypeOK SelectedFenced'
  run_expected_failure fencing_unfenced_commit_selected Fencing 'Invariant SelectedFenced is violated'
}

# Adoption on physical byte quorums (the old Scan) instead of certificates
# adopts a late-acknowledged stale record.
defcase fencing_stale_selected
case_fencing_stale_selected() {
  local d="$neg/fencing_stale_selected"
  prepare_case fencing_stale_selected
  edit_once "$d/Fencing.tla" '           ready == {c \in found : CertDurable(c)}' '           ready == {c \in found : OnLiveQuorum(c)}'
  edit_once "$d/Fencing.cfg" 'INVARIANTS TypeOK StaleNeverStored CertFenced KnownFenced SelectedFenced NoLateAckedKnown ScanFindsCertified' 'INVARIANTS TypeOK NoLateAckedKnown'
  run_expected_failure fencing_stale_selected Fencing 'Invariant NoLateAckedKnown is violated'
}

fencing_witness() {
  prepare_case "$1"
  printf '%s\n' "INVARIANT $2" >> "$neg/$1/Fencing.cfg"
  run_expected_failure "$1" Fencing "Invariant $2 is violated"
}
defcase fencing_recovery_witness
case_fencing_recovery_witness() { fencing_witness fencing_recovery_witness NeverRecoveredAfterRotation; }
defcase fencing_reacquire_witness
case_fencing_reacquire_witness() { fencing_witness fencing_reacquire_witness NeverReacquiredRecovered; }
defcase fencing_middle_witness
case_fencing_middle_witness() { fencing_witness fencing_middle_witness NeverMiddleRecovered; }
defcase fencing_late_ack_witness
case_fencing_late_ack_witness() { fencing_witness fencing_late_ack_witness NeverLateAck; }
defcase fencing_late_repair_witness
case_fencing_late_repair_witness() { fencing_witness fencing_late_repair_witness NeverLateRepair; }

# A commit certificate written before the writer's Ack can outlive the bytes.
defcase fencing_cert_unacked
case_fencing_cert_unacked() {
  prepare_case fencing_cert_unacked
  edit_once "$neg/fencing_cert_unacked/Fencing.tla" '    /\ c \in acked' '    /\ TRUE'
  run_expected_failure fencing_cert_unacked Fencing 'Invariant ScanFindsCertified is violated'
}

defcase fencing_repair_disguised
case_fencing_repair_disguised() {
  prepare_case fencing_repair_disguised
  edit_once "$neg/fencing_repair_disguised/Fencing.tla" '    /\ src \in live /\ c \in stored[src]   \* repair copies existing bytes' '    /\ TRUE'
  run_expected_failure fencing_repair_disguised Fencing 'Invariant StaleNeverStored is violated'
}

# Liveness: a commit over a parent that was acknowledged but never committed
# (its writer was fenced out) is never adoptable.
defcase fencing_commit_orphan
case_fencing_commit_orphan() {
  prepare_case fencing_commit_orphan
  edit_once "$neg/fencing_commit_orphan/Fencing.tla" '    /\ ParentsCommittedOK(c)' '    /\ TRUE'
  run_expected_failure fencing_commit_orphan Fencing 'Temporal properties were violated' FencingLive
}

# Liveness: after a replica loss a committed record needs certificate repair
# to be on a fully live write quorum again.
defcase fencing_no_cert_repair
case_fencing_no_cert_repair() {
  prepare_case fencing_no_cert_repair
  edit_once "$neg/fencing_no_cert_repair/Fencing.tla" '            /\ \A c \in Records, src \in Replicas, r \in Replicas : WF_vars(CertRepair(c, src, r))' '            /\ TRUE'
  run_expected_failure fencing_no_cert_repair Fencing 'Temporal properties were violated' FencingLive
}

defcase cert_scan_raw_marker
case_cert_scan_raw_marker() {
  prepare_case cert_scan_raw_marker
  edit_once "$neg/cert_scan_raw_marker/Certificates.tla" '                        /\ \E r \in q : g \in cert[r]' '                        /\ \E r \in q : g \in marker[r]'
  run_expected_failure cert_scan_raw_marker Certificates 'Invariant ReceivedPublished is violated'
}

# With certificates written after publication (CertificatesLagging) a commit
# without its own reply quorum can contain an undiscoverable group.
defcase cert_commit_unguarded
case_cert_commit_unguarded() {
  local d="$neg/cert_commit_unguarded"
  prepare_case cert_commit_unguarded
  edit_once "$d/Certificates.tla" '                /\ \A g \in S : CertQuorumBy(n, g)' '                /\ TRUE'
  edit_once "$d/CertificatesLagging.cfg" ' CheckpointCertified CheckpointDiscoverable' ' CheckpointDiscoverable'
  run_expected_failure cert_commit_unguarded Certificates 'Invariant CheckpointDiscoverable is violated' CertificatesLagging
}

# Under atomic certification every known group is published and so already
# carries a certificate quorum: the same deletion keeps discoverability.
defcase cert_commit_unguarded_atomic
case_cert_commit_unguarded_atomic() {
  local d="$neg/cert_commit_unguarded_atomic"
  prepare_case cert_commit_unguarded_atomic
  edit_once "$d/Certificates.tla" '                /\ \A g \in S : CertQuorumBy(n, g)' '                /\ TRUE'
  edit_once "$d/Certificates.cfg" ' CheckpointCertified CheckpointDiscoverable' ' CheckpointDiscoverable'
  run_expected_pass cert_commit_unguarded_atomic Certificates 'atomic certificates make the commit reply check redundant for discoverability'
}

defcase cert_put_unknown
case_cert_put_unknown() {
  prepare_case cert_put_unknown
  edit_once "$neg/cert_put_unknown/Certificates.tla" '                    /\ g \in known[n]' '                    /\ TRUE'
  run_expected_failure cert_put_unknown Certificates 'Invariant CertSound is violated'
}

defcase cert_rediscovery_work
case_cert_rediscovery_work() {
  prepare_case cert_rediscovery_work
  printf '%s\n' 'INVARIANT NeverRediscoveredAfterLoss' >> "$neg/cert_rediscovery_work/Certificates.cfg"
  run_expected_failure cert_rediscovery_work Certificates 'Invariant NeverRediscoveredAfterLoss is violated'
}

defcase cert_lost_replier_work
case_cert_lost_replier_work() {
  prepare_case cert_lost_replier_work
  printf '%s\n' 'PROPERTY NeverCommitWithLostReplier' >> "$neg/cert_lost_replier_work/Certificates.cfg"
  run_expected_failure cert_lost_replier_work Certificates 'Action property NeverCommitWithLostReplier is violated'
}

# Stranded publication: certificates written only after publication, by a
# node that still knows the group, are lost with the publisher's index.
defcase cert_stranded_publication
case_cert_stranded_publication() {
  local d="$neg/cert_stranded_publication"
  prepare_case cert_stranded_publication
  edit_once "$d/CertificatesLive.cfg" 'AtomicCert = TRUE' 'AtomicCert = FALSE'
  edit_once "$d/CertificatesLive.cfg" ' PublishedCertified' ''
  single_property "$d/CertificatesLive.cfg" PublishedDiscoverable
  run_expected_failure cert_stranded_publication Certificates 'Temporal properties were violated' CertificatesLive
}

defcase workspace_arrival_order
case_workspace_arrival_order() {
  prepare_case workspace_arrival_order
  edit_once "$neg/workspace_arrival_order/Workspace.tla" "    /\\ doc' = [doc EXCEPT ![x][File[d]] = Render(known'[x], File[d])]" "    /\\ doc' = [doc EXCEPT ![x][File[d]] = Append(doc[x][File[d]], d)]"
  run_expected_failure workspace_arrival_order Workspace 'Invariant SameKnownSameRender is violated'
}

defcase workspace_first_seen_winner
case_workspace_first_seen_winner() {
  prepare_case workspace_first_seen_winner
  edit_once "$neg/workspace_first_seen_winner/Workspace.tla" 'Winner(x, K, n) == LinMin(Heads(K, n))' 'Winner(x, K, n) == IF firstSeen[x][n] \in Heads(K, n) THEN firstSeen[x][n] ELSE LinMin(Heads(K, n))'
  run_expected_failure workspace_first_seen_winner Workspace 'Invariant SameKnownSameRender is violated'
}

defcase workspace_counter_clock
case_workspace_counter_clock() {
  prepare_case workspace_counter_clock
  edit_once "$neg/workspace_counter_clock/Workspace.tla" 'Clock(x) == 1 + KnownMax(known[x])' 'Clock(x) == 1 + Cardinality({d \in known[x] : Author[d] = x})'
  run_expected_failure workspace_counter_clock Workspace 'Action property IntentionPreserved is violated'
}

defcase workspace_own_key_winner
case_workspace_own_key_winner() {
  prepare_case workspace_own_key_winner
  edit_once "$neg/workspace_own_key_winner/Workspace.tla" 'Winner(x, K, n) == LinMin(Heads(K, n))' 'Winner(x, K, n) == Oldest(Heads(K, n))'
  run_expected_failure workspace_own_key_winner Workspace 'Action property WinnerLineageKeepsName is violated'
}

defcase workspace_render_superseded
case_workspace_render_superseded() {
  prepare_case workspace_render_superseded
  edit_once "$neg/workspace_render_superseded/Workspace.tla" 'LiveIn(K, f) == {d \in K : File[d] = f /\ Live(K, d)}' 'LiveIn(K, f) == {d \in K : File[d] = f}'
  run_expected_failure workspace_render_superseded Workspace 'Invariant NoSupersededRendered is violated'
}

# A partial revision (a3 revises a1 for foo only) retires a1 for bar as well.
defcase workspace_partial_revision_witness
case_workspace_partial_revision_witness() {
  prepare_case workspace_partial_revision_witness
  printf '%s\n' 'INVARIANT NeverPartialRevisionFreed' >> "$neg/workspace_partial_revision_witness/Workspace.cfg"
  run_expected_failure workspace_partial_revision_witness Workspace 'Invariant NeverPartialRevisionFreed is violated'
}

defcase workspace_superseded_holds_name
case_workspace_superseded_holds_name() {
  prepare_case workspace_superseded_holds_name
  edit_once "$neg/workspace_superseded_holds_name/Workspace.tla" 'Heads(K, n) == {d \in K : n \in NameSet(d) /\ Live(K, d)}' 'Heads(K, n) == {d \in K : n \in NameSet(d) /\ ~Tomb[d] /\ ~\E e \in K : d \in Anc(e) /\ Name[e] = n}'
  run_expected_failure workspace_superseded_holds_name Workspace 'Invariant NameHeld is violated'
}

# Receive is causal for the anchor and for the revision ancestor.
defcase workspace_receive_unknown_anchor
case_workspace_receive_unknown_anchor() {
  prepare_case workspace_receive_unknown_anchor
  edit_once "$neg/workspace_receive_unknown_anchor/Workspace.tla" $'\\notin known[x]\n    /\\ anchor[d] = Root \\/ anchor[d] \\in known[x]\n' $'\\notin known[x]\n'
  run_expected_failure workspace_receive_unknown_anchor Workspace 'Invariant RenderComplete is violated'
}

defcase workspace_receive_unknown_revision
case_workspace_receive_unknown_revision() {
  prepare_case workspace_receive_unknown_revision
  edit_once "$neg/workspace_receive_unknown_revision/Workspace.tla" $'\\in known[x]\n    /\\ Rev[d] = None \\/ Rev[d] \\in known[x]\n    /\\ known\' = [known EXCEPT ![x] = @ \\cup {d}]\n    /\\ doc\'' $'\\in known[x]\n    /\\ known\' = [known EXCEPT ![x] = @ \\cup {d}]\n    /\\ doc\''
  run_expected_failure workspace_receive_unknown_revision Workspace 'Invariant RenderComplete is violated'
}

# Redundant checks and the independent failure oracle for each effective guard
# are documented in verification/TLA-GUARDS.md.

# ---------------------------------------------------------------------------
if [[ $# == 0 ]]; then
  run=("${cases[@]}")
  rm -rf "$neg"
else
  run=("$@")
fi
mkdir -p "$neg"
for label in "${run[@]}"; do
  if ! declare -F "case_$label" > /dev/null; then
    echo "Unknown negative case: $label" >&2
    exit 2
  fi
  "case_$label"
done
if [[ $# == 0 ]]; then
  printf '%s\n' "${cases[@]}" > "$neg/MANIFEST"
  echo "Negative suite complete: ${#cases[@]} cases"
fi
