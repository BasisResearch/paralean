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

# W5: editor publication, policy fencing, atomic rename and private recapture.
editor_mutation() {
  local label="$1" old="$2" replacement="$3" invariant="$4" config="$5"
  prepare_case "$label"
  edit_once "$neg/$label/EditorWiring.tla" "$old" "$replacement"
  run_expected_failure "$label" EditorWiring "Invariant $invariant is violated" "$config"
}
defcase editor_no_receipt
case_editor_no_receipt() { editor_mutation editor_no_receipt 'ReceiptOK == receipt' 'ReceiptOK == TRUE' PublicationSafe EditorPublication; }
defcase editor_no_action
case_editor_no_action() { editor_mutation editor_no_action 'ActionOK == authorized' 'ActionOK == TRUE' PublicationSafe EditorPublication; }
defcase editor_stale_publish
case_editor_stale_publish() { editor_mutation editor_stale_publish 'FreshOK == captured = Stamp' 'FreshOK == TRUE' PublicationSafe EditorPublication; }
defcase editor_no_policy_fence
case_editor_no_policy_fence() { editor_mutation editor_no_policy_fence 'FenceSession == FALSE' 'FenceSession == TRUE' SessionFenced EditorPublication; }
defcase rename_missing_participant
case_rename_missing_participant() { editor_mutation rename_missing_participant 'AllPrepared == prepared = Workspaces' 'AllPrepared == TRUE' RenameSafe EditorRename; }
defcase rename_incomplete_inventory
case_rename_incomplete_inventory() { editor_mutation rename_incomplete_inventory 'InventoryOK == complete' 'InventoryOK == TRUE' RenameSafe EditorRename; }
defcase rename_invalid_plan
case_rename_invalid_plan() { editor_mutation rename_invalid_plan 'PlansOK == validPlans' 'PlansOK == TRUE' RenameSafe EditorRename; }
defcase rename_stale_plan
case_rename_stale_plan() { editor_mutation rename_stale_plan 'FreshOK == captured = Stamp' 'FreshOK == TRUE' RenameSafe EditorRename; }
defcase rename_partial_commit
case_rename_partial_commit() { editor_mutation rename_partial_commit 'RenameSet == Workspaces' 'RenameSet == {"a"}' RenameAtomic EditorRename; }
defcase recapture_unverified
case_recapture_unverified() { editor_mutation recapture_unverified 'ReplayOK == replayVerified' 'ReplayOK == TRUE' OverlaySafe CapsuleReplay; }
defcase recapture_wrong_identity
case_recapture_wrong_identity() { editor_mutation recapture_wrong_identity 'IdentityOK == capsuleMatches' 'IdentityOK == TRUE' OverlaySafe CapsuleReplay; }
defcase editor_publish_work
case_editor_publish_work() {
  prepare_case editor_publish_work
  printf '%s\n' 'INVARIANT NeverPublished' >> "$neg/editor_publish_work/EditorPublication.cfg"
  run_expected_failure editor_publish_work EditorWiring 'Invariant NeverPublished is violated' EditorPublication
}
defcase editor_rename_work
case_editor_rename_work() {
  prepare_case editor_rename_work
  printf '%s\n' 'INVARIANT NeverRenamed' >> "$neg/editor_rename_work/EditorRename.cfg"
  run_expected_failure editor_rename_work EditorWiring 'Invariant NeverRenamed is violated' EditorRename
}
defcase editor_recapture_work
case_editor_recapture_work() {
  prepare_case editor_recapture_work
  printf '%s\n' 'INVARIANT NeverOverlay' >> "$neg/editor_recapture_work/CapsuleReplay.cfg"
  run_expected_failure editor_recapture_work EditorWiring 'Invariant NeverOverlay is violated' CapsuleReplay
}

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
  'target_home_publication TargetHomes NeverPublished'
  'target_home_receive TargetHomes NeverRemoteReceived'
  'target_home_handover TargetHomes NeverReassignedPublication'
  'replay_original ReplayIdentity NeverOriginalAccepted'
  'replay_synthetic_rejection ReplayIdentity NeverSyntheticRejected'
  'replay_ordinary ReplayIdentity NeverOrdinarySyntheticAccepted'
  'lookup_reordered_ref ExportLookup NeverRefAccepted'
  'lookup_reordered_trace ExportLookup NeverTraceAccepted'
  'lookup_reordered_option ExportLookup NeverOptionAccepted'
  'lookup_literal_rejected ExportLookup NeverLiteralRejected'
  'lookup_ambiguous_rejected ExportLookup NeverAmbiguousRejected'
  'lookup_reuse_rejected ExportLookup NeverReusedRejected'
  'residual_f10_recovered ExportLookupResidual NeverDriftAccepted'
  'residual_exact_owner_body_rejected ExportLookupResidual NeverOwnerRejected'
  'residual_early_rejected ExportLookupResidual NeverEarlyRejected'
  'residual_full_ambiguous_rejected ExportLookupResidual NeverAmbiguousRejected'
  'residual_ambiguous_owner_reserved ExportLookupResidual NeverAmbigEarlyRejected'
  'residual_two_captures_rejected ExportLookupResidual NeverTwoRejected'
  'residual_two_candidates_rejected ExportLookupResidual NeverMultiRejected'
  'residual_changed_body_rejected ExportLookupResidual NeverChangedRejected'
  'catalogue_relay CatalogueExchange NeverRelayedChild'
  'w4_handover W4Scale NeverHandover'
  'w4_handover_publish W4Scale NeverHandoverPublished'
  'w4_cross_shard W4Scale NeverDependentPublished'
  'w4_collect W4Scale NeverCollected'
  'w4_desktop_recovery W4Scale NeverRecovered'
  'w4_retained W4Scale NeverRetained'
  'w4_tombstoned W4Scale NeverTombstoned'
  'history_compacted W4History NeverCompacted'
  'history_poll_compacted W4History NeverPollCompacted'
  'history_late_work W4History NeverReplayedAfterCompact'
  'history_late_poll W4History NeverLatePoll'
  'history_replay_gc_off W4History NeverReplayWithGcOff'
  'history_handover W4History NeverHandover'
  'history_cancelled_replay W4History NeverCancelledReplay'
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

# W4 leases and controller-metadata collection. The observers remain intact
# when the corresponding action guard is removed.
defcase w4_no_term_fence
case_w4_no_term_fence() {
  prepare_case w4_no_term_fence
  edit_once "$neg/w4_no_term_fence/W4Scale.tla" \
    '  /\ TermOK(Home[o], w, o)' '  /\ TRUE'
  run_expected_failure w4_no_term_fence W4Scale 'Invariant NoStalePublish is violated'
}

defcase w4_no_expiry
case_w4_no_expiry() {
  prepare_case w4_no_expiry
  edit_once "$neg/w4_no_expiry/W4Scale.tla" \
    'LeaseOK(s, w) == holder[s] = w /\ version[s] < expiry[s]' \
    'LeaseOK(s, w) == holder[s] = w'
  run_expected_failure w4_no_expiry W4Scale 'Invariant NoStalePublish is violated'
}

defcase w4_no_cross_shard_closure
case_w4_no_cross_shard_closure() {
  prepare_case w4_no_cross_shard_closure
  edit_once "$neg/w4_no_cross_shard_closure/W4Scale.tla" \
    'Protected == Closure(Closure(Closure(RootSet)))' 'Protected == RootSet'
  run_expected_failure w4_no_cross_shard_closure W4Scale 'Invariant RootsLive is violated'
}

defcase w4_no_pending_root
case_w4_no_pending_root() {
  prepare_case w4_no_pending_root
  edit_once "$neg/w4_no_pending_root/W4Scale.tla" \
    'RootSet == (Range(roots) \ {None}) \cup pending \cup checkpoint \cup catalog' \
    'RootSet == (Range(roots) \ {None}) \cup checkpoint \cup catalog'
  run_expected_failure w4_no_pending_root W4Scale 'Invariant RootsLive is violated'
}

defcase w4_no_demand_root
case_w4_no_demand_root() {
  prepare_case w4_no_demand_root
  edit_once "$neg/w4_no_demand_root/W4Scale.tla" \
    '           \cup retained \cup UNION {demand[w] : w \in Workers}' \
    '           \cup retained'
  edit_once "$neg/w4_no_demand_root/W4Scale.cfg" \
    'INVARIANTS RootsLive NoResurrection NoStalePublish NoUnrequestedFetch GraceKept NoDemandDeleted' \
    'INVARIANTS NoDemandDeleted'
  run_expected_failure w4_no_demand_root W4Scale 'Invariant NoDemandDeleted is violated'
}

defcase w4_no_grace
case_w4_no_grace() {
  prepare_case w4_no_grace
  edit_once "$neg/w4_no_grace/W4Scale.tla" \
    'OldEnough(o) == retired[o] > 0 /\ version[Home[o]] >= retired[o] + Grace' \
    'OldEnough(o) == retired[o] > 0'
  run_expected_failure w4_no_grace W4Scale 'Invariant GraceKept is violated'
}

defcase w4_no_checkpoint_root
case_w4_no_checkpoint_root() {
  prepare_case w4_no_checkpoint_root
  edit_once "$neg/w4_no_checkpoint_root/W4Scale.tla" \
    'RootSet == (Range(roots) \ {None}) \cup pending \cup checkpoint \cup catalog' \
    'RootSet == (Range(roots) \ {None}) \cup pending \cup catalog'
  run_expected_failure w4_no_checkpoint_root W4Scale 'Invariant RootsLive is violated'
}

defcase w4_no_catalog_root
case_w4_no_catalog_root() {
  prepare_case w4_no_catalog_root
  edit_once "$neg/w4_no_catalog_root/W4Scale.tla" \
    'RootSet == (Range(roots) \ {None}) \cup pending \cup checkpoint \cup catalog' \
    'RootSet == (Range(roots) \ {None}) \cup pending \cup checkpoint'
  run_expected_failure w4_no_catalog_root W4Scale 'Invariant RootsLive is violated'
}

defcase w4_no_retained_root
case_w4_no_retained_root() {
  prepare_case w4_no_retained_root
  edit_once "$neg/w4_no_retained_root/W4Scale.tla" \
    '           \cup retained \cup UNION {demand[w] : w \in Workers}' \
    '           \cup UNION {demand[w] : w \in Workers}'
  run_expected_failure w4_no_retained_root W4Scale 'Invariant RootsLive is violated'
}

# Integration: W3 tombstone lineage is a GC root like checkpoints and catalogue
# records; without it a tombstoned, superseded snapshot can be collected.
defcase w4_no_tombstone_root
case_w4_no_tombstone_root() {
  prepare_case w4_no_tombstone_root
  edit_once "$neg/w4_no_tombstone_root/W4Scale.tla" \
    'TombstoneRoots == tombstoned' 'TombstoneRoots == {}'
  run_expected_failure w4_no_tombstone_root W4Scale 'Invariant RootsLive is violated'
}

defcase w4_unsolicited_fetch
case_w4_unsolicited_fetch() {
  prepare_case w4_unsolicited_fetch
  edit_once "$neg/w4_unsolicited_fetch/W4Scale.tla" \
    '  /\ o \in demand[w]' \
    '  /\ TRUE'
  run_expected_failure w4_unsolicited_fetch W4Scale 'Invariant NoUnrequestedFetch is violated'
}

# W4 history compaction: one atomic metadata transaction moves terminal work
# and stable poll bindings to immutable replay rows before pruning the head.
defcase history_no_fence
case_history_no_fence() {
  prepare_case history_no_fence
  edit_once "$neg/history_no_fence/W4History.tla" \
    'FenceOK(w) == LeaseOK(w) /\ begun[w] = term' \
    'FenceOK(w) == TRUE'
  run_expected_failure history_no_fence W4History 'Invariant FencedCompact is violated'
}

defcase history_no_terminal_check
case_history_no_terminal_check() {
  prepare_case history_no_terminal_check
  edit_once "$neg/history_no_terminal_check/W4History.tla" \
    'TerminalOK == status = "done"' 'TerminalOK == TRUE'
  run_expected_failure history_no_terminal_check W4History 'Invariant PendingKept is violated'
}

defcase history_no_work_marker
case_history_no_work_marker() {
  prepare_case history_no_work_marker
  edit_once "$neg/history_no_work_marker/W4History.tla" \
    "  /\\ workReplay' = TRUE" "  /\\ workReplay' = FALSE"
  run_expected_failure history_no_work_marker W4History 'Invariant ReplayCovered is violated'
}

defcase history_no_poll_marker
case_history_no_poll_marker() {
  prepare_case history_no_poll_marker
  edit_once "$neg/history_no_poll_marker/W4History.tla" \
    "  /\\ pollReplay' = (pollReplay \\/ pollSnapshot)" \
    "  /\\ pollReplay' = pollReplay"
  run_expected_failure history_no_poll_marker W4History 'Invariant PollCovered is violated'
}

defcase history_no_work_replay_lookup
case_history_no_work_replay_lookup() {
  prepare_case history_no_work_replay_lookup
  edit_once "$neg/history_no_work_replay_lookup/W4History.tla" \
    'WorkKnown == status # "absent" \/ workReplay' \
    'WorkKnown == status # "absent"'
  run_expected_failure history_no_work_replay_lookup W4History 'Invariant NoDuplicateWork is violated'
}

defcase history_no_poll_replay_lookup
case_history_no_poll_replay_lookup() {
  prepare_case history_no_poll_replay_lookup
  edit_once "$neg/history_no_poll_replay_lookup/W4History.tla" \
    'PollKnown == pollSnapshot \/ pollReplay' \
    'PollKnown == pollSnapshot'
  run_expected_failure history_no_poll_replay_lookup W4History 'Invariant NoDuplicatePoll is violated'
}

defcase history_no_identity_check
case_history_no_identity_check() {
  prepare_case history_no_identity_check
  edit_once "$neg/history_no_identity_check/W4History.tla" \
    '  /\ (~WorkKnown \/ p = StoredPayload)' '  /\ TRUE'
  run_expected_failure history_no_identity_check W4History 'Invariant ExactIdentity is violated'
}

defcase history_no_poll_worker_check
case_history_no_poll_worker_check() {
  prepare_case history_no_poll_worker_check
  edit_once "$neg/history_no_poll_worker_check/W4History.tla" \
    '  /\ (~PollKnown \/ pollWorker = w)' '  /\ TRUE'
  run_expected_failure history_no_poll_worker_check W4History 'Invariant NoWrongWorker is violated'
}

defcase history_no_work_grace
case_history_no_work_grace() {
  prepare_case history_no_work_grace
  edit_once "$neg/history_no_work_grace/W4History.tla" \
    '  /\ tick >= workFinishedTick + Grace' '  /\ TRUE'
  run_expected_failure history_no_work_grace W4History 'Invariant LogicalGrace is violated'
}

defcase history_no_poll_grace
case_history_no_poll_grace() {
  prepare_case history_no_poll_grace
  edit_once "$neg/history_no_poll_grace/W4History.tla" \
    '  /\ tick >= pollStableTick + Grace' \
    '  /\ TRUE'
  run_expected_failure history_no_poll_grace W4History 'Invariant LogicalGrace is violated'
}

defcase history_no_cancel_overlay
case_history_no_cancel_overlay() {
  prepare_case history_no_cancel_overlay
  edit_once "$neg/history_no_cancel_overlay/W4History.tla" \
    'DuplicateResult == IF cancelled THEN "cancelled" ELSE "done"' \
    'DuplicateResult == "done"'
  run_expected_failure history_no_cancel_overlay W4History 'Invariant CancelOverlay is violated'
}

# ---------------------------------------------------------------------------
# Source-qualified catalogue exchange guards.
for spec in \
  'catalogue_no_proof|SourceProof(r) == r \in sourceCert|SourceProof(r) == TRUE|OnlySourceCertified' \
  'catalogue_no_parent|ParentReady(n, r) == Parent(r) \subseteq (copies[n] \cup local[n])|ParentReady(n, r) == TRUE|ParentClosed' \
  'catalogue_no_ack|PayloadReady(n, r) == r \in payload[n]|PayloadReady(n, r) == TRUE|LocallyAcknowledged'; do
  IFS='|' read -r label old new invariant <<< "$spec"
  # Keep the oracle independent of the predicate removed by a mutation.
  if [[ $label == catalogue_no_parent ]]; then
    old='  /\ ParentReady(n, r)'
    new='  /\ TRUE'
  fi
  eval "case_$label() {
    prepare_case '$label'
    edit_once \"\$neg/$label/CatalogueExchange.tla\" '$old' '$new'
    finite_witness_config \"\$neg/$label/CatalogueExchange.cfg\" '$invariant'
    run_expected_failure '$label' CatalogueExchange 'Invariant $invariant is violated'
  }"
  defcase "$label"
done

defcase catalogue_local_certificate
case_catalogue_local_certificate() {
  prepare_case catalogue_local_certificate
  edit_once "$neg/catalogue_local_certificate/CatalogueExchange.tla" \
    "  /\\ local' = local" "  /\\ local' = [local EXCEPT ![n] = @ \\cup {r}]"
  finite_witness_config "$neg/catalogue_local_certificate/CatalogueExchange.cfg" FenceIsolation
  run_expected_failure catalogue_local_certificate CatalogueExchange 'Invariant FenceIsolation is violated'
}

for spec in \
  'position_foreign_certificate|UseForeignEvidence|LocalCertOnly' \
  'position_group_wide_delete|GroupWideDelete|ReinsertVisible' \
  'position_move_without_delete|SkipMoveGuard|MoveCertified'; do
  IFS='|' read -r label flag invariant <<< "$spec"
  eval "case_$label() {
    prepare_case '$label'
    edit_once \"\$neg/$label/StorePositions.cfg\" '  $flag = FALSE' '  $flag = TRUE'
    run_expected_failure '$label' StorePositions 'Invariant $invariant is violated'
  }"
  defcase "$label"
done

defcase position_registry_erasure
case_position_registry_erasure() {
  prepare_case position_registry_erasure
  edit_once "$neg/position_registry_erasure/StorePositions.tla" \
    '  /\ r = Author[Target[d]]
  /\ storedD'"'"' = [storedD EXCEPT ![r] = @ \cup {d}]
  /\ certD'"'"' = [certD EXCEPT ![r] = @ \cup {d}]
  /\ UNCHANGED <<stagedP, ackP, storedP, certP, foreignP, ackD,
                 foreignD, registry, checkpoint>>' \
    '  /\ r = Author[Target[d]]
  /\ storedD'"'"' = [storedD EXCEPT ![r] = @ \cup {d}]
  /\ certD'"'"' = [certD EXCEPT ![r] = @ \cup {d}]
  /\ registry'"'"' = [registry EXCEPT ![r] = @ \ {GroupOf[Target[d]]}]
  /\ UNCHANGED <<stagedP, ackP, storedP, certP, foreignP, ackD,
                 foreignD, checkpoint>>'
  edit_once "$neg/position_registry_erasure/StorePositions.cfg" \
    'INVARIANTS TypeOK LocalCertOnly TombstoneNeutral MoveCertified CheckpointKept PositionExact ReinsertVisible NoFreshCollision LineageNameStable Converged' \
    'INVARIANT TombstoneNeutral'
  run_expected_failure position_registry_erasure StorePositions 'Invariant TombstoneNeutral is violated'
}

for spec in \
  'agent_no_registry|RegistryGuard|PublishedAuthorized' \
  'agent_no_revocation|RevocationGuard|PublishedAuthorized' \
  'agent_no_controller_fence|FenceGuard|DeletedAuthorized' \
  'agent_no_controller_source|SourceGuard|DeletedAuthorized'; do
  IFS='|' read -r label flag invariant <<< "$spec"
  eval "case_$label() {
    prepare_case '$label'
    edit_once \"\$neg/$label/AgentAuthority.cfg\" '  $flag = TRUE' '  $flag = FALSE'
    run_expected_failure '$label' AgentAuthority 'Invariant $invariant is violated'
  }"
  defcase "$label"
done

defcase checkpoint_no_current
case_checkpoint_no_current() {
  prepare_case checkpoint_no_current
  edit_once "$neg/checkpoint_no_current/CheckpointConflicts.cfg" '  CheckCurrent = TRUE' '  CheckCurrent = FALSE'
  run_expected_failure checkpoint_no_current CheckpointConflicts 'Invariant CommitCurrent is violated'
}

defcase checkpoint_no_buildable
case_checkpoint_no_buildable() {
  prepare_case checkpoint_no_buildable
  edit_once "$neg/checkpoint_no_buildable/CheckpointConflicts.cfg" '  CheckBuildable = TRUE' '  CheckBuildable = FALSE'
  edit_once "$neg/checkpoint_no_buildable/CheckpointConflicts.cfg" '  CheckCurrent = TRUE' '  CheckCurrent = FALSE'
  edit_once "$neg/checkpoint_no_buildable/CheckpointConflicts.cfg" \
    'INVARIANTS TypeOK CommittedBuildable CommittedDeps CommitCurrent' 'INVARIANTS TypeOK CommittedBuildable'
  run_expected_failure checkpoint_no_buildable CheckpointConflicts 'Invariant CommittedBuildable is violated'
}

defcase checkpoint_no_dependencies
case_checkpoint_no_dependencies() {
  prepare_case checkpoint_no_dependencies
  edit_once "$neg/checkpoint_no_dependencies/CheckpointConflicts.cfg" '  CheckDeps = TRUE' '  CheckDeps = FALSE'
  run_expected_failure checkpoint_no_dependencies CheckpointConflicts 'Invariant CommittedDeps is violated'
}

# Base protocol guards.
defcase target_no_home
case_target_no_home() {
  prepare_case target_no_home
  edit_once "$neg/target_no_home/TargetHomes.tla" 'AtHome(d) == d = Home' 'AtHome(d) == TRUE'
  # Isolate the substantive failure: independently fenced stores can create
  # incomparable target proofs. Do not stop at an origin/config invariant.
  edit_once "$neg/target_no_home/TargetHomes.cfg" \
    'INVARIANTS TypeOK TargetChain HeadUnique HomeHeadTopsChain HomeAuthority RemoteRegistersUnchanged' \
    'INVARIANTS TypeOK TargetChain'
  edit_once "$neg/target_no_home/TargetHomes.cfg" 'SPECIFICATION FairSpec' 'SPECIFICATION Spec'
  edit_once "$neg/target_no_home/TargetHomes.cfg" 'PROPERTY EventualDelivery' ''
  run_expected_failure target_no_home TargetHomes 'Invariant TargetChain is violated'
}

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

# Omitting the exact stored-content check admits a replay from the synthetic
# module even though its generated Name literal denotes a different value.
defcase replay_without_exact_identity
case_replay_without_exact_identity() {
  prepare_case replay_without_exact_identity
  edit_once "$neg/replay_without_exact_identity/ReplayIdentity.tla" \
    '  /\ Produced(g, c) = Stored[g]' '  /\ TRUE'
  run_expected_failure replay_without_exact_identity ReplayIdentity \
    'Invariant AcceptedExact is violated'
}

# Positional matching loses source provenance when exported constNames are
# sorted differently from command capture order.
defcase lookup_positional_queue
case_lookup_positional_queue() {
  prepare_case lookup_positional_queue
  edit_once "$neg/lookup_positional_queue/ExportLookup.tla" \
    'Match(g, c) == CandidateKey[c] = CapturedKey[g]' \
    'Match(g, c) == c = Positional[g]'
  run_expected_failure lookup_positional_queue ExportLookup \
    'Invariant AttemptedKey is violated'
}

# A duplicated raw hygiene key is an ambiguous source association even when
# both candidate kernel values happen to have equal bytes.
defcase lookup_no_uniqueness
case_lookup_no_uniqueness() {
  prepare_case lookup_no_uniqueness
  edit_once "$neg/lookup_no_uniqueness/ExportLookup.tla" \
    '  /\ Cardinality(Matches(g)) = 1' '  /\ TRUE'
  run_expected_failure lookup_no_uniqueness ExportLookup \
    'Invariant AcceptedUnique is violated'
}

defcase lookup_no_exact_identity
case_lookup_no_exact_identity() {
  prepare_case lookup_no_exact_identity
  edit_once "$neg/lookup_no_exact_identity/ExportLookup.tla" \
    '  /\ Body[c] = Stored[g]' '  /\ TRUE'
  run_expected_failure lookup_no_exact_identity ExportLookup \
    'Invariant AcceptedExact is violated'
}

# A single exported declaration must not be assigned to two captured groups,
# even when both store the same body and the raw hygiene key is unique.
defcase lookup_no_reuse_guard
case_lookup_no_reuse_guard() {
  prepare_case lookup_no_reuse_guard
  edit_once "$neg/lookup_no_reuse_guard/ExportLookup.tla" \
    '  /\ Unused(c)' '  /\ TRUE'
  run_expected_failure lookup_no_reuse_guard ExportLookup \
    'Invariant AcceptedNotReused is violated'
}

# Full-key candidates stay reserved even when their exact owner fails body
# comparison or several exported constants share its key.
defcase residual_no_exact_reservation
case_residual_no_exact_reservation() {
  prepare_case residual_no_exact_reservation
  edit_once "$neg/residual_no_exact_reservation/ExportLookupResidual.tla" \
    'UnusedStem(g) == {c \in StemMatches(g) : Unused(c) /\ ~FullClaimed(c)}' \
    'UnusedStem(g) == {c \in StemMatches(g) : Unused(c)}'
  run_expected_failure residual_no_exact_reservation ExportLookupResidual \
    'Invariant NoExactCandidateStolen is violated'
}

# Derived fixture only: keep the pristine model unchanged. Two exported names
# share an ambiguous full key; a third exported name has the same stem but a
# different key. The residual captured member may use only that third name.
derive_residual_ambiguous_extra() {
  local d="$1/ExportLookupResidual.tla"
  edit_once "$d" '"cOwner", "cAmbig1", "cAmbig2",' \
    '"cOwner", "cAmbig1", "cAmbig2", "cAmbig3",'
  edit_once "$d" '[] c = "cAmbig2" -> "ambigKey"' \
    $'[] c = "cAmbig2" -> "ambigKey"\n                                        [] c = "cAmbig3" -> "freeAmbigKey"'
  edit_once "$d" '[] c \in {"cAmbig1", "cAmbig2"} -> "ambigCommand"' \
    '[] c \in {"cAmbig1", "cAmbig2", "cAmbig3"} -> "ambigCommand"'
  edit_once "$d" '[] c \in {"cAmbig1", "cAmbig2"} -> "A"' \
    '[] c \in {"cAmbig1", "cAmbig2", "cAmbig3"} -> "A"'
}

defcase residual_ambiguous_extra_baseline
case_residual_ambiguous_extra_baseline() {
  local d="$neg/residual_ambiguous_extra_baseline"
  prepare_case residual_ambiguous_extra_baseline
  derive_residual_ambiguous_extra "$d"
  run_expected_pass residual_ambiguous_extra_baseline ExportLookupResidual \
    'derived ambiguous full key and unique residual candidate'
}

defcase residual_no_fullkey_guard
case_residual_no_fullkey_guard() {
  local d="$neg/residual_no_fullkey_guard"
  prepare_case residual_no_fullkey_guard
  derive_residual_ambiguous_extra "$d"
  edit_once "$d/ExportLookupResidual.tla" \
    $'ResidualSuccess(g, c) ==\n  /\\ phase = "residual"\n  /\\ <<g, c>> \\in Pairs \\ attempted\n  /\\ FullMatches(g) = {}' \
    $'ResidualSuccess(g, c) ==\n  /\\ phase = "residual"\n  /\\ <<g, c>> \\in Pairs \\ attempted\n  /\\ TRUE'
  run_expected_failure residual_no_fullkey_guard ExportLookupResidual \
    'Invariant NoAmbiguousAccepted is violated'
}

defcase residual_no_capture_uniqueness
case_residual_no_capture_uniqueness() {
  prepare_case residual_no_capture_uniqueness
  edit_once "$neg/residual_no_capture_uniqueness/ExportLookupResidual.tla" \
    '  /\ Cardinality(ResidualCaptures(g)) = 1' '  /\ TRUE'
  run_expected_failure residual_no_capture_uniqueness ExportLookupResidual \
    'Invariant NoTwoAccepted is violated'
}

defcase residual_no_candidate_uniqueness
case_residual_no_candidate_uniqueness() {
  prepare_case residual_no_candidate_uniqueness
  edit_once "$neg/residual_no_candidate_uniqueness/ExportLookupResidual.tla" \
    '  /\ Cardinality(UnusedStem(g)) = 1' '  /\ TRUE'
  run_expected_failure residual_no_candidate_uniqueness ExportLookupResidual \
    'Invariant NoMultiAccepted is violated'
}

defcase residual_no_exact_body
case_residual_no_exact_body() {
  prepare_case residual_no_exact_body
  edit_once "$neg/residual_no_exact_body/ExportLookupResidual.tla" \
    $'  /\\ Cardinality(UnusedStem(g)) = 1\n  /\\ Body[c] = Stored[g]' \
    $'  /\\ Cardinality(UnusedStem(g)) = 1\n  /\\ TRUE'
  run_expected_failure residual_no_exact_body ExportLookupResidual \
    'Invariant AcceptedExact is violated'
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

# A per-author counter instead of the Lamport clock.
defcase workspace_counter_clock
case_workspace_counter_clock() {
  prepare_case workspace_counter_clock
  edit_once "$neg/workspace_counter_clock/Workspace.tla" 'Clock(x) == 1 + lamport[x]' 'Clock(x) == 1 + Cardinality({d \in View(x) : Author[d] = x})'
  # ClockCovers states the Lamport rule itself; drop it so the oracle is intention.
  edit_once "$neg/workspace_counter_clock/Workspace.cfg" ' ClockCovers' ''
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

# Pending state (WorkspacePending.cfg): an author anchors at its own pending
# declaration; an agent renders a declaration received before its anchor.
pending_witness() {
  local label="$1" invariant="$2"
  prepare_case "$label"
  finite_witness_config "$neg/$label/WorkspacePending.cfg" "$invariant"
  run_expected_failure "$label" Workspace "Invariant $invariant is violated" WorkspacePending
}
defcase workspace_own_pending_anchor
case_workspace_own_pending_anchor() { pending_witness workspace_own_pending_anchor NeverOwnPendingAnchor; }
defcase workspace_early_arrival
case_workspace_early_arrival() { pending_witness workspace_early_arrival NeverEarlyArrivalRendered; }

# A clock rebuilt from the known (published) set alone, as after a restart
# without a persisted clock, reuses the timestamp of an own pending declaration.
defcase workspace_known_clock
case_workspace_known_clock() {
  prepare_case workspace_known_clock
  edit_once "$neg/workspace_known_clock/Workspace.tla" 'Clock(x) == 1 + lamport[x]' 'Clock(x) == 1 + (IF known[x] = {} THEN 0 ELSE CHOOSE t \in {ts[e] : e \in known[x]} : \A e \in known[x] : ts[e] <= t)'
  run_expected_failure workspace_known_clock Workspace 'Invariant KeysUnique is violated' WorkspacePending
}

# PublishGuard: without it a declaration is published before its author's
# own pending anchor.
defcase workspace_no_publish_guard
case_workspace_no_publish_guard() {
  prepare_case workspace_no_publish_guard
  edit_once "$neg/workspace_no_publish_guard/Workspace.tla" $'    /\\ d \\in pending[x]\n    /\\ anchor[d] = Root \\/ anchor[d] \\in known[x]\n' $'    /\\ d \\in pending[x]\n'
  run_expected_failure workspace_no_publish_guard Workspace 'Invariant AnchorClosed is violated' WorkspacePending
}

# Anchoring only on published declarations loses the own-pending-anchor work.
defcase workspace_anchor_published_only
case_workspace_anchor_published_only() {
  local d="$neg/workspace_anchor_published_only"
  prepare_case workspace_anchor_published_only
  edit_once "$d/Workspace.tla" '{e \in View(x) : File[e] = File[d] /\ Rev[e] = None}' '{e \in known[x] : File[e] = File[d] /\ Rev[e] = None}'
  finite_witness_config "$d/WorkspacePending.cfg" NeverOwnPendingAnchor
  run_expected_missing_witness workspace_anchor_published_only Workspace WorkspacePending
}

# Rendering by the anchor tree of the known records (instead of the carried
# paths) drops a declaration received before its anchor.
defcase workspace_render_tree_order
case_workspace_render_tree_order() {
  prepare_case workspace_render_tree_order
  edit_once "$neg/workspace_render_tree_order/Workspace.tla" 'Positions(K, f) == ByPath(Roots(K, f))' 'Positions(K, f) == TreeOrder(K, f)'
  run_expected_failure workspace_render_tree_order Workspace 'Invariant RenderComplete is violated' WorkspacePending
}

# Receive is causal for the revision ancestor.
defcase workspace_receive_unknown_revision
case_workspace_receive_unknown_revision() {
  prepare_case workspace_receive_unknown_revision
  edit_once "$neg/workspace_receive_unknown_revision/Workspace.tla" $'\\notin known[x]\n    /\\ Rev[d] = None \\/ Rev[d] \\in known[x]\n    /\\ known\' = [known EXCEPT ![x] = @ \\cup {d}]\n    /\\ lamport\'' $'\\notin known[x]\n    /\\ known\' = [known EXCEPT ![x] = @ \\cup {d}]\n    /\\ lamport\''
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
