#!/usr/bin/env bash
# Checks verification/tla/Hardened.tla (all hardened guards on one store):
# positive configurations, coverage witnesses (each Never* property must be
# violated), one mutation per guard (each must produce its named invariant
# violation) and redundancy probes (each must pass). Standalone.
#
#   bash scripts/check-tla-hardened.sh            # every case; writes MANIFEST
#   bash scripts/check-tla-hardened.sh a b ...    # only these labels; no MANIFEST
#   bash scripts/check-tla-hardened.sh --list     # print the case labels
#
# Opt-in: not part of check-tla.sh. archive-verification.sh archives a complete
# run (.runs/tla/hardened/MANIFEST) under verification/results/tlc/hardened.
#
# TLC_WORKERS (default 4) and TLC_HEAP (default 6g) bound resources; runs are
# sequential. Each case runs on copies in .runs/tla/hardened/<label>/; its log
# ends with the hashes of the pristine sources and of the (possibly mutated)
# files TLC parsed (scripts/tla-common.sh).
set -euo pipefail
cd "$(dirname "$0")/.."
root="$PWD"
# shellcheck source=scripts/tla-common.sh
source scripts/tla-common.sh
out="$root/.runs/tla/hardened"
workers="${TLC_WORKERS:-4}"
heap="${TLC_HEAP:-6g}"

# Exactly one occurrence, so a changed source cannot silently defeat a mutation.
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

# derive_cfg BASE OUT CHECK [KEY=VALUE ...] [constraint=NAME] [nosym]
# Copies BASE (a cfg in the run directory), drops its INVARIANT lines,
# overrides constants and checks only CHECK ("INVARIANT(S) ..." or "PROPERTY X").
derive_cfg() {
  python3 - "$@" <<'PY'
from pathlib import Path
import sys
base, outp, check, *opts = sys.argv[1:]
lines = [l for l in Path(base).read_text().splitlines()
         if not l.startswith('INVARIANT')]
for o in opts:
    if o == 'nosym':
        lines = [l for l in lines if not l.startswith('SYMMETRY')]
    elif o.startswith('constraint='):
        lines.append('CONSTRAINT ' + o.split('=', 1)[1])
    else:
        k, v = o.split('=', 1)
        hits = [i for i, l in enumerate(lines) if l.strip().startswith(k + ' =')]
        if len(hits) != 1:
            raise SystemExit(f'constant {k} not found exactly once')
        lines[hits[0]] = f'  {k} = {v}'
lines.append(check)
Path(outp).write_text('\n'.join(lines) + '\n')
PY
}

# run_tlc label module cfg expect-tag
run_tlc() {
  local label="$1" module="$2" cfg="$3" expect="$4"
  local dir="$out/$label" start end
  start=$(date +%s)
  if java "-Xmx$heap" -XX:+UseParallelGC -cp "$root/.deps/tla2tools.jar" tlc2.TLC \
    -workers "$workers" -metadir "$dir/states" -config "$dir/$cfg.cfg" \
    "$dir/$module.tla" > "$dir/result.log" 2>&1; then
    tlc_exit=0
  else
    tlc_exit=$?
  fi
  end=$(date +%s)
  rm -rf "$dir/states"
  record_provenance "$dir" "$module" "$cfg" "$dir/result.log" "$expect"
  echo "  [$((end - start))s] $(grep -E '^[0-9]+ states generated' "$dir/result.log" | tail -1 || true)"
}

# TLC's own output, without the provenance block.
tlc_has() {
  sed '/^==== Paralean TLC provenance ====$/,$d' "$1" | grep -F -- "$2" > /dev/null
}

expect_pass() {
  local label="$1" module="$2" cfg="$3" kind="$4"
  run_tlc "$label" "$module" "$cfg" "pass: $kind"
  if [[ $tlc_exit != 0 ]] ||
     ! tlc_has "$out/$label/result.log" 'Model checking completed. No error has been found.'; then
    tail -80 "$out/$label/result.log"
    echo "FAIL $label: expected no error ($kind, exit $tlc_exit)" >&2
    exit 1
  fi
  echo "$label: no error ($kind)"
}

expect_failure() {
  local label="$1" module="$2" cfg="$3" expected="$4"
  run_tlc "$label" "$module" "$cfg" "failure: $expected"
  if [[ $tlc_exit == 0 ]] || ! tlc_has "$out/$label/result.log" "$expected"; then
    tail -80 "$out/$label/result.log"
    echo "FAIL $label: expected '$expected' (exit $tlc_exit)" >&2
    exit 1
  fi
  echo "$label: $expected"
}

cases=()
defcase() { cases+=("$1"); }

# witness LABEL NEVER [cfg options]: the Never* invariant must be violated.
# HardenedMC only adds pruning constraints (see that module).
witness() {
  local label="$1" name="$2"; shift 2
  stage_sources "$out/$label"
  derive_cfg "$out/$label/Hardened.cfg" "$out/$label/run.cfg" "INVARIANT $name" "$@"
  expect_failure "$label" HardenedMC run "Invariant $name is violated"
}

# mutate BASE LABEL INVARIANT OLD NEW [OLD NEW ...]: the guard deletion must
# violate INVARIANT on the BASE instance (Hardened or HardenedReacquire).
mutate() {
  local base="$1" label="$2" invariant="$3"; shift 3
  stage_sources "$out/$label"
  while (($#)); do
    edit_once "$out/$label/Hardened.tla" "$1" "$2"
    shift 2
  done
  derive_cfg "$out/$label/$base.cfg" "$out/$label/run.cfg" "INVARIANT $invariant"
  expect_failure "$label" Hardened run "Invariant $invariant is violated"
}

# probe LABEL "INVARIANTS ..." OLD NEW: a guard deletion that must NOT break
# the listed invariants (the guard is redundant for them in this model).
probe() {
  local label="$1" invariants="$2"
  stage_sources "$out/$label"
  edit_once "$out/$label/Hardened.tla" "$3" "$4"
  derive_cfg "$out/$label/Hardened.cfg" "$out/$label/run.cfg" "$invariants"
  expect_pass "$label" Hardened run "redundant guard"
}

# ---------------------------------------------------------------------------
# Positive runs.
defcase hardened
case_hardened() { stage_sources "$out/hardened"; expect_pass hardened Hardened Hardened safety; }
defcase hardened_reacquire
case_hardened_reacquire() {
  stage_sources "$out/hardened_reacquire"
  expect_pass hardened_reacquire Hardened HardenedReacquire safety
}

# ---------------------------------------------------------------------------
# Coverage witnesses.
defcase w_completed_after_handover
case_w_completed_after_handover() { witness w_completed_after_handover NeverCompletedAfterHandover constraint=NoFailures; }
defcase w_recovered_after_loss_erasure
case_w_recovered_after_loss_erasure() { witness w_recovered_after_loss_erasure NeverRecoveredAfterLossAndErasure MaxEpoch=0 MaxFence=1; }
defcase w_completed_unready_after_loss
case_w_completed_unready_after_loss() { witness w_completed_unready_after_loss NeverCompletedUnreadyAfterLoss MaxEpoch=0 MaxFence=1; }
defcase w_stale_prepare_refused
case_w_stale_prepare_refused() {
  stage_sources "$out/w_stale_prepare_refused"
  derive_cfg "$out/w_stale_prepare_refused/Hardened.cfg" "$out/w_stale_prepare_refused/run.cfg" \
    "PROPERTY NeverStalePrepareRefused" constraint=NoFailures nosym
  expect_failure w_stale_prepare_refused HardenedMC run "Action property NeverStalePrepareRefused is violated"
}
defcase w_stale_catalogue_writer
case_w_stale_catalogue_writer() { witness w_stale_catalogue_writer NeverStaleCatalogueWriter MaxEpoch=0 constraint=NoFailures; }
defcase w_byzantine_attempt
case_w_byzantine_attempt() { witness w_byzantine_attempt NeverByzantineAttempt ByzProbe=TRUE; }
defcase w_reacquired_completed
case_w_reacquired_completed() { witness w_reacquired_completed NeverReacquiredCompleted MaxEpoch=0 MaxFence=3 constraint=NoFailures; }
defcase w_completed_superseded
case_w_completed_superseded() { witness w_completed_superseded NeverCompletedSuperseded MaxFence=1 constraint=NoFailures; }

# ---------------------------------------------------------------------------
# Mutations: one guard each.
defcase m_no_receipt
case_m_no_receipt() { mutate Hardened m_no_receipt StagedValid \
  'ReceiptOK(w, g) == g \in issued' 'ReceiptOK(w, g) == TRUE'; }
defcase m_no_owner_check
case_m_no_owner_check() { mutate Hardened m_no_owner_check TargetChain \
  'OwnerOK(w) == rec[w][1] = w' 'OwnerOK(w) == TRUE' \
  'ReadUseful(w) == owner = w' 'ReadUseful(w) == TRUE'; }
defcase m_no_epoch_condition
case_m_no_epoch_condition() { mutate Hardened m_no_epoch_condition TargetChain \
  'EpochOK(p) == stamp[p] = epoch' 'EpochOK(p) == TRUE'; }
defcase m_no_head_update
case_m_no_head_update() { mutate Hardened m_no_head_update TargetChain \
  'HeadAfter(p) == p' 'HeadAfter(p) == recHead'; }
defcase m_head_from_scan
case_m_head_from_scan() { mutate Hardened m_head_from_scan TargetChain \
  'ReadHead(w) == rec[w][3]' 'ReadHead(w) == IF Heads(w) = {} THEN None ELSE CHOOSE h \in Heads(w) : TRUE'; }
defcase m_no_learn_own_write
case_m_no_learn_own_write() { mutate Hardened m_no_learn_own_write TargetChain \
  'LearnOwnWrite(w, g) == IF g \in Proofs THEN [rec EXCEPT ![w] = <<w, stamp[g], g>>] ELSE rec' 'LearnOwnWrite(w, g) == rec'; }
# The publisher's certificates leave the publish write (the non-atomic,
# stranding design).
defcase m_publish_without_certs
case_m_publish_without_certs() { mutate Hardened m_publish_without_certs PublishedDiscoverable \
  $'  /\\ cert\' = AtomicCerts(g)\n  /\\ certReply\' = [certReply EXCEPT ![w][g] = live]\n' $'  /\\ UNCHANGED pubCertVars\n'; }
defcase m_cert_before_publish
case_m_cert_before_publish() { mutate Hardened m_cert_before_publish CertSound \
  'CertAfterPublish(w, g) == g \in known[w]' 'CertAfterPublish(w, g) == g \in known[w] \/ g \in pending[w]'; }
defcase m_unfenced_put
case_m_unfenced_put() { mutate Hardened m_unfenced_put StaleNeverStored \
  'PutFenceOK(w) == fence = Current(w)' 'PutFenceOK(w) == TRUE'; }
defcase m_repair_without_source
case_m_repair_without_source() { mutate Hardened m_repair_without_source StaleNeverStored \
  'RepairSourceOK(c, src) == src \in live /\ c \in catStored[src]' 'RepairSourceOK(c, src) == TRUE'; }
defcase m_commit_cert_before_ack
case_m_commit_cert_before_ack() { mutate Hardened m_commit_cert_before_ack CompletedRecoverable \
  'AckedOK(c) == QuorumIn(catReply[c])' 'AckedOK(c) == TRUE'; }
defcase m_unfenced_commit_cert
case_m_unfenced_commit_cert() { mutate Hardened m_unfenced_commit_cert ReadyCommitFenced \
  'CommitFenceOK(c) == fence = Tok(c)' 'CommitFenceOK(c) == TRUE'; }
defcase m_parent_uncommitted
case_m_parent_uncommitted() { mutate HardenedReacquire m_parent_uncommitted CompletedRecoverable \
  'ParentsCommittedOK(c) == parentOf[c] = NoTuple \/ CertDurable(rcert, parentOf[c])' 'ParentsCommittedOK(c) == TRUE'; }
defcase m_cert_repair_without_source
case_m_cert_repair_without_source() { mutate Hardened m_cert_repair_without_source CertFenced \
  'CertRepairSourceOK(c, src) == src \in live /\ c \in rcert[src]' 'CertRepairSourceOK(c, src) == TRUE'; }
defcase m_adopt_on_bytes
case_m_adopt_on_bytes() { mutate Hardened m_adopt_on_bytes ReadyCommitFenced \
  'Ready(Q, c) == \A d \in Chain(c) : ReadyOne(Q, d)' \
  'Ready(Q, c) == \E W \in LiveWrites : \A r \in W : c \in catStored[r]'; }
defcase m_complete_uncommitted
case_m_complete_uncommitted() { mutate Hardened m_complete_uncommitted CompletedRecoverable \
  'CatalogueCommitted(w, c) == QuorumIn(rcReply[c])' 'CatalogueCommitted(w, c) == TRUE'; }

# ---------------------------------------------------------------------------
# Redundancy probes: each deletion must leave the listed invariants intact.
# Without the first-write fence, adoption and completion stay safe: the fenced
# commit certificate alone keeps stale records out of recovery.
defcase r_unfenced_put_adoption
case_r_unfenced_put_adoption() { probe r_unfenced_put_adoption \
  "INVARIANTS TargetChain RecordTopsChain CertSound PublishedDiscoverable CheckpointDiscoverable CertFenced ReadyCommitFenced ReadySnapshotSound CompletedRecoverable" \
  'PutFenceOK(w) == fence = Current(w)' 'PutFenceOK(w) == TRUE'; }
# With atomic publication the publisher's certificates reach every live
# replica in the publish write, so every published group is already found by
# every fully live scan; the committer's own reply quorum adds nothing here.
defcase r_commit_without_own_quorum
case_r_commit_without_own_quorum() { probe r_commit_without_own_quorum \
  "INVARIANTS PublishedDiscoverable CheckpointDiscoverable ReadySnapshotSound CompletedRecoverable" \
  'OwnQuorum(w, p) == QuorumIn(certReply[w][p])' 'OwnQuorum(w, p) == TRUE'; }
# Object certificates are written to every live replica at checkpoint commit,
# before a record for that snapshot can be put, so the conjunct never decides
# readiness in this model.
defcase r_ready_without_object_certs
case_r_ready_without_object_certs() { probe r_ready_without_object_certs \
  "INVARIANTS StaleNeverStored CertFenced ReadyCommitFenced ReadyFirstWriteFenced ReadySnapshotSound CompletedRecoverable" \
  'ReadyOne(Q, c) == (\E r \in Q : c \in catStored[r]) /\ CertDurable(rcert, c) /\ CertDurable(ocert, Snap(c))' \
  'ReadyOne(Q, c) == (\E r \in Q : c \in catStored[r]) /\ CertDurable(rcert, c)'; }

# ---------------------------------------------------------------------------
if [[ $# == 1 && $1 == --list ]]; then
  printf '%s\n' "${cases[@]}"
  exit 0
fi
if [[ $# == 0 ]]; then
  run=("${cases[@]}")
  rm -rf "$out"
else
  run=("$@")
fi
mkdir -p "$out"
for label in "${run[@]}"; do
  if ! declare -F "case_$label" > /dev/null; then
    echo "Unknown case: $label" >&2
    exit 2
  fi
  "case_$label"
done
if [[ $# == 0 ]]; then
  printf '%s\n' "${cases[@]}" > "$out/MANIFEST"
  echo "Hardened suite complete: ${#cases[@]} cases"
fi
