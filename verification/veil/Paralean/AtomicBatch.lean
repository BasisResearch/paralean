import Paralean.Hardened

/-!
# Atomic multi-group publication

A batch (store.md T12) publishes several groups and tombstones in one store transaction.
Each member passes the guards of a single publication in the state left by the members
before it, and nobody observes the states between members: a committed transaction maps
to a finite sequence of abstract steps taken at its commit version (store.md, "Atomic
transactions as step sequences"). Here a batch is a nonempty run of hardened steps,
taken as one observable step.

* `run_reachable`, `breachable_iff`: runs whose transactions are hardened steps or batch
  commits reach exactly the hardened reachable states, so `hardened_safe` and every
  other hardened theorem hold for them (`batch_published_receipted`,
  `batch_no_target_collision`).
* `run_published_mono`, `commit_publishes_members`: a group published by any member is
  published once the batch commits. Observers see the state before the commit or after
  it, so they see none of the batch or all of it.
* `run_pairs_next`, `stale_member_blocked`: every member is a hardened step, so no member
  publishes a target proof prepared under an older owner epoch; a batch containing such
  a member does not exist.

Readers that span several transactions (paginated scans, anti-entropy, working copies)
are outside this model; `verification/tla/AtomicBatch.tla` checks them.
-/

namespace ParaleanAtomicBatch
open ParaleanHardened
noncomputable section
variable {node group name snapshot request packet record workspace token scan replica writeQuorum readQuorum : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]
  [DecidableEq request] [Inhabited request] [DecidableEq packet] [Inhabited packet]
  [DecidableEq record] [Inhabited record] [DecidableEq workspace] [Inhabited workspace]
  [DecidableEq token] [Inhabited token] [DecidableEq scan] [Inhabited scan]
  [DecidableEq replica] [Inhabited replica] [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum]
attribute [local instance] Classical.propDecidable

local notation "ATheory" => ParaleanAdmission.Theory node group name snapshot request packet replica writeQuorum readQuorum
local notation "RTheory" => ParaleanRecovery.Theory record workspace snapshot group name token scan
local notation "ModelState" => ParaleanCompletionRecovery.State node group name snapshot request packet record workspace token scan replica writeQuorum readQuorum
local notation "XState" => Extra node record replica group name snapshot
local notation "HState" => ModelState × XState

/-- The member steps of one batch in commit order: each list entry is the state after
one member, reached from the previous one by a hardened step. -/
inductive Run (a : ATheory) (r : RTheory) (encode : record → Nat) (cfg : Config a token record) :
    HState → List HState → HState → Prop where
  | nil {p} : Run a r encode cfg p [] p
  | cons {p q u rest} : Next a r encode cfg p q → Run a r encode cfg q rest u →
      Run a r encode cfg p (q :: rest) u

/-- A batch commit, observed as one step. -/
def Commit (a : ATheory) (r : RTheory) (encode : record → Nat) (cfg : Config a token record)
    (p q : HState) : Prop :=
  ∃ ms, ms ≠ [] ∧ Run a r encode cfg p ms q

/-- Runs whose transactions are hardened steps or batch commits. -/
inductive BReachable (a : ATheory) (r : RTheory) (encode : record → Nat) (cfg : Config a token record) :
    HState → Prop where
  | initial {p} : Initial a r p → BReachable a r encode cfg p
  | step {p q} : BReachable a r encode cfg p → Next a r encode cfg p q → BReachable a r encode cfg q
  | batch {p q} : BReachable a r encode cfg p → Commit a r encode cfg p q → BReachable a r encode cfg q

theorem run_reachable (a : ATheory) (r : RTheory) (encode : record → Nat) (cfg : Config a token record)
    {p ms q} (h : Run a r encode cfg p ms q) (hp : Reachable a r encode cfg p) :
    Reachable a r encode cfg q := by
  induction h with
  | nil => exact hp
  | cons ht _ ih => exact ih (.step hp ht)

theorem commit_reachable (a : ATheory) (r : RTheory) (encode : record → Nat) (cfg : Config a token record)
    {p q} (h : Commit a r encode cfg p q) (hp : Reachable a r encode cfg p) :
    Reachable a r encode cfg q :=
  let ⟨_, _, hr⟩ := h
  run_reachable a r encode cfg hr hp

/-- A batch refines a sequence of hardened steps: batch runs reach exactly the hardened
states. -/
theorem breachable_iff (a : ATheory) (r : RTheory) (encode : record → Nat) (cfg : Config a token record)
    {p} : BReachable a r encode cfg p ↔ Reachable a r encode cfg p := by
  constructor
  · intro h
    induction h with
    | initial hi => exact .initial hi
    | step _ ht ih => exact .step ih ht
    | batch _ hc ih => exact commit_reachable a r encode cfg hc ih
  · intro h
    induction h with
    | initial hi => exact .initial hi
    | step _ ht ih => exact .step ih ht

/-- Fix 1 survives batching: every published group has a verified validator receipt. -/
theorem batch_published_receipted (a : ATheory) (r : RTheory) (encode : record → Nat)
    (cfg : Config a token record) (ha : ParaleanAdmission.Assumptions a)
    (hra : ParaleanRecovery.CoupledAssumptions (ParaleanRecovery.ofAdmission a r encode))
    {p} (h : BReachable a r encode cfg p) (d : group)
    (hd : p.1.admission.protocol.registry.published d = true) :
    ParaleanPublicationReceipts.Receipted a d :=
  (hardened_safe a r encode cfg ha hra ((breachable_iff a r encode cfg).1 h)).2.1 d hd

/-- Fix 2 survives batching: no node has two heads for a target name. -/
theorem batch_no_target_collision (a : ATheory) (r : RTheory) (encode : record → Nat)
    (cfg : Config a token record) (ha : ParaleanAdmission.Assumptions a)
    (hra : ParaleanRecovery.CoupledAssumptions (ParaleanRecovery.ofAdmission a r encode))
    {p} (h : BReachable a r encode cfg p) (x : name)
    (hx : ParaleanTargetNames.IsTarget a cfg.targets x) (n : node) :
    ¬∃ g h, g ≠ h ∧ ParaleanGroups.isHead n g x a.registry p.1.admission.protocol.registry ∧
      ParaleanGroups.isHead n h x a.registry p.1.admission.protocol.registry :=
  (hardened_safe a r encode cfg ha hra ((breachable_iff a r encode cfg).1 h)).2.2.1 x hx n

/-- Publication is monotone along a batch run. -/
theorem run_published_mono (a : ATheory) (r : RTheory) (encode : record → Nat)
    (cfg : Config a token record) {p ms q} (h : Run a r encode cfg p ms q) (d : group)
    (hd : p.1.admission.protocol.registry.published d = true) :
    q.1.admission.protocol.registry.published d = true := by
  induction h with
  | nil => exact hd
  | cons ht _ ih =>
    exact ih ((ParaleanTargetNames.published_step_shape a r encode ht.1).1 d hd)

/-- Every group published by some member is published when the batch commits. -/
theorem commit_publishes_members (a : ATheory) (r : RTheory) (encode : record → Nat)
    (cfg : Config a token record) {p ms q} (h : Run a r encode cfg p ms q) :
    ∀ s ∈ ms, ∀ d, s.1.admission.protocol.registry.published d = true →
      q.1.admission.protocol.registry.published d = true := by
  induction h with
  | nil => intro s hs; cases hs
  | cons _ hr ih =>
    intro s hs d hd
    cases hs with
    | head => exact run_published_mono a r encode cfg hr d hd
    | tail _ hs' => exact ih s hs' d hd

/-- The consecutive state pairs of a run: the member steps. -/
def pairs : HState → List HState → List (HState × HState)
  | _, [] => []
  | p, q :: rest => (p, q) :: pairs q rest

theorem run_pairs_next (a : ATheory) (r : RTheory) (encode : record → Nat)
    (cfg : Config a token record) {p ms q} (h : Run a r encode cfg p ms q) :
    ∀ st ∈ pairs p ms, Next a r encode cfg st.1 st.2 := by
  induction h with
  | nil => intro st hst; cases hst
  | cons ht _ ih =>
    intro st hst
    cases hst with
    | head => exact ht
    | tail _ hst' => exact ih st hst'

/-- A stale owner cannot publish any member: no member step newly publishes a target
proof from a pending bit prepared under an epoch that is no longer current. -/
theorem stale_member_blocked (a : ATheory) (r : RTheory) (encode : record → Nat)
    (cfg : Config a token record) {p ms q} (h : Run a r encode cfg p ms q)
    (st : HState × HState) (hst : st ∈ pairs p ms) (n : node) (d : group) (x : name)
    (hm : a.registry.member d x = true) (hx : ParaleanTargetNames.IsTarget a cfg.targets x)
    (hstale : st.1.2.2.2.2.preparedEpoch n d x ≠ st.1.2.2.2.2.epoch x)
    (hs : st.1.1.admission.protocol.registry.published d = false)
    (ht : st.2.1.admission.protocol.registry.published d = true)
    (hp : st.1.1.admission.protocol.registry.pending n d = true)
    (hc : st.2.1.admission.protocol.registry.pending n d = false) : False :=
  ParaleanTargetNames.stale_publication_blocked a cfg.targets r encode st.1.1 st.2.1
    st.1.2.2.2.2 st.2.2.2.2.2 n d x hm hx hstale hs ht hp hc
    (run_pairs_next a r encode cfg h st hst).2.2.1

end
end ParaleanAtomicBatch
