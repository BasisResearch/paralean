import Paralean.RecoveryAdequacy

/-! Completion and catalogue recovery over one physical store. A finish cannot
bypass the durable catalogue guard. Component APIs remain unchanged. -/
namespace ParaleanCompletionRecovery

structure State (node group name snapshot request packet record workspace token scan replica writeQuorum readQuorum : Type) where
  admission : ParaleanAdmission.State node group name snapshot request packet replica writeQuorum readQuorum
  recovery : ParaleanRecovery.CanonicalState record workspace snapshot group name token scan

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
set_option linter.unusedSectionVars false

local notation "ATheory" => ParaleanAdmission.Theory node group name snapshot request packet replica writeQuorum readQuorum
local notation "RTheory" => ParaleanRecovery.Theory record workspace snapshot group name token scan
local notation "ModelState" => State node group name snapshot request packet record workspace token scan replica writeQuorum readQuorum

def recoveryView (s : ModelState) : ParaleanRecovery.CoupledState record workspace snapshot group name token scan replica
    (ParaleanAdmission.StoredObject group snapshot) writeQuorum readQuorum :=
  ⟨s.recovery, s.admission.protocol.storage⟩

def Initial (a : ATheory) (r : RTheory) (s : ModelState) : Prop :=
  ParaleanAdmission.Initial a s.admission ∧ ParaleanRecovery.RecoveryInit r s.recovery

def Safe (a : ATheory) (r : RTheory) (encode : record → Nat) (s : ModelState) : Prop :=
  ParaleanAdmission.Safe a s.admission ∧
  ParaleanRecovery.CoupledSafe (ParaleanRecovery.ofAdmission a r encode) (recoveryView s)

/-- Finish is an actual paired delivery/registry action, guarded by a committed
record for this exact image and workspace. Commitment already acknowledges all
three object kinds in the same disk. -/
inductive FinishStep (a : ATheory) (r : RTheory) (n : node) (S : snapshot) (c : record) :
    ModelState → ModelState → Prop where
  | guarded {ad ad' rec} : ParaleanAdmission.FinishStep a n S ad ad' →
      rec.committed c = true → r.image c = S → r.recordWorkspace c = r.identity →
      FinishStep a r n S c ⟨ad, rec⟩ ⟨ad', rec⟩

/-- Labeled admission events without the completion label. -/
inductive OrdinaryNext (a : ATheory) :
    ParaleanAdmission.State node group name snapshot request packet replica writeQuorum readQuorum →
    ParaleanAdmission.State node group name snapshot request packet replica writeQuorum readQuorum → Prop where
  | control {dl dl' pr} (label : ParaleanDelivery.Label node group request packet snapshot name) :
      ParaleanAdmission.Control label → ParaleanDelivery.Step a.delivery dl label dl' →
      OrdinaryNext a ⟨dl, pr⟩ ⟨dl', pr⟩
  | registry {dl rg rg' disk} (label : ParaleanGroups.Label node group name snapshot) :
      ParaleanAdmission.NonCrash label → ParaleanGroups.GroupsNext a.registry rg label rg' →
      ParaleanGroupComposition.Guard (ParaleanAdmission.protocolTheory a) disk label →
      OrdinaryNext a ⟨dl, ⟨rg, disk⟩⟩ ⟨dl, ⟨rg', disk⟩⟩
  | accept {ad ad'} (n : node) (packet : packet) :
      ParaleanAdmission.AcceptStep a n packet ad ad' → OrdinaryNext a ad ad'
  | crash {ad ad'} (n : node) : ParaleanAdmission.CrashStep a n ad ad' → OrdinaryNext a ad ad'
  | stutter {ad} : OrdinaryNext a ad ad

theorem OrdinaryNext.to_next (a : ATheory) {ad ad'} (ht : OrdinaryNext a ad ad') :
    ParaleanAdmission.Next a ad ad' := by
  cases ht with
  | control label hc hd => exact .control label hc hd
  | registry label hc hg hd => exact .protocol (.registry label hc hg hd)
  | accept n m ht => exact ht.to_next a n m _ _
  | crash n ht => exact ht.to_next a n _ _
  | stutter => exact .stutter

/-- Only generated disk transitions occur in this branch. Equal endpoints do
not permit an unlabeled completion event to enter recovery coupling. -/
inductive StorageProtocol (a : ATheory) :
    ParaleanGroupComposition.State node group name snapshot replica (ParaleanAdmission.StoredObject group snapshot) writeQuorum readQuorum →
    ParaleanGroupComposition.State node group name snapshot replica (ParaleanAdmission.StoredObject group snapshot) writeQuorum readQuorum → Prop where
  | storage {rg disk disk'} (label : Durability.Label replica (ParaleanAdmission.StoredObject group snapshot) writeQuorum readQuorum) :
      ParaleanGroupComposition.StorageNext a.storage disk label disk' →
      StorageProtocol a ⟨rg, disk⟩ ⟨rg, disk'⟩

inductive DiskNext (a : ATheory) :
    ParaleanAdmission.State node group name snapshot request packet replica writeQuorum readQuorum →
    ParaleanAdmission.State node group name snapshot request packet replica writeQuorum readQuorum → Prop where
  | protocol {dl pr pr'} : StorageProtocol a pr pr' → DiskNext a ⟨dl, pr⟩ ⟨dl, pr'⟩
  | stutter {ad} : DiskNext a ad ad

theorem DiskNext.to_next (a : ATheory) {ad ad'} (ht : DiskNext a ad ad') :
    ParaleanAdmission.Next a ad ad' := by
  cases ht with
  | protocol hp => cases hp with | storage label hd => exact .protocol (.storage label hd)
  | stutter => exact .stutter

/-- Ordinary admission work excludes completion. Recovery transitions synchronize
any disk update with a generated admission storage transition. -/
inductive Next (a : ATheory) (r : RTheory) (encode : record → Nat) : ModelState → ModelState → Prop where
  | admission {ad ad' rec} : OrdinaryNext a ad ad' →
      ad'.protocol.storage = ad.protocol.storage →
      Next a r encode ⟨ad, rec⟩ ⟨ad', rec⟩
  | coupled {ad ad' rec rec'} : DiskNext a ad ad' →
      ad'.delivery = ad.delivery → ad'.protocol.registry = ad.protocol.registry →
      ParaleanRecovery.CoupledNext (ParaleanRecovery.ofAdmission a r encode)
        ⟨rec, ad.protocol.storage⟩ ⟨rec', ad'.protocol.storage⟩ →
      Next a r encode ⟨ad, rec⟩ ⟨ad', rec'⟩
  | finish {s s'} (n : node) (S : snapshot) (c : record) :
      FinishStep a r n S c s s' → Next a r encode s s'

inductive Reachable (a : ATheory) (r : RTheory) (encode : record → Nat) : ModelState → Prop where
  | initial {s} : Initial a r s → Reachable a r encode s
  | step {s s'} : Reachable a r encode s → Next a r encode s s' → Reachable a r encode s'

theorem next_admission_projection (a : ATheory) (r : RTheory) (encode : record → Nat)
    {s s'} (ht : Next a r encode s s') : ParaleanAdmission.Next a s.admission s'.admission := by
  cases ht with
  | admission ht _ => exact ht.to_next a
  | coupled ht _ _ _ => exact ht.to_next a
  | finish n S c ht => cases ht with | guarded ht _ _ _ => exact ht.to_next a n S _ _

theorem reachable_admission_projection (a : ATheory) (r : RTheory) (encode : record → Nat)
    {s} (hr : Reachable a r encode s) : ParaleanAdmission.Reachable a s.admission := by
  induction hr with
  | initial hi => exact .initial hi.1
  | step _ ht ih => exact .step ih (next_admission_projection a r encode ht)

theorem next_safe (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    (hr : ParaleanRecovery.CoupledAssumptions (ParaleanRecovery.ofAdmission a r encode))
    {s s'} (hs : Safe a r encode s) (ht : Next a r encode s s') : Safe a r encode s' := by
  refine ⟨ParaleanAdmission.next_safe a ha _ _ hs.1 (next_admission_projection a r encode ht), ?_⟩
  cases ht with
  | admission _ hd => simpa [recoveryView, hd] using hs.2
  | coupled _ _ _ hc => exact ParaleanRecovery.coupled_next_safe _ hr _ _ hs.2 hc
  | finish n S c hf =>
    cases hf with
    | guarded ht _ _ _ =>
      cases ht with
      | paired hd hp =>
        cases hp with
        | registry _ _ => exact hs.2

theorem reachable_safe (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    (hr : ParaleanRecovery.CoupledAssumptions (ParaleanRecovery.ofAdmission a r encode))
    {s} (hs : Reachable a r encode s) : Safe a r encode s := by
  induction hs with
  | initial hi =>
    exact ⟨ParaleanAdmission.initial_safe a ha _ hi.1,
      ParaleanRecovery.coupled_initial_safe _ hr _ ⟨hi.2, hi.1.2.2⟩⟩
  | step _ ht ih => exact next_safe a r encode ha hr ih ht

/-- The catalogue guard does not manufacture completion: whenever the original
finish is enabled and a matching durable record exists, the composed finish is enabled. -/
theorem finish_enabled_iff (a : ATheory) (r : RTheory) (s : ModelState)
    (n : node) (S : snapshot) (c : record) :
    (∃ s', FinishStep a r n S c s s') ↔
      (∃ ad', ParaleanAdmission.FinishStep a n S s.admission ad') ∧
      s.recovery.committed c = true ∧ r.image c = S ∧ r.recordWorkspace c = r.identity := by
  constructor
  · rintro ⟨s', ht⟩
    cases ht with | guarded ht hc hi hw => exact ⟨⟨_, ht⟩, hc, hi, hw⟩
  · rintro ⟨⟨ad', ht⟩, hc, hi, hw⟩
    cases s
    exact ⟨⟨ad', _⟩, .guarded ht hc hi hw⟩

/-- Failures use the generated store destruction and desktop-forgetting actions.
They cannot publish or invent a catalogue entry. -/
inductive FailureNext (a : ATheory) (r : RTheory) (encode : record → Nat) : ModelState → ModelState → Prop where
  | storage {dl rg rec disk disk'} (lost : replica) :
      ParaleanGroupComposition.StorageNext a.storage disk (.Lose lost) disk' →
      FailureNext a r encode ⟨⟨dl, ⟨rg, disk⟩⟩, rec⟩ ⟨⟨dl, ⟨rg, disk'⟩⟩, rec⟩
  | desktop {ad rec rec'} : ParaleanRecovery.RecoveryNext r rec .loseDesktop rec' →
      FailureNext a r encode ⟨ad, rec⟩ ⟨ad, rec'⟩

theorem FailureNext.to_next (a : ATheory) (r : RTheory) (encode : record → Nat)
    {s s'} (ht : FailureNext a r encode s s') : Next a r encode s s' := by
  cases ht with
  | storage lost hd =>
    apply Next.coupled (a := a) (r := r) (encode := encode)
      (DiskNext.protocol (StorageProtocol.storage (.Lose lost) hd)) rfl rfl
    exact ParaleanRecovery.CoupledNext.storage (.Lose lost) hd trivial
  | desktop hr =>
    apply Next.coupled (a := a) (r := r) (encode := encode) DiskNext.stutter rfl rfl
    exact ParaleanRecovery.CoupledNext.recovery .loseDesktop (by intro c epoch h; cases h)
      (by intro v h; cases h) hr

theorem FailureNext.committed (a : ATheory) (r : RTheory) (encode : record → Nat)
    {s s'} (ht : FailureNext a r encode s s') : s'.recovery.committed = s.recovery.committed := by
  cases ht with
  | storage _ _ => rfl
  | desktop ht =>
    simp only [ParaleanRecovery.RecoveryNext, ParaleanRecovery.Next, ParaleanRecovery.NextAct,
      ParaleanRecovery.loseDesktop.ext.derived_eq] at ht
    dsimp [ParaleanRecovery.loseDesktop.ext.tr, getFrom, setIn, readFrom,
      Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
      ParaleanRecovery.canonicalFieldRep, Veil.canonicalFieldRepresentation] at ht
    subst_vars
    rfl

inductive FailurePath (a : ATheory) (r : RTheory) (encode : record → Nat) : ModelState → ModelState → Prop where
  | refl {s} : FailurePath a r encode s s
  | snoc {s t u} : FailurePath a r encode s t → FailureNext a r encode t u → FailurePath a r encode s u

theorem FailurePath.reachable (a : ATheory) (r : RTheory) (encode : record → Nat)
    {s t} (hs : Reachable a r encode s) (hp : FailurePath a r encode s t) : Reachable a r encode t := by
  induction hp with
  | refl => exact hs
  | snoc _ ht ih => exact .step ih (ht.to_next a r encode)

theorem FailurePath.committed (a : ATheory) (r : RTheory) (encode : record → Nat)
    {s t} (hp : FailurePath a r encode s t) : t.recovery.committed = s.recovery.committed := by
  induction hp with
  | refl => rfl
  | snoc _ ht ih => exact (ht.committed a r encode).trans ih

/-- A completed required target has a physical recovery path after arbitrary
allowed replica destruction and loss of every desktop catalogue ID. The scan
reads the single disk; admission results and heads are not recovery inputs. -/
theorem completed_required_target_recovery (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    (hra : ParaleanRecovery.CoupledAssumptions (ParaleanRecovery.ofAdmission a r encode))
    {before completed failed : ModelState} (hb : Reachable a r encode before)
    (n : node) (S : snapshot) (c : record) (hf : FinishStep a r n S c before completed)
    (failures : FailurePath a r encode completed failed)
    (q : readQuorum) (hq : ∀ replica, a.storage.memberR replica q = true → failed.admission.protocol.storage.live replica = true)
    (v : scan)
    (hscan : ParaleanRecovery.PhysicalScan (ParaleanRecovery.ofAdmission a r encode) failed.admission.protocol.storage q v)
    (hready : ParaleanRecovery.ReadyScan (ParaleanRecovery.ofAdmission a r encode) failed.admission.protocol.storage v)
    (target : request) (needed : a.delivery.required target = true) :
    ∃ g recovered₁ recovered₂ recovered₃,
      completed.admission.delivery.done n = true ∧ completed.admission.delivery.result n = S ∧
      a.registry.contents S g = true ∧ completed.admission.delivery.checked g target = true ∧
      a.delivery.realizes g target = true ∧
      (∃ replica, failed.admission.protocol.storage.live replica = true ∧
        failed.admission.protocol.storage.stored replica (.catalog (encode c)) = true) ∧
      (∃ replica, failed.admission.protocol.storage.live replica = true ∧
        failed.admission.protocol.storage.stored replica (.manifest S) = true) ∧
      (∃ replica, failed.admission.protocol.storage.live replica = true ∧
        failed.admission.protocol.storage.stored replica (.payload g) = true) ∧
      ParaleanRecovery.CoupledNext (ParaleanRecovery.ofAdmission a r encode) (recoveryView failed) recovered₁ ∧
      ParaleanRecovery.CoupledNext (ParaleanRecovery.ofAdmission a r encode) recovered₁ recovered₂ ∧
      ParaleanRecovery.CoupledNext (ParaleanRecovery.ofAdmission a r encode) recovered₂ recovered₃ ∧
      recovered₃.recovery.selected = true ∧ recovered₃.recovery.selectedRecord = c ∧
      r.image recovered₃.recovery.selectedRecord = S ∧
      recovered₃.recovery.writer = failed.recovery.writer ∧
      recovered₃.recovery.fence = failed.recovery.fence ∧
      recovered₃.storage = failed.admission.protocol.storage := by
  have hc : completed.recovery.committed c = true := by cases hf with | guarded _ hc _ _ => exact hc
  have hi : r.image c = S := by cases hf with | guarded _ _ hi _ => exact hi
  have had : ParaleanAdmission.FinishStep a n S before.admission completed.admission := by
    cases hf with | guarded ht _ _ _ => exact ht
  obtain ⟨g, hg, hchecked, hreal⟩ := ParaleanAdmission.finish_required_groups a ha
    (reachable_admission_projection a r encode hb) n S _ had target needed
  have hrf := failures.reachable a r encode (Reachable.step hb (.finish n S c hf))
  have hcf : failed.recovery.committed c = true := by rw [failures.committed a r encode]; exact hc
  obtain ⟨s₁, s₂, s₃, ht₁, ht₂, ht₃, _, _, _, selected, exactRecord, writer, fence, disk⟩ :=
    ParaleanRecovery.physical_historical_recovery_adequate _ (recoveryView failed) hra
      (reachable_safe a r encode ha hra hrf).2 q hq v hscan hready c hcf
  have hsafe := (reachable_safe a r encode ha hra hrf).2
  have hacks := hsafe.2.2
  have catalogCopy := ParaleanGroupComposition.acknowledged_has_copy
    (ParaleanRecovery.ofAdmission a r encode).base failed.admission.protocol.storage hra.1 hsafe.2.1
    _ (hacks.1 c hcf)
  have other := hacks.2 c hcf
  have manifestCopy := ParaleanGroupComposition.acknowledged_has_copy
    (ParaleanRecovery.ofAdmission a r encode).base failed.admission.protocol.storage hra.1 hsafe.2.1
    _ other.1
  have payloadCopy := ParaleanGroupComposition.acknowledged_has_copy
    (ParaleanRecovery.ofAdmission a r encode).base failed.admission.protocol.storage hra.1 hsafe.2.1
    _ (other.2 g (by simpa [ParaleanRecovery.ofAdmission, ParaleanAdmission.protocolTheory, hi] using hg))
  have complete := ParaleanAdmission.finish_complete_current_durable a ha
    (reachable_admission_projection a r encode hb) n S _ had
  refine ⟨g, s₁, s₂, s₃, complete.1, complete.2.1, hg, hchecked, hreal,
    catalogCopy, ?_, payloadCopy, ht₁, ht₂, ht₃, selected, exactRecord,
    ?_, writer, fence, disk⟩
  · simpa [ParaleanRecovery.ofAdmission, ParaleanAdmission.protocolTheory, hi] using manifestCopy
  · rw [exactRecord]; exact hi

/-- Install a recovery projection without changing admission delivery or registry. -/
def installRecovery (s : ModelState)
    (v : ParaleanRecovery.CoupledState record workspace snapshot group name token scan replica
      (ParaleanAdmission.StoredObject group snapshot) writeQuorum readQuorum) : ModelState :=
  ⟨⟨s.admission.delivery, ⟨s.admission.protocol.registry, v.storage⟩⟩, v.recovery⟩

theorem install_self (s : ModelState) : installRecovery s (recoveryView s) = s := by
  cases s with | mk ad rec => cases ad with | mk dl pr => cases pr; rfl

theorem lift_coupled (a : ATheory) (r : RTheory) (encode : record → Nat) (s : ModelState)
    {v v'} (ht : ParaleanRecovery.CoupledNext (ParaleanRecovery.ofAdmission a r encode) v v') :
    Next a r encode (installRecovery s v) (installRecovery s v') := by
  cases ht with
  | storage l hd hg => exact .coupled (.protocol (.storage l hd)) rfl rfl (.storage l hd hg)
  | commit c epoch w hr hd hm hp =>
    exact .coupled (.protocol (.storage (.Ack _ w) hd)) rfl rfl (.commit c epoch w hr hd hm hp)
  | recovery l hn hd hr => exact .coupled .stutter rfl rfl (.recovery l hn hd hr)

/-- Physical recovery extends the composed reachable prefix by three actual
product transitions. It needs no local completion ID, head, or result. -/
theorem physical_recovery_extends_composed_prefix (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    (hra : ParaleanRecovery.CoupledAssumptions (ParaleanRecovery.ofAdmission a r encode))
    {s : ModelState} (hs : Reachable a r encode s)
    (q : readQuorum) (hq : ∀ replica, a.storage.memberR replica q = true → s.admission.protocol.storage.live replica = true)
    (v : scan)
    (hscan : ParaleanRecovery.PhysicalScan (ParaleanRecovery.ofAdmission a r encode) s.admission.protocol.storage q v)
    (hready : ParaleanRecovery.ReadyScan (ParaleanRecovery.ofAdmission a r encode) s.admission.protocol.storage v)
    (c : record) (hc : s.recovery.committed c = true) :
    ∃ s₁ s₂ s₃, Next a r encode s s₁ ∧ Next a r encode s₁ s₂ ∧ Next a r encode s₂ s₃ ∧
      Reachable a r encode s₃ ∧ s₃.recovery.selected = true ∧ s₃.recovery.selectedRecord = c ∧
      s₃.recovery.writer = s.recovery.writer ∧ s₃.recovery.fence = s.recovery.fence ∧
      s₃.admission.protocol.storage = s.admission.protocol.storage := by
  obtain ⟨v₁, v₂, v₃, ht₁, ht₂, ht₃, _, _, _, selected, exactRecord, writer, fence, disk⟩ :=
    ParaleanRecovery.physical_historical_recovery_adequate _ (recoveryView s) hra
      (reachable_safe a r encode ha hra hs).2 q hq v hscan hready c hc
  have h₁ := lift_coupled a r encode s ht₁
  rw [install_self] at h₁
  have h₂ := lift_coupled a r encode s ht₂
  have h₃ := lift_coupled a r encode s ht₃
  exact ⟨installRecovery s v₁, installRecovery s v₂, installRecovery s v₃,
    h₁, h₂, h₃, .step (.step (.step hs h₁) h₂) h₃, selected, exactRecord, writer, fence, disk⟩

#print axioms next_safe
#print axioms reachable_safe
#print axioms finish_enabled_iff
#print axioms completed_required_target_recovery
#print axioms physical_recovery_extends_composed_prefix
end
end ParaleanCompletionRecovery
