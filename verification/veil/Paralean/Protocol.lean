import Paralean.CompletionRecovery
import Paralean.PublicationDiscovery

/-! Joint protocol on one typed physical store. Every visible step carries both
an actual completion/recovery path and an actual discovery transition. Atomic
publication has two internal storage/registry steps; completion remains guarded.
Neither component can bypass the other component's guards. -/
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
namespace ParaleanProtocol
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

inductive CompletionPath (a : ATheory) (r : RTheory) (encode : record → Nat) : ModelState → ModelState → Prop where
  | refl {s} : CompletionPath a r encode s s
  | snoc {s t u} : CompletionPath a r encode s t →
      ParaleanCompletionRecovery.Next a r encode t u → CompletionPath a r encode s u

theorem CompletionPath.reachable (a : ATheory) (r : RTheory) (encode : record → Nat)
    {s t} (h : CompletionPath a r encode s t) (hs : ParaleanCompletionRecovery.Reachable a r encode s) :
    ParaleanCompletionRecovery.Reachable a r encode t := by
  induction h with
  | refl => exact hs
  | snoc _ ht ih => exact .step ih ht

/-- A visible step is one shared component step, or the designated atomic publish.
No other hidden sequence of completion/recovery events is allowed. -/
inductive Next (a : ATheory) (r : RTheory) (encode : record → Nat) : ModelState → ModelState → Prop where
  | paired {s t} : ParaleanCompletionRecovery.Next a r encode s t →
      ParaleanPublicationDiscovery.Next (ParaleanAdmission.protocolTheory a)
        s.admission.protocol t.admission.protocol → Next a r encode s t
  | publish {dl rg rg' rec disk disk'} (n : node) (d : group) (w : writeQuorum) :
      ParaleanGroups.GroupsNext a.registry rg (.publish n d) rg' →
      ParaleanGroupComposition.StorageNext a.storage disk (.Ack (.publication d) w) disk' →
      disk.acknowledged (.payload d) = true →
      Next a r encode ⟨⟨dl, ⟨rg, disk⟩⟩, rec⟩ ⟨⟨dl, ⟨rg', disk'⟩⟩, rec⟩

theorem Next.completion (a : ATheory) (r : RTheory) (encode : record → Nat)
    {s t : ModelState} (ht : Next a r encode s t) : CompletionPath a r encode s t := by
  cases ht with
  | paired hc _ => exact .snoc .refl hc
  | publish n d w hp hd payload =>
    exact .snoc (.snoc .refl (.admission (.registry (.publish n d) trivial hp payload) rfl))
      (.coupled (.protocol (.storage (.Ack (.publication d) w) hd)) rfl rfl
        (.storage (.Ack (.publication d) w) hd trivial))

theorem Next.discovery (a : ATheory) (r : RTheory) (encode : record → Nat)
    {s t : ModelState} (ht : Next a r encode s t) :
    ParaleanPublicationDiscovery.Next (ParaleanAdmission.protocolTheory a)
      s.admission.protocol t.admission.protocol := by
  cases ht with
  | paired _ hd => exact hd
  | publish n d w hp hd payload => exact .publish n d w hp hd payload

inductive Reachable (a : ATheory) (r : RTheory) (encode : record → Nat) : ModelState → Prop where
  | initial {s} : ParaleanCompletionRecovery.Initial a r s → Reachable a r encode s
  | step {s t} : Reachable a r encode s → Next a r encode s t → Reachable a r encode t

theorem reachable_completion (a : ATheory) (r : RTheory) (encode : record → Nat)
    {s} (h : Reachable a r encode s) : ParaleanCompletionRecovery.Reachable a r encode s := by
  induction h with
  | initial hi => exact .initial hi
  | step _ ht ih => exact (ht.completion a r encode).reachable a r encode ih

theorem reachable_discovery (a : ATheory) (r : RTheory) (encode : record → Nat)
    {s} (h : Reachable a r encode s) :
    ParaleanPublicationDiscovery.Reachable (ParaleanAdmission.protocolTheory a) s.admission.protocol := by
  induction h with
  | initial hi => exact .initial hi.1.2
  | step _ ht ih => exact .step ih (ht.discovery a r encode)

theorem reachable_safe (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    (hra : ParaleanRecovery.CoupledAssumptions (ParaleanRecovery.ofAdmission a r encode))
    {s} (h : Reachable a r encode s) :
    ParaleanCompletionRecovery.Safe a r encode s ∧
      ParaleanPublicationDiscovery.Safe (ParaleanAdmission.protocolTheory a) s.admission.protocol :=
  ⟨ParaleanCompletionRecovery.reachable_safe a r encode ha hra (reachable_completion a r encode h),
    ParaleanPublicationDiscovery.reachable_safe _ ha.2.1 (reachable_discovery a r encode h)⟩

/-- Successful finish is a visible joint transition, including same-head commits. -/
theorem finish_step (a : ATheory) (r : RTheory) (encode : record → Nat)
    {s t : ModelState} (n : node) (S : snapshot) (c : record)
    (h : ParaleanCompletionRecovery.FinishStep a r n S c s t) : Next a r encode s t := by
  refine .paired (.finish n S c h) ?_
  cases h with
  | guarded hf _ _ _ =>
    cases hf with
    | paired _ hp =>
      cases hp with
      | registry hr hg =>
        exact .registry (.commit n S) (by intros; simp) hr hg (by intros; contradiction)

/-- Storage writes and allowed replica loss obey both sets of guards. -/
theorem storage_step (a : ATheory) (r : RTheory) (encode : record → Nat)
    (dl : ParaleanDelivery.CanonicalState node group request packet snapshot name)
    (rg : ParaleanGroups.CanonicalState node group name snapshot)
    (rec : ParaleanRecovery.CanonicalState record workspace snapshot group name token scan)
    (disk disk' : ParaleanGroupComposition.DiskState replica (ParaleanAdmission.StoredObject group snapshot) writeQuorum readQuorum)
    (label : Durability.Label replica (ParaleanAdmission.StoredObject group snapshot) writeQuorum readQuorum)
    (hd : ParaleanGroupComposition.StorageNext a.storage disk label disk')
    (guard : ParaleanPublicationDiscovery.StorageGuard label) :
    Next a r encode ⟨⟨dl, ⟨rg, disk⟩⟩, rec⟩ ⟨⟨dl, ⟨rg, disk'⟩⟩, rec⟩ := by
  exact .paired (.coupled (.protocol (.storage label hd)) rfl rfl
    (.storage label hd (by cases label <;> trivial))) (.storage label guard hd)

/-- Every disk-preserving generated recovery action is a joint transition. -/
theorem recovery_step (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ad : ParaleanAdmission.State node group name snapshot request packet replica writeQuorum readQuorum)
    (rec rec' : ParaleanRecovery.CanonicalState record workspace snapshot group name token scan)
    (h : ParaleanRecovery.CoupledNext (ParaleanRecovery.ofAdmission a r encode)
      ⟨rec, ad.protocol.storage⟩ ⟨rec', ad.protocol.storage⟩) :
    Next a r encode ⟨ad, rec⟩ ⟨ad, rec'⟩ :=
  .paired (.coupled .stutter rfl rfl h) .stutter

/-- Atomic publish projects to generated publish and marker acknowledgement. -/
theorem publication_step (a : ATheory) (r : RTheory) (encode : record → Nat)
    (dl : ParaleanDelivery.CanonicalState node group request packet snapshot name)
    (rg rg' : ParaleanGroups.CanonicalState node group name snapshot)
    (rec : ParaleanRecovery.CanonicalState record workspace snapshot group name token scan)
    (disk disk' : ParaleanGroupComposition.DiskState replica (ParaleanAdmission.StoredObject group snapshot) writeQuorum readQuorum)
    (n : node) (d : group) (w : writeQuorum)
    (hp : ParaleanGroups.GroupsNext a.registry rg (.publish n d) rg')
    (hd : ParaleanGroupComposition.StorageNext a.storage disk (.Ack (.publication d) w) disk')
    (payload : disk.acknowledged (.payload d) = true) :
    Next a r encode ⟨⟨dl, ⟨rg, disk⟩⟩, rec⟩ ⟨⟨dl, ⟨rg', disk'⟩⟩, rec⟩ := .publish n d w hp hd payload

/-- Replica loss and desktop loss remain actual joint protocol actions. -/
theorem failure_step (a : ATheory) (r : RTheory) (encode : record → Nat)
    {s t : ModelState} (h : ParaleanCompletionRecovery.FailureNext a r encode s t) :
    Next a r encode s t := by
  cases h with
  | storage lost hd => exact .paired (.coupled (.protocol (.storage (.Lose lost) hd)) rfl rfl
      (.storage (.Lose lost) hd trivial)) (.storage (.Lose lost) trivial hd)
  | desktop hr => exact .paired (.coupled .stutter rfl rfl
      (.recovery .loseDesktop (by intro c epoch he; cases he) (by intro v he; cases he) hr)) .stutter

theorem failures_reachable (a : ATheory) (r : RTheory) (encode : record → Nat)
    {s t : ModelState} (hs : Reachable a r encode s)
    (h : ParaleanCompletionRecovery.FailurePath a r encode s t) : Reachable a r encode t := by
  induction h with
  | refl => exact hs
  | snoc _ ht ih => exact .step ih (failure_step a r encode ht)

/-- Joint reachability supplies the durable discovery invariant even after every
worker's volatile index is erased. The selected group ID comes from physical scan. -/
theorem all_indexes_erased_rediscovery (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a) {s : ModelState} (hs : Reachable a r encode s)
    (q : readQuorum) (hq : ∀ replica, a.storage.memberR replica q = true → s.admission.protocol.storage.live replica = true)
    (ids : group → Prop)
    (scan : ParaleanPublicationDiscovery.PhysicalScan (ParaleanAdmission.protocolTheory a) s.admission.protocol.storage q ids)
    (erased : ∀ n d, s.admission.protocol.registry.known n d = false)
    (n : node) (ready : s.admission.protocol.registry.alive n = true ∧ s.admission.protocol.registry.online n = true)
    (d : group) (published : s.admission.protocol.registry.published d = true) :
    ids d ∧ ∃ rg', ParaleanGroups.ReceiveStep a.registry s.admission.protocol.registry rg' n d ∧
      rg'.known n d = true ∧ Next a r encode s ⟨⟨s.admission.delivery, ⟨rg', s.admission.protocol.storage⟩⟩, s.recovery⟩ := by
  obtain ⟨hid, rg', ht, hk, hd⟩ := ParaleanPublicationDiscovery.all_indexes_erased_rediscovery _ ha.2.1 _
    (ParaleanPublicationDiscovery.reachable_safe _ ha.2.1 (reachable_discovery a r encode hs))
    q hq ids scan erased n ready d published
  refine ⟨hid, rg', ht, hk, .paired ?_ hd⟩
  refine ParaleanCompletionRecovery.Next.admission ?_ rfl
  apply ParaleanCompletionRecovery.OrdinaryNext.registry (.receive n d) trivial _ trivial
  simpa only [ParaleanGroups.GroupsNext, ParaleanGroups.Next,
    ParaleanGroups.NextAct, ParaleanGroups.receive.ext.derived_eq] using ht

/-- Physical recovery extends the joint protocol with three actual transitions.
The returned state selects exactly the committed record and retains the lease state. -/
theorem committed_physical_recovery (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    (hra : ParaleanRecovery.CoupledAssumptions (ParaleanRecovery.ofAdmission a r encode))
    {s : ModelState} (hs : Reachable a r encode s)
    (q : readQuorum) (hq : ∀ replica, a.storage.memberR replica q = true → s.admission.protocol.storage.live replica = true)
    (v : scan)
    (hscan : ParaleanRecovery.PhysicalScan (ParaleanRecovery.ofAdmission a r encode) s.admission.protocol.storage q v)
    (hready : ParaleanRecovery.ReadyScan (ParaleanRecovery.ofAdmission a r encode) s.admission.protocol.storage v)
    (c : record) (hc : s.recovery.committed c = true) :
    ∃ s₁ s₂ s₃ : ModelState, Next a r encode s s₁ ∧ Next a r encode s₁ s₂ ∧ Next a r encode s₂ s₃ ∧
      Reachable a r encode s₃ ∧ s₃.recovery.selected = true ∧ s₃.recovery.selectedRecord = c ∧
      s₃.recovery.writer = s.recovery.writer ∧ s₃.recovery.fence = s.recovery.fence ∧
      s₃.admission = s.admission := by
  let cr := ParaleanRecovery.ofAdmission a r encode
  let view := ParaleanCompletionRecovery.recoveryView s
  have safe := (reachable_safe a r encode ha hra hs).1.2
  have admissible := ParaleanRecovery.committed_admissible_from_physical_scan cr view hra safe q hq v hscan hready c hc
  obtain ⟨rec₁, ht₁, _, scanned, writer₁, fence₁, known₁⟩ :=
    ParaleanRecovery.physical_enumeration_enabled_with_label cr view hra safe q hq v hscan hready
  let s₁ : ModelState := ⟨s.admission, rec₁⟩
  have step₁ : Next a r encode s s₁ := recovery_step a r encode s.admission s.recovery rec₁ ht₁
  have hk : rec₁.known c = true := (known₁ c).2 admissible
  obtain ⟨recovered₂, ht₂, _, reconstructed, known₂, writer₂, fence₂, disk₂⟩ :=
    ParaleanRecovery.reconstruction_enabled_for_known_record cr ⟨rec₁, s.admission.protocol.storage⟩ c scanned hk
  have h₂ : recovered₂ = ⟨recovered₂.recovery, s.admission.protocol.storage⟩ := by
    cases recovered₂ with
    | mk rr dd => change dd = s.admission.protocol.storage at disk₂; cases disk₂; rfl
  let s₂ : ModelState := ⟨s.admission, recovered₂.recovery⟩
  have step₂ : Next a r encode s₁ s₂ := by
    apply recovery_step a r encode s.admission rec₁ recovered₂.recovery
    rw [h₂] at ht₂
    exact ht₂
  obtain ⟨recovered₃, ht₃, _, selected, exactRecord, writer₃, fence₃, disk₃⟩ :=
    ParaleanRecovery.historical_enabled_for_known_record cr recovered₂ c reconstructed known₂
  let s₃ : ModelState := ⟨s.admission, recovered₃.recovery⟩
  have step₃ : Next a r encode s₂ s₃ := by
    apply recovery_step a r encode s.admission recovered₂.recovery recovered₃.recovery
    have disk₃' := disk₃.trans disk₂
    have h₃ : recovered₃ = ⟨recovered₃.recovery, s.admission.protocol.storage⟩ := by
      cases recovered₃ with
      | mk rr dd => change dd = s.admission.protocol.storage at disk₃'; cases disk₃'; rfl
    rw [h₂, h₃] at ht₃
    exact ht₃
  exact ⟨s₁, s₂, s₃, step₁, step₂, step₃,
    .step (.step (.step hs step₁) step₂) step₃, selected, exactRecord,
    writer₃.trans (writer₂.trans writer₁), fence₃.trans (fence₂.trans fence₁), rfl⟩

/-- Required-target completion and physical recovery hold in the same joint run. -/
theorem completed_required_target_recovery (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    (hra : ParaleanRecovery.CoupledAssumptions (ParaleanRecovery.ofAdmission a r encode))
    {before completed failed : ModelState} (hb : Reachable a r encode before)
    (n : node) (S : snapshot) (c : record) (hf : ParaleanCompletionRecovery.FinishStep a r n S c before completed)
    (failures : ParaleanCompletionRecovery.FailurePath a r encode completed failed)
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
      Next a r encode failed recovered₁ ∧
      Next a r encode recovered₁ recovered₂ ∧
      Next a r encode recovered₂ recovered₃ ∧
      recovered₃.recovery.selected = true ∧ recovered₃.recovery.selectedRecord = c ∧
      r.image recovered₃.recovery.selectedRecord = S ∧
      recovered₃.recovery.writer = failed.recovery.writer ∧
      recovered₃.recovery.fence = failed.recovery.fence ∧
      recovered₃.admission = failed.admission ∧ Reachable a r encode recovered₃ := by
  rcases ParaleanCompletionRecovery.completed_required_target_recovery a r encode ha hra
    (reachable_completion a r encode hb) n S c hf failures q hq v hscan hready target needed with
    ⟨g, _, _, _, done, result, hg, checked, realizes, catalog, manifest, payload, _⟩
  have completedReachable := Reachable.step hb (finish_step a r encode n S c hf)
  have failedReachable := failures_reachable a r encode completedReachable failures
  have hc : failed.recovery.committed c = true := by
    rw [failures.committed a r encode]
    cases hf with | guarded _ hc _ _ => exact hc
  have hi : r.image c = S := by cases hf with | guarded _ _ hi _ => exact hi
  obtain ⟨s₁, s₂, s₃, ht₁, ht₂, ht₃, reachable, selected, exactRecord, writer, fence, admission⟩ :=
    committed_physical_recovery a r encode ha hra failedReachable q hq v hscan hready c hc
  exact ⟨g, s₁, s₂, s₃, done, result, hg, checked, realizes, catalog, manifest, payload,
    ht₁, ht₂, ht₃, selected, exactRecord, by rw [exactRecord]; exact hi,
    writer, fence, admission, reachable⟩

/-- The joint timeline supplies the discovery trace; fairness refers to physical
scan candidates on this same disk and to eventual network healing. -/
structure Trace (a : ATheory) (r : RTheory) (encode : record → Nat) where
  state : Nat → ModelState
  initial : Reachable a r encode (state 0)
  next : ∀ t, Next a r encode (state t) (state (t + 1))

def Trace.toDiscovery (a : ATheory) (r : RTheory) (encode : record → Nat)
    (tr : Trace a r encode) : ParaleanPublicationDiscovery.Trace (ParaleanAdmission.protocolTheory a) where
  state t := (tr.state t).admission.protocol
  initial := reachable_discovery a r encode tr.initial
  next t := (tr.next t).discovery a r encode

theorem Trace.eventual_delivery (a : ATheory) (r : RTheory) (encode : record → Nat)
    (tr : Trace a r encode) (ha : ParaleanAdmission.Assumptions a)
    (healFair : (tr.toDiscovery a r encode).toRegistry.HealFair)
    (fair : (tr.toDiscovery a r encode).ScanReceiveFair)
    (n : node) (d : group) (t : Nat)
    (published : (tr.state t).admission.protocol.registry.published d = true) :
    ParaleanConvergence.EventuallyAlways (fun t => (tr.state t).admission.protocol.registry.known n d = true) :=
  (tr.toDiscovery a r encode).eventual_delivery ha.2.1 healFair fair n d t published

theorem Trace.index_convergence (a : ATheory) (r : RTheory) (encode : record → Nat)
    (tr : Trace a r encode) (ha : ParaleanAdmission.Assumptions a)
    (healFair : (tr.toDiscovery a r encode).toRegistry.HealFair)
    (fair : (tr.toDiscovery a r encode).ScanReceiveFair)
    (nodes : List node) (groups : List group)
    (allNodes : ∀ n, n ∈ nodes) (allGroups : ∀ d, d ∈ groups) :
    ParaleanConvergence.EventuallyAlways (fun t => ∀ n,
      (tr.state t).admission.protocol.registry.known n = (tr.state t).admission.protocol.registry.published) :=
  (tr.toDiscovery a r encode).index_convergence ha.2.1 healFair fair nodes groups allNodes allGroups

end
#print axioms reachable_safe
#print axioms finish_step
#print axioms publication_step
#print axioms all_indexes_erased_rediscovery
#print axioms committed_physical_recovery
#print axioms completed_required_target_recovery
#print axioms Trace.eventual_delivery
#print axioms Trace.index_convergence
end ParaleanProtocol
