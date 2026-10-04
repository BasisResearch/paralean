import Paralean.Protocol
import Paralean.CompletionRecoveryExecution

/-! A single shared-store execution exercises durable publication, guarded
completion, physical replica loss, real desktop-ID loss, and exact recovery. -/
namespace ParaleanProtocol.Example
noncomputable section
open ParaleanAdmission
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

abbrev Disk := ParaleanGroupComposition.DiskState Bool (StoredObject Bool Bool) Unit Unit
abbrev Registry := ParaleanGroups.CanonicalState Bool Bool (Fin 3) Bool
abbrev Delivery := ParaleanDelivery.CanonicalState Bool Bool Bool Bool Bool (Fin 3)
abbrev Recovery := ParaleanRecovery.CanonicalState Bool Unit Bool Bool (Fin 3) Bool Unit
abbrev ModelState := ParaleanCompletionRecovery.Example.CState

def state (dl : Delivery) (rg : Registry) (disk : Disk) (rec : Recovery := ParaleanCompletionRecovery.Example.rec0) : ModelState :=
  ⟨⟨dl, ⟨rg, disk⟩⟩, rec⟩

def d0 := ParaleanCompletionRecovery.Example.disk0
def d1 := ParaleanCompletionRecovery.Example.put d0 false (.payload false)
def d2 := ParaleanCompletionRecovery.Example.put d1 true (.payload false)
def d3 := ParaleanCompletionRecovery.Example.ack d2 (.payload false)
def d4 := ParaleanCompletionRecovery.Example.put d3 false (.publication false)
def d5 := ParaleanCompletionRecovery.Example.put d4 true (.publication false)
def d6 := ParaleanCompletionRecovery.Example.ack d5 (.publication false)
def d7 := ParaleanCompletionRecovery.Example.put d6 false (.payload true)
def d8 := ParaleanCompletionRecovery.Example.put d7 true (.payload true)
def d9 := ParaleanCompletionRecovery.Example.ack d8 (.payload true)
def d10 := ParaleanCompletionRecovery.Example.put d9 false (.publication true)
def d11 := ParaleanCompletionRecovery.Example.put d10 true (.publication true)
def d12 := ParaleanCompletionRecovery.Example.ack d11 (.publication true)
def d13 := ParaleanCompletionRecovery.Example.put d12 false (.manifest true)
def d14 := ParaleanCompletionRecovery.Example.put d13 true (.manifest true)
def d15 := ParaleanCompletionRecovery.Example.ack d14 (.manifest true)
def d16 := ParaleanCompletionRecovery.Example.put d15 false (.catalog 1)
def d17 := ParaleanCompletionRecovery.Example.put d16 true (.catalog 1)
def d18 := ParaleanCompletionRecovery.Example.ack d17 (.catalog 1)
def lostDisk : Disk := { d18 with live := id, stored := fun r o => if r then d18.stored r o else false }

abbrev initial := state ParaleanCompletionRecovery.Example.dl0 ParaleanCompletionRecovery.Example.rg0 d0
abbrev completed := state ParaleanCompletionRecovery.Example.dlDone ParaleanCompletionRecovery.Example.rgCommitted d18 ParaleanCompletionRecovery.Example.recCommitted
abbrev selected := state ParaleanCompletionRecovery.Example.dlDone ParaleanCompletionRecovery.Example.rgCommitted d18 ParaleanCompletionRecovery.Example.recSelected
abbrev failed := state ParaleanCompletionRecovery.Example.dlDone ParaleanCompletionRecovery.Example.rgCommitted lostDisk ParaleanCompletionRecovery.Example.recForgotten

/-- Publication bytes may be written before their atomic acknowledgement. -/
theorem put_joint (dl : Delivery) (rg : Registry) (disk : Disk) (r : Bool)
    (o : StoredObject Bool Bool) (live : disk.live r = true) :
    ParaleanProtocol.Next ParaleanCompletionRecovery.Example.theory ParaleanCompletionRecovery.Example.recoveryTheory ParaleanCompletionRecovery.Example.encode (state dl rg disk)
      (state dl rg (ParaleanCompletionRecovery.Example.put disk r o)) :=
  ParaleanProtocol.storage_step ParaleanCompletionRecovery.Example.theory ParaleanCompletionRecovery.Example.recoveryTheory ParaleanCompletionRecovery.Example.encode dl rg ParaleanCompletionRecovery.Example.rec0 disk
    (ParaleanCompletionRecovery.Example.put disk r o) (.Put r o) (ParaleanCompletionRecovery.Example.put_step disk r o live) trivial

theorem ack_joint (dl : Delivery) (rg : Registry) (disk : Disk) (o : StoredObject Bool Bool)
    (quorum : ∀ r, disk.live r = true ∧ disk.stored r o = true)
    (guard : ParaleanPublicationDiscovery.StorageGuard (Durability.Label.Ack o () : Durability.Label Bool (StoredObject Bool Bool) Unit Unit)) :
    ParaleanProtocol.Next ParaleanCompletionRecovery.Example.theory ParaleanCompletionRecovery.Example.recoveryTheory ParaleanCompletionRecovery.Example.encode (state dl rg disk)
      (state dl rg (ParaleanCompletionRecovery.Example.ack disk o)) :=
  ParaleanProtocol.storage_step ParaleanCompletionRecovery.Example.theory ParaleanCompletionRecovery.Example.recoveryTheory ParaleanCompletionRecovery.Example.encode dl rg ParaleanCompletionRecovery.Example.rec0 disk
    (ParaleanCompletionRecovery.Example.ack disk o) (.Ack o ()) (ParaleanCompletionRecovery.Example.ack_step disk o quorum) guard

theorem prepare_joint (dl : Delivery) (rg rg' : Registry) (disk : Disk) (g : Bool)
    (step : ParaleanGroups.GroupsNext ParaleanCompletionRecovery.Example.groupTheory rg (.prepare false g) rg') :
    ParaleanProtocol.Next ParaleanCompletionRecovery.Example.theory ParaleanCompletionRecovery.Example.recoveryTheory ParaleanCompletionRecovery.Example.encode (state dl rg disk) (state dl rg' disk) :=
  .paired (.admission (.registry (.prepare false g) trivial step trivial) rfl)
    (.registry (.prepare false g) (by intros; simp) step trivial (by intros; contradiction))

theorem publish_joint (dl : Delivery) (rg rg' : Registry) (disk : Disk) (g : Bool)
    (step : ParaleanGroups.GroupsNext ParaleanCompletionRecovery.Example.groupTheory rg (.publish false g) rg')
    (payload : disk.acknowledged (.payload g) = true)
    (quorum : ∀ r, disk.live r = true ∧ disk.stored r (.publication g) = true) :
    ParaleanProtocol.Next ParaleanCompletionRecovery.Example.theory ParaleanCompletionRecovery.Example.recoveryTheory ParaleanCompletionRecovery.Example.encode (state dl rg disk)
      (state dl rg' (ParaleanCompletionRecovery.Example.ack disk (.publication g))) :=
  .publish false g () step (ParaleanCompletionRecovery.Example.ack_step disk (.publication g) quorum) payload

theorem control_joint (dl dl' : Delivery) (rg : Registry) (disk : Disk)
    (label : ParaleanDelivery.Label Bool Bool Bool Bool Bool (Fin 3))
    (control : ParaleanAdmission.Control label)
    (step : ParaleanDelivery.Step ParaleanCompletionRecovery.Example.deliveryTheory dl label dl') :
    ParaleanProtocol.Next ParaleanCompletionRecovery.Example.theory ParaleanCompletionRecovery.Example.recoveryTheory ParaleanCompletionRecovery.Example.encode (state dl rg disk) (state dl' rg disk) :=
  .paired (.admission (.control label control step) rfl) .stutter

theorem accept_joint (dl dl' : Delivery) (rg rg' : Registry) (disk : Disk) (g : Bool)
    (delivery : ParaleanDelivery.Step ParaleanCompletionRecovery.Example.deliveryTheory dl (.accept true g) dl')
    (registry : ParaleanGroups.GroupsNext ParaleanCompletionRecovery.Example.groupTheory rg (.receive true g) rg')
    (marker : disk.acknowledged (.publication g) = true)
    (bytes : disk.stored true (.publication g) = true) (live : disk.live true = true) :
    ParaleanProtocol.Next ParaleanCompletionRecovery.Example.theory ParaleanCompletionRecovery.Example.recoveryTheory ParaleanCompletionRecovery.Example.encode (state dl rg disk) (state dl' rg' disk) := by
  refine .paired (.admission (.accept true g (.paired delivery (.receive registry))) rfl)
    (.registry (.receive true g) (by intros; simp) registry trivial ?_)
  intro n d h
  cases h
  let ids := fun d => ∃ r, ParaleanCompletionRecovery.Example.storageTheory.memberR r () = true ∧ disk.live r = true ∧ disk.stored r (.publication d) = true
  exact ⟨(), ids, by intro d; rfl, ⟨true, rfl, live, bytes⟩, marker⟩

theorem initial_valid : ParaleanCompletionRecovery.Initial ParaleanCompletionRecovery.Example.theory ParaleanCompletionRecovery.Example.recoveryTheory initial :=
  ⟨ParaleanCompletionRecovery.Example.initial_valid, ParaleanCompletionRecovery.Example.recovery_initial⟩

theorem before_catalog_reachable : ParaleanProtocol.Reachable ParaleanCompletionRecovery.Example.theory ParaleanCompletionRecovery.Example.recoveryTheory ParaleanCompletionRecovery.Example.encode
    (state ParaleanCompletionRecovery.Example.dlAcceptedTarget ParaleanCompletionRecovery.Example.rgReceived d17) := by
  have h0 : ParaleanProtocol.Reachable ParaleanCompletionRecovery.Example.theory ParaleanCompletionRecovery.Example.recoveryTheory ParaleanCompletionRecovery.Example.encode initial := .initial initial_valid
  have h1 := ParaleanProtocol.Reachable.step h0 (put_joint ParaleanCompletionRecovery.Example.dl0 ParaleanCompletionRecovery.Example.rg0 d0 false (.payload false) rfl)
  have h2 := ParaleanProtocol.Reachable.step h1 (put_joint ParaleanCompletionRecovery.Example.dl0 ParaleanCompletionRecovery.Example.rg0 d1 true (.payload false) rfl)
  have h3 := ParaleanProtocol.Reachable.step h2 (ack_joint ParaleanCompletionRecovery.Example.dl0 ParaleanCompletionRecovery.Example.rg0 d2 (.payload false)
    (by intro r; cases r <;> simp [d2, d1, d0, ParaleanCompletionRecovery.Example.disk0, ParaleanCompletionRecovery.Example.put]) trivial)
  have h4 := ParaleanProtocol.Reachable.step h3 (put_joint ParaleanCompletionRecovery.Example.dl0 ParaleanCompletionRecovery.Example.rg0 d3 false (.publication false) rfl)
  have h5 := ParaleanProtocol.Reachable.step h4 (put_joint ParaleanCompletionRecovery.Example.dl0 ParaleanCompletionRecovery.Example.rg0 d4 true (.publication false) rfl)
  have h6 := ParaleanProtocol.Reachable.step h5 (prepare_joint ParaleanCompletionRecovery.Example.dl0 ParaleanCompletionRecovery.Example.rg0 ParaleanCompletionRecovery.Example.rgPreparedHelper d5 false ParaleanCompletionRecovery.Example.group_steps.2.1)
  have h7 := ParaleanProtocol.Reachable.step h6 (publish_joint ParaleanCompletionRecovery.Example.dl0 ParaleanCompletionRecovery.Example.rgPreparedHelper ParaleanCompletionRecovery.Example.rgHelper d5 false
    ParaleanCompletionRecovery.Example.group_steps.2.2.1 (by simp [d5, d4, d3, ParaleanCompletionRecovery.Example.ack, ParaleanCompletionRecovery.Example.put])
    (by intro r; cases r <;> simp [d5, d4, d3, d2, d1, d0, ParaleanCompletionRecovery.Example.disk0, ParaleanCompletionRecovery.Example.put, ParaleanCompletionRecovery.Example.ack]))
  have h8 := ParaleanProtocol.Reachable.step h7 (put_joint ParaleanCompletionRecovery.Example.dl0 ParaleanCompletionRecovery.Example.rgHelper d6 false (.payload true) rfl)
  have h9 := ParaleanProtocol.Reachable.step h8 (put_joint ParaleanCompletionRecovery.Example.dl0 ParaleanCompletionRecovery.Example.rgHelper d7 true (.payload true) rfl)
  have h10 := ParaleanProtocol.Reachable.step h9 (ack_joint ParaleanCompletionRecovery.Example.dl0 ParaleanCompletionRecovery.Example.rgHelper d8 (.payload true)
    (by intro r; cases r <;> simp [d8, d7, d6, d5, d4, d3, d2, d1, d0, ParaleanCompletionRecovery.Example.disk0, ParaleanCompletionRecovery.Example.put, ParaleanCompletionRecovery.Example.ack]) trivial)
  have h11 := ParaleanProtocol.Reachable.step h10 (put_joint ParaleanCompletionRecovery.Example.dl0 ParaleanCompletionRecovery.Example.rgHelper d9 false (.publication true) rfl)
  have h12 := ParaleanProtocol.Reachable.step h11 (put_joint ParaleanCompletionRecovery.Example.dl0 ParaleanCompletionRecovery.Example.rgHelper d10 true (.publication true) rfl)
  have h13 := ParaleanProtocol.Reachable.step h12 (prepare_joint ParaleanCompletionRecovery.Example.dl0 ParaleanCompletionRecovery.Example.rgHelper ParaleanCompletionRecovery.Example.rgPreparedTarget d11 true ParaleanCompletionRecovery.Example.group_steps.2.2.2.1)
  have h14 := ParaleanProtocol.Reachable.step h13 (publish_joint ParaleanCompletionRecovery.Example.dl0 ParaleanCompletionRecovery.Example.rgPreparedTarget ParaleanCompletionRecovery.Example.rgPublished d11 true
    ParaleanCompletionRecovery.Example.group_steps.2.2.2.2.1 (by simp [d11, d10, d9, ParaleanCompletionRecovery.Example.ack, ParaleanCompletionRecovery.Example.put])
    (by intro r; cases r <;> simp [d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0, ParaleanCompletionRecovery.Example.disk0, ParaleanCompletionRecovery.Example.put, ParaleanCompletionRecovery.Example.ack]))
  have h15 := ParaleanProtocol.Reachable.step h14 (control_joint ParaleanCompletionRecovery.Example.dl0 ParaleanCompletionRecovery.Example.dlStartedHelper ParaleanCompletionRecovery.Example.rgPublished d12
    (.start true false) trivial ParaleanCompletionRecovery.Example.delivery_steps.2.1)
  have h16 := ParaleanProtocol.Reachable.step h15 (control_joint ParaleanCompletionRecovery.Example.dlStartedHelper ParaleanCompletionRecovery.Example.dlSentHelper ParaleanCompletionRecovery.Example.rgPublished d12
    (.send false) trivial ParaleanCompletionRecovery.Example.delivery_steps.2.2.1)
  have h17 := ParaleanProtocol.Reachable.step h16 (accept_joint ParaleanCompletionRecovery.Example.dlSentHelper ParaleanCompletionRecovery.Example.dlAcceptedHelper ParaleanCompletionRecovery.Example.rgPublished ParaleanCompletionRecovery.Example.rgReceivedHelper d12 false
    ParaleanCompletionRecovery.Example.delivery_steps.2.2.2.1 ParaleanCompletionRecovery.Example.group_steps.2.2.2.2.2.1
    (by simp [d12, d11, d10, d9, d8, d7, d6, ParaleanCompletionRecovery.Example.put, ParaleanCompletionRecovery.Example.ack])
    (by simp [d12, d11, d10, d9, d8, d7, d6, d5, d4, ParaleanCompletionRecovery.Example.put, ParaleanCompletionRecovery.Example.ack]) rfl)
  have h18 := ParaleanProtocol.Reachable.step h17 (control_joint ParaleanCompletionRecovery.Example.dlAcceptedHelper ParaleanCompletionRecovery.Example.dlStartedTarget ParaleanCompletionRecovery.Example.rgReceivedHelper d12
    (.start true true) trivial ParaleanCompletionRecovery.Example.delivery_steps.2.2.2.2.1)
  have h19 := ParaleanProtocol.Reachable.step h18 (control_joint ParaleanCompletionRecovery.Example.dlStartedTarget ParaleanCompletionRecovery.Example.dlSentTarget ParaleanCompletionRecovery.Example.rgReceivedHelper d12
    (.send true) trivial ParaleanCompletionRecovery.Example.delivery_steps.2.2.2.2.2.1)
  have h20 := ParaleanProtocol.Reachable.step h19 (accept_joint ParaleanCompletionRecovery.Example.dlSentTarget ParaleanCompletionRecovery.Example.dlAcceptedTarget ParaleanCompletionRecovery.Example.rgReceivedHelper ParaleanCompletionRecovery.Example.rgReceived d12 true
    ParaleanCompletionRecovery.Example.delivery_steps.2.2.2.2.2.2.1 ParaleanCompletionRecovery.Example.group_steps.2.2.2.2.2.2.1
    (by simp [d12, ParaleanCompletionRecovery.Example.ack]) (by simp [d12, d11, d10, ParaleanCompletionRecovery.Example.put, ParaleanCompletionRecovery.Example.ack]) rfl)
  have h21 := ParaleanProtocol.Reachable.step h20 (put_joint ParaleanCompletionRecovery.Example.dlAcceptedTarget ParaleanCompletionRecovery.Example.rgReceived d12 false (.manifest true) rfl)
  have h22 := ParaleanProtocol.Reachable.step h21 (put_joint ParaleanCompletionRecovery.Example.dlAcceptedTarget ParaleanCompletionRecovery.Example.rgReceived d13 true (.manifest true) rfl)
  have h23 := ParaleanProtocol.Reachable.step h22 (ack_joint ParaleanCompletionRecovery.Example.dlAcceptedTarget ParaleanCompletionRecovery.Example.rgReceived d14 (.manifest true)
    (by intro r; cases r <;> simp [d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0, ParaleanCompletionRecovery.Example.disk0, ParaleanCompletionRecovery.Example.put, ParaleanCompletionRecovery.Example.ack]) trivial)
  have h24 := ParaleanProtocol.Reachable.step h23 (put_joint ParaleanCompletionRecovery.Example.dlAcceptedTarget ParaleanCompletionRecovery.Example.rgReceived d15 false (.catalog 1) rfl)
  exact ParaleanProtocol.Reachable.step h24 (put_joint ParaleanCompletionRecovery.Example.dlAcceptedTarget ParaleanCompletionRecovery.Example.rgReceived d16 true (.catalog 1) rfl)

theorem recovery_commit : ParaleanRecovery.RecoveryNext ParaleanCompletionRecovery.Example.recoveryTheory ParaleanCompletionRecovery.Example.rec0 (.commit true false) ParaleanCompletionRecovery.Example.recCommitted := by
    simp [ParaleanRecovery.RecoveryNext, ParaleanRecovery.Next, ParaleanRecovery.NextAct,
      ParaleanRecovery.commit.ext.derived_eq, ParaleanRecovery.commit.ext.tr,
      ParaleanRecovery.buildable, ParaleanCompletionRecovery.Example.recoveryTheory, ParaleanCompletionRecovery.Example.groupTheory, ParaleanCompletionRecovery.Example.rec0, ParaleanCompletionRecovery.Example.recCommitted,
      getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
      instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanRecovery.canonicalFieldRep,
      Veil.canonicalFieldRepresentation, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]

open ParaleanCompletionRecovery.Example
attribute [local simp] d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18

theorem catalogue_commit_joint : ParaleanProtocol.Next theory recoveryTheory encode
    (state dlAcceptedTarget rgReceived d17) (state dlAcceptedTarget rgReceived d18 recCommitted) := by
  have hd := ack_step d17 (.catalog 1) (by intro r; cases r <;> simp [disk0, put, ack])
  refine .paired (.coupled (.protocol (.storage (.Ack (.catalog 1) ()) hd)) rfl rfl
    (.commit true false () recovery_commit hd ?_ ?_)) (.storage (.Ack (.catalog 1) ()) trivial hd)
  · simp [state, ParaleanRecovery.ofAdmission, protocolTheory, theory, recoveryTheory, put, ack]
  · intro g hg
    cases g <;> simp [state, ParaleanRecovery.ofAdmission, protocolTheory, theory, recoveryTheory, put, ack]

theorem guarded_finish_joint : ParaleanCompletionRecovery.FinishStep theory recoveryTheory true true true
    (state dlAcceptedTarget rgReceived d18 recCommitted) completed := by
  refine .guarded (.paired delivery_steps.2.2.2.2.2.2.2
    (.registry group_steps.2.2.2.2.2.2.2 ?_)) rfl rfl rfl
  simp [ParaleanGroupComposition.Guard, protocolTheory, theory, put, ack]

theorem completed_reachable : ParaleanProtocol.Reachable theory recoveryTheory encode completed :=
  .step (.step before_catalog_reachable catalogue_commit_joint)
    (ParaleanProtocol.finish_step theory recoveryTheory encode true true true guarded_finish_joint)

theorem selected_reachable : ParaleanProtocol.Reachable theory recoveryTheory encode selected := by
  have h₁ : ParaleanProtocol.Next theory recoveryTheory encode completed
      (state dlDone rgCommitted d18 recScanned) := by
    apply ParaleanProtocol.recovery_step theory recoveryTheory encode _ _ _
    refine .recovery (.enumerate ()) (by intro c epoch h; cases h) ?_ local_selection_steps.1
    intro v h c hc
    cases v
    cases c
    · simp [ParaleanRecovery.ofAdmission, recoveryTheory] at hc
    · simp [ParaleanRecovery.StorageReady, ParaleanRecovery.ofAdmission, protocolTheory,
        theory, recoveryTheory, groupTheory, encode, state, put, ack, Bool.forall_bool]
  have h₂ : ParaleanProtocol.Next theory recoveryTheory encode
      (state dlDone rgCommitted d18 recScanned) (state dlDone rgCommitted d18 recReconstructed) :=
    ParaleanProtocol.recovery_step theory recoveryTheory encode _ _ _
      (.recovery .reconstruct (by intro c epoch h; cases h) (by intro v h; cases h) local_selection_steps.2.1)
  have h₃ : ParaleanProtocol.Next theory recoveryTheory encode
      (state dlDone rgCommitted d18 recReconstructed) selected :=
    ParaleanProtocol.recovery_step theory recoveryTheory encode _ _ _
      (.recovery (.historical true) (by intro c epoch h; cases h) (by intro v h; cases h) local_selection_steps.2.2)
  exact .step (.step (.step completed_reachable h₁) h₂) h₃

theorem destroy_replica : ParaleanGroupComposition.StorageNext storageTheory d18 (.Lose false) lostDisk := by
  simp only [ParaleanGroupComposition.StorageNext, Durability.Next, Durability.NextAct, Durability.Lose.ext.derived_eq]
  dsimp [Durability.Lose.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanGroupComposition.diskFieldRep,
    Veil.canonicalFieldRepresentation]
  simp [storageTheory, lostDisk, disk0, put, ack, Veil.FieldRepresentation.setSingle,
    Veil.CanonicalField.set, Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry,
    Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]

theorem forget_selected : ParaleanRecovery.RecoveryNext recoveryTheory recSelected .loseDesktop recForgotten := by
  simp [ParaleanRecovery.RecoveryNext, ParaleanRecovery.Next, ParaleanRecovery.NextAct,
    ParaleanRecovery.loseDesktop.ext.derived_eq, ParaleanRecovery.loseDesktop.ext.tr,
    recSelected, recReconstructed, recScanned, recForgotten, recCommitted, rec0,
    getFrom, setIn, readFrom, Veil.FieldRepresentation.get, instIsSubStateOfRefl,
    instIsSubReaderOfRefl, ParaleanRecovery.canonicalFieldRep, Veil.canonicalFieldRepresentation,
    Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp]

theorem failure_path : ParaleanCompletionRecovery.FailurePath theory recoveryTheory encode selected failed :=
  .snoc (.snoc .refl (.storage false destroy_replica)) (.desktop forget_selected)

theorem failed_reachable : ParaleanProtocol.Reachable theory recoveryTheory encode failed :=
  ParaleanProtocol.failures_reachable theory recoveryTheory encode selected_reachable failure_path

theorem physical_catalogue_scan : ParaleanRecovery.PhysicalScan
    (ParaleanRecovery.ofAdmission theory recoveryTheory encode) failed.admission.protocol.storage () () := by
  intro c
  cases c <;> simp [ParaleanRecovery.PhysicalScan, ParaleanRecovery.QuorumCatalog,
    ParaleanRecovery.ofAdmission, protocolTheory, theory, recoveryTheory, encode,
    state, lostDisk, storageTheory, disk0, put, ack, Bool.exists_bool]

theorem ready_catalogue_scan : ParaleanRecovery.ReadyScan
    (ParaleanRecovery.ofAdmission theory recoveryTheory encode) failed.admission.protocol.storage () := by
  intro c
  cases c <;> simp [ParaleanRecovery.StorageReady, ParaleanRecovery.ofAdmission,
    protocolTheory, theory, recoveryTheory, groupTheory, encode, state,
    lostDisk, disk0, put, ack, Bool.forall_bool]

/-- Both publication markers survive; receipts enumerate actual marker bytes. -/
theorem physical_publication_scan : ParaleanPublicationDiscovery.PhysicalScan
    (protocolTheory theory) failed.admission.protocol.storage () (fun _ => True) := by
  intro g
  cases g <;> simp [ParaleanPublicationDiscovery.PhysicalScan, protocolTheory, theory,
    storageTheory, state, lostDisk, disk0, put, ack, Bool.exists_bool]

/-- One required nonempty execution, governed by both guards, loses a replica and
an actually selected desktop ID, then recovers the exact completed snapshot.
Every returned object has bytes on the surviving replica. -/
theorem joint_nonempty_completion_loss_recovery :
    ParaleanProtocol.Reachable theory recoveryTheory encode selected ∧
    selected.recovery.selectedRecord = true ∧ selected.recovery.known true = true ∧
    ParaleanCompletionRecovery.FailurePath theory recoveryTheory encode selected failed ∧
    ParaleanProtocol.Reachable theory recoveryTheory encode failed ∧
    failed.recovery.selectedRecord = false ∧ (∀ c, failed.recovery.known c = false) ∧
    failed.recovery.writer = false ∧ failed.admission.delivery.done true = true ∧
    failed.admission.delivery.result true = true ∧ failed.admission.delivery.checked true true = true ∧
    deliveryTheory.required true = true ∧ deliveryTheory.realizes true true = true ∧
    groupTheory.deps true false = true ∧ groupTheory.member false 0 = true ∧
    groupTheory.member false 1 = true ∧ groupTheory.member true 2 = true ∧
    ∃ s₁ s₂ recovered, ParaleanProtocol.Next theory recoveryTheory encode failed s₁ ∧
      ParaleanProtocol.Next theory recoveryTheory encode s₁ s₂ ∧
      ParaleanProtocol.Next theory recoveryTheory encode s₂ recovered ∧
      ParaleanProtocol.Reachable theory recoveryTheory encode recovered ∧
      recovered.recovery.selected = true ∧ recovered.recovery.selectedRecord = true ∧
      recoveryTheory.image recovered.recovery.selectedRecord = true ∧
      recovered.recovery.writer = false ∧ recovered.recovery.fence = 0 ∧
      recovered.admission.protocol.storage.live false = false ∧
      recovered.admission.protocol.storage.live true = true ∧
      recovered.admission.protocol.storage.stored true (.catalog 1) = true ∧
      recovered.admission.protocol.storage.stored true (.manifest true) = true ∧
      (∀ g, recovered.admission.protocol.storage.stored true (.payload g) = true ∧
        recovered.admission.protocol.storage.stored true (.publication g) = true) := by
  obtain ⟨s₁, s₂, recovered, ht₁, ht₂, ht₃, reachable, selectedRecord, recordEq, writer, fence, admission⟩ :=
    ParaleanProtocol.committed_physical_recovery theory recoveryTheory encode assumptions recovery_assumptions
      failed_reachable () (by intro r h; cases r <;> simp [theory, storageTheory] at h ⊢; rfl)
      () physical_catalogue_scan ready_catalogue_scan true rfl
  refine ⟨selected_reachable, rfl, rfl, failure_path, failed_reachable, rfl,
    by intro c; rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    s₁, s₂, recovered, ht₁, ht₂, ht₃, reachable, selectedRecord, recordEq, ?_, writer, fence, ?_⟩
  · rw [recordEq]; rfl
  · rw [admission]
    simp [state, lostDisk, disk0, put, ack, Bool.forall_bool]

end
#print axioms joint_nonempty_completion_loss_recovery
end ParaleanProtocol.Example
