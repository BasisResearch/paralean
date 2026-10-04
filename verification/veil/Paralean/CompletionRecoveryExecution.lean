import Paralean.CompletionRecovery

/-! One connected execution admits a two-name helper group and its dependent
target, accepts both receipts at another worker, durably completes the task,
then destroys a replica that acknowledged all three stored objects. -/
namespace ParaleanCompletionRecovery.Example
open ParaleanAdmission
noncomputable section Execution
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

abbrev Obj := StoredObject Bool Bool
abbrev Disk := ParaleanGroupComposition.DiskState Bool Obj Unit Unit
abbrev Registry := ParaleanGroups.CanonicalState Bool Bool (Fin 3) Bool
abbrev Delivery := ParaleanDelivery.CanonicalState Bool Bool Bool Bool Bool (Fin 3)
abbrev ModelState := ParaleanAdmission.State Bool Bool (Fin 3) Bool Bool Bool Bool Unit Unit

def groupTheory : ParaleanGroups.Theory Bool Bool (Fin 3) Bool where
  valid := fun _ => true
  deps := fun g h => g && !h
  ancestors := fun _ _ => false
  member := fun g x => if g then decide (x = 2) else decide (x ≠ 2)
  revisions := fun _ _ _ => false
  contents := fun S _ => S
  exportable := fun _ => true
  emptySnapshot := false

def storageTheory : Durability.Theory Bool Obj Unit Unit where
  memberW := fun _ _ => true
  memberR := fun r _ => r
  meet := fun _ _ => true

def deliveryTheory : ParaleanDelivery.Theory Bool Bool Bool Bool Bool (Fin 3) where
  packetRequest := id
  packetObject := id
  packetEpoch := fun m => if m then 2 else 1
  packetNode := fun _ => true
  receiptRequest := id
  receiptObject := id
  receiptEpoch := fun m => if m then 2 else 1
  receiptNode := fun _ => true
  intact := fun _ => true
  verified := fun _ => true
  valid := groupTheory.valid
  realizes := fun g r => decide (g = r)
  required := id
  deps := groupTheory.deps
  member := groupTheory.member
  contents := groupTheory.contents
  exportable := groupTheory.exportable

def theory : Theory Bool Bool (Fin 3) Bool Bool Bool Bool Unit Unit :=
  ⟨deliveryTheory, groupTheory, storageTheory⟩
def state (dl : Delivery) (rg : Registry) (disk : Disk) : ModelState := ⟨dl, ⟨rg, disk⟩⟩

def rg0 : Registry where
  published := fun _ => false
  known := fun _ _ => false
  pending := fun _ _ => false
  head := fun _ => false
  alive := fun _ => true
  online := fun _ => true
  stable := false
  clock := 0
  rank := fun _ => 0
def rgPreparedHelper : Registry :=
  { rg0 with pending := fun n g => !n && !g }
def rgHelper : Registry :=
  { rg0 with
    published := fun g => !g
    known := fun n g => !n && !g
    clock := 1 }
def rgPreparedTarget : Registry :=
  { rgHelper with pending := fun n g => !n && g }
def rgPublished : Registry :=
  { rg0 with
    published := fun _ => true
    known := fun n _ => !n
    clock := 2
    rank := fun g => if g then 1 else 0 }
def rgReceivedHelper : Registry :=
  { rgPublished with known := fun n g => !n || !g }
def rgReceived : Registry :=
  { rgPublished with known := fun _ _ => true }
def rgCommitted : Registry :=
  { rgReceived with head := id }

def dl0 : Delivery where
  flight := fun _ => false
  checked := fun _ _ => false
  current := fun _ => false
  epoch := fun _ => 0
  active := fun _ => false
  accepted := fun _ => false
  acceptedObject := fun _ => false
  done := fun _ => false
  result := fun _ => false
def dlStartedHelper : Delivery :=
  { dl0 with epoch := fun n => if n then 1 else 0, active := id }
def dlSentHelper : Delivery :=
  { dlStartedHelper with flight := fun m => !m }
def dlAcceptedHelper : Delivery :=
  { dlStartedHelper with checked := fun g r => !g && !r, accepted := id }
def dlStartedTarget : Delivery :=
  { dlAcceptedHelper with
    current := id
    epoch := fun n => if n then 2 else 0
    accepted := fun _ => false }
def dlSentTarget : Delivery := { dlStartedTarget with flight := id }
def dlAcceptedTarget : Delivery :=
  { dlStartedTarget with
    checked := fun g r => decide (g = r)
    accepted := id
    acceptedObject := id }
def dlDone : Delivery := { dlAcceptedTarget with done := id, result := id }

def disk0 : Disk := ⟨fun _ _ => false, fun _ => true, fun _ => false, fun _ => ()⟩
def put (disk : Disk) (r : Bool) (o : Obj) : Disk :=
  { disk with stored := fun n p => if r = n ∧ o = p then true else disk.stored n p }
def ack (disk : Disk) (o : Obj) : Disk :=
  { disk with acknowledged := fun p => if o = p then true else disk.acknowledged p }
def disk1 := put disk0 false (.payload false)
def disk2 := put disk1 true (.payload false)
def disk3 := ack disk2 (.payload false)
def disk4 := put disk3 false (.payload true)
def disk5 := put disk4 true (.payload true)
def disk6 := ack disk5 (.payload true)
def disk7 := put disk6 false (.manifest true)
def disk8 := put disk7 true (.manifest true)
def disk9 := ack disk8 (.manifest true)
def diskLost : Disk :=
  { disk9 with live := id, stored := fun r o => if r then disk9.stored r o else false }

theorem assumptions : Assumptions theory := by
  refine ⟨?_, ?_, ?_⟩
  · simp [DeliveryAssumptions, ParaleanDelivery.Assumptions, ParaleanDelivery.receipt_sound,
      theory, deliveryTheory, groupTheory, readFrom, instIsSubReaderOfRefl]
  · constructor
    · decide
    · simp [ParaleanGroupComposition.StorageAssumptions, Durability.Assumptions,
        Durability.assumption_0, protocolTheory, theory, storageTheory, readFrom, instIsSubReaderOfRefl]
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem group_steps :
    ParaleanGroups.GroupsInit groupTheory rg0 ∧
    ParaleanGroups.GroupsNext groupTheory rg0 (.prepare false false) rgPreparedHelper ∧
    ParaleanGroups.GroupsNext groupTheory rgPreparedHelper (.publish false false) rgHelper ∧
    ParaleanGroups.GroupsNext groupTheory rgHelper (.prepare false true) rgPreparedTarget ∧
    ParaleanGroups.GroupsNext groupTheory rgPreparedTarget (.publish false true) rgPublished ∧
    ParaleanGroups.GroupsNext groupTheory rgPublished (.receive true false) rgReceivedHelper ∧
    ParaleanGroups.GroupsNext groupTheory rgReceivedHelper (.receive true true) rgReceived ∧
    ParaleanGroups.GroupsNext groupTheory rgReceived (.commit true true) rgCommitted := by
  repeat' apply And.intro
  all_goals simp [ParaleanGroups.GroupsInit, ParaleanGroups.Init, ParaleanGroups.initializer.ext.tr,
    ParaleanGroups.GroupsNext, ParaleanGroups.Next, ParaleanGroups.NextAct,
    ParaleanGroups.prepare.ext.derived_eq, ParaleanGroups.publish.ext.derived_eq,
    ParaleanGroups.receive.ext.derived_eq, ParaleanGroups.commit.ext.derived_eq,
    ParaleanGroups.prepare.ext.tr, ParaleanGroups.publish.ext.tr,
    ParaleanGroups.receive.ext.tr, ParaleanGroups.commit.ext.tr,
    ParaleanGroups.buildable, ParaleanGroups.current, ParaleanGroups.isHead,
    groupTheory, rg0, rgPreparedHelper, rgHelper, rgPreparedTarget, rgPublished,
    rgReceivedHelper, rgReceived, rgCommitted, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation,
    Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]

theorem delivery_steps :
    ParaleanDelivery.Initial deliveryTheory dl0 ∧
    ParaleanDelivery.Step deliveryTheory dl0 (.start true false) dlStartedHelper ∧
    ParaleanDelivery.Step deliveryTheory dlStartedHelper (.send false) dlSentHelper ∧
    ParaleanDelivery.Step deliveryTheory dlSentHelper (.accept true false) dlAcceptedHelper ∧
    ParaleanDelivery.Step deliveryTheory dlAcceptedHelper (.start true true) dlStartedTarget ∧
    ParaleanDelivery.Step deliveryTheory dlStartedTarget (.send true) dlSentTarget ∧
    ParaleanDelivery.Step deliveryTheory dlSentTarget (.accept true true) dlAcceptedTarget ∧
    ParaleanDelivery.Step deliveryTheory dlAcceptedTarget (.finish true true) dlDone := by
  repeat' apply And.intro
  all_goals simp [ParaleanDelivery.Initial, ParaleanDelivery.Init, ParaleanDelivery.initializer.ext.tr,
    ParaleanDelivery.Step, ParaleanDelivery.Next, ParaleanDelivery.NextAct,
    ParaleanDelivery.start.ext.derived_eq, ParaleanDelivery.send.ext.derived_eq,
    ParaleanDelivery.accept.ext.derived_eq, ParaleanDelivery.finish.ext.derived_eq,
    ParaleanDelivery.start.ext.tr, ParaleanDelivery.send.ext.tr,
    ParaleanDelivery.accept.ext.tr, ParaleanDelivery.finish.ext.tr, ParaleanDelivery.ready,
    deliveryTheory, groupTheory, dl0, dlStartedHelper, dlSentHelper, dlAcceptedHelper,
    dlStartedTarget, dlSentTarget, dlAcceptedTarget, dlDone, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanDelivery.canonicalFieldRep, Veil.canonicalFieldRepresentation,
    Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]

theorem put_step (disk : Disk) (r : Bool) (o : Obj) (hl : disk.live r = true) :
    ParaleanGroupComposition.StorageNext storageTheory disk (.Put r o) (put disk r o) := by
  simp only [ParaleanGroupComposition.StorageNext, Durability.Next, Durability.NextAct,
    Durability.Put.ext.derived_eq]
  dsimp [Durability.Put.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanGroupComposition.diskFieldRep,
    Veil.canonicalFieldRepresentation]
  refine ⟨hl, ?_⟩
  simp [put, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp, funext_iff]

theorem ack_step (disk : Disk) (o : Obj)
    (hq : ∀ r, disk.live r = true ∧ disk.stored r o = true) :
    ParaleanGroupComposition.StorageNext storageTheory disk (.Ack o ()) (ack disk o) := by
  simp only [ParaleanGroupComposition.StorageNext, Durability.Next, Durability.NextAct,
    Durability.Ack.ext.derived_eq]
  dsimp [Durability.Ack.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanGroupComposition.diskFieldRep,
    Veil.canonicalFieldRepresentation]
  refine ⟨fun r _ => hq r, ?_⟩
  simp [ack, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp, funext_iff]

theorem lose_step :
    ParaleanGroupComposition.StorageNext storageTheory disk9 (.Lose false) diskLost := by
  simp only [ParaleanGroupComposition.StorageNext, Durability.Next, Durability.NextAct,
    Durability.Lose.ext.derived_eq]
  dsimp [Durability.Lose.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanGroupComposition.diskFieldRep,
    Veil.canonicalFieldRepresentation]
  simp [storageTheory, diskLost, disk9, disk8, disk7, disk6, disk5, disk4,
    disk3, disk2, disk1, disk0, put, ack, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]

abbrev CState := ParaleanCompletionRecovery.State Bool Bool (Fin 3) Bool Bool Bool Bool Unit Bool Unit Bool Unit Unit

def recoveryTheory : ParaleanRecovery.Theory Bool Unit Bool Bool (Fin 3) Bool Unit where
  tokenRank := fun t => if t then 1 else 0
  identity := ()
  recordWorkspace := fun _ => ()
  image := id
  causalRank := fun _ => 0
  parent := fun _ _ => false
  ancestor := fun _ _ => false
  valid := groupTheory.valid
  deps := groupTheory.deps
  member := groupTheory.member
  contents := groupTheory.contents
  exportable := groupTheory.exportable
  decoded := fun _ => id
  ready := fun _ => id

def encode (c : Bool) : Nat := if c then 1 else 0

def rec0 : ParaleanRecovery.CanonicalState Bool Unit Bool Bool (Fin 3) Bool Unit :=
  ⟨fun _ => false, fun _ => false, fun _ => false, fun _ => false,
    false, false, false, false, false, true, 0⟩
def recCommitted := { rec0 with committed := id, durableAck := id }
def compose (ad : ModelState) : CState := ⟨ad, rec0⟩

theorem lift_unfinished {ad ad' : ModelState} (ht : ParaleanAdmission.Next theory ad ad')
    (hfalse : ∀ n, ad'.delivery.done n = false) :
    ParaleanCompletionRecovery.Next theory recoveryTheory encode (compose ad) (compose ad') := by
  cases ht with
  | control l hc hd => exact .admission (.control l hc hd) rfl
  | protocol hp =>
    cases hp with
    | registry l hc hg hd => exact .admission (.registry l hc hg hd) rfl
    | storage l hd => exact .coupled (.protocol (.storage l hd)) rfl rfl (.storage l hd (by cases l <;> trivial))
    | stutter => exact .admission .stutter rfl
  | accept n m hd hp =>
    have h := ParaleanAdmission.AcceptStep.paired hd hp
    cases hp with
    | receive hg => exact .admission (.accept n m h) rfl
    | duplicate hk => exact .admission (.accept n m h) rfl
  | finish n S hd hp =>
    have he := ParaleanDelivery.finish_effect theory.delivery _ _ n S hd
    have hf := hfalse n
    rw [he.1] at hf
    contradiction
  | crash n hd hp => exact .admission (.crash n (.paired hd hp)) rfl
  | stutter => exact .admission .stutter rfl

inductive PipelinePath : ModelState → ModelState → Prop where
  | refl {s} : PipelinePath s s
  | append {s t u} : PipelinePath s t →
      ParaleanCompletionRecovery.Next theory recoveryTheory encode (compose t) (compose u) → PipelinePath s u

theorem PipelinePath.snoc {s t u : ModelState} (path : PipelinePath s t)
    (ht : ParaleanAdmission.Next theory t u)
    (hf : ∀ n, u.delivery.done n = false := by
      intro n; simp [state, dl0, dlStartedHelper, dlSentHelper, dlAcceptedHelper,
        dlStartedTarget, dlSentTarget, dlAcceptedTarget]) : PipelinePath s u :=
  .append path (lift_unfinished ht hf)

theorem PipelinePath.reachable {s t : ModelState}
    (hr : ParaleanCompletionRecovery.Reachable theory recoveryTheory encode (compose s))
    (path : PipelinePath s t) :
    ParaleanCompletionRecovery.Reachable theory recoveryTheory encode (compose t) := by
  induction path with
  | refl => exact hr
  | append _ ht ih => exact .step ih ht

abbrev initial := state dl0 rg0 disk0
abbrev beforeHelper := state dlSentHelper rgPublished disk6
abbrev afterHelper := state dlAcceptedHelper rgReceivedHelper disk6
abbrev beforeTarget := state dlSentTarget rgReceivedHelper disk6
abbrev afterTarget := state dlAcceptedTarget rgReceived disk6
abbrev beforeFinish := state dlAcceptedTarget rgReceived disk9
abbrev completed := state dlDone rgCommitted disk9
abbrev failed := state dlDone rgCommitted diskLost

theorem initial_valid : ParaleanAdmission.Initial theory initial := by
  refine ⟨delivery_steps.1, group_steps.1, ?_⟩
  simp [ParaleanGroupComposition.StorageInit, Durability.Init, Durability.initializer.ext.tr,
    initial, state, disk0, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanGroupComposition.diskFieldRep,
    Veil.canonicalFieldRepresentation, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

theorem prepare_and_send : PipelinePath initial beforeHelper := by
  obtain ⟨_, hprepareHelper, hpublishHelper, hprepareTarget, hpublishTarget, _, _, _⟩ := group_steps
  obtain ⟨_, hstart, hsend, _, _, _, _, _⟩ := delivery_steps
  have h0 : PipelinePath initial initial := .refl
  have h1 : PipelinePath initial (state dl0 rg0 disk1) := PipelinePath.snoc h0 (.protocol (.storage (.Put false (.payload false))
    (put_step disk0 false (.payload false) rfl)))
  have h2 : PipelinePath initial (state dl0 rg0 disk2) := PipelinePath.snoc h1 (.protocol (.storage (.Put true (.payload false))
    (put_step disk1 true (.payload false) rfl)))
  have h3 : PipelinePath initial (state dl0 rg0 disk3) := PipelinePath.snoc h2 (.protocol (.storage (.Ack (.payload false) ())
    (ack_step disk2 (.payload false) (by intro r; cases r <;> simp [disk2, disk1, disk0, put]))))
  have h4 : PipelinePath initial (state dl0 rgPreparedHelper disk3) := PipelinePath.snoc h3 (.protocol (.registry (.prepare false false) trivial hprepareHelper trivial))
  have h5 : PipelinePath initial (state dl0 rgHelper disk3) := PipelinePath.snoc h4 (.protocol (.registry (.publish false false) trivial hpublishHelper
    (by simp [ParaleanGroupComposition.Guard, protocolTheory, disk3, ack])))
  have h6 : PipelinePath initial (state dl0 rgHelper disk4) := PipelinePath.snoc h5 (.protocol (.storage (.Put false (.payload true))
    (put_step disk3 false (.payload true) rfl)))
  have h7 : PipelinePath initial (state dl0 rgHelper disk5) := PipelinePath.snoc h6 (.protocol (.storage (.Put true (.payload true))
    (put_step disk4 true (.payload true) rfl)))
  have h8 : PipelinePath initial (state dl0 rgHelper disk6) := PipelinePath.snoc h7 (.protocol (.storage (.Ack (.payload true) ())
    (ack_step disk5 (.payload true) (by intro r; cases r <;> simp [disk5, disk4, disk3, disk2, disk1, disk0, put, ack]))))
  have h9 : PipelinePath initial (state dl0 rgPreparedTarget disk6) := PipelinePath.snoc h8 (.protocol (.registry (.prepare false true) trivial hprepareTarget trivial))
  have h10 : PipelinePath initial (state dl0 rgPublished disk6) := PipelinePath.snoc h9 (.protocol (.registry (.publish false true) trivial hpublishTarget
    (by simp [ParaleanGroupComposition.Guard, protocolTheory, disk6, ack])))
  have h11 : PipelinePath initial (state dlStartedHelper rgPublished disk6) := PipelinePath.snoc h10 (.control (.start true false) trivial hstart)
  exact PipelinePath.snoc h11 (.control (.send false) trivial hsend)

theorem accept_helper : AcceptStep theory true false beforeHelper afterHelper :=
  .paired delivery_steps.2.2.2.1 (.receive group_steps.2.2.2.2.2.1)

theorem between_receipts : PipelinePath afterHelper beforeTarget := by
  have h0 : PipelinePath afterHelper afterHelper := .refl
  have h1 : PipelinePath afterHelper (state dlStartedTarget rgReceivedHelper disk6) :=
    PipelinePath.snoc h0 (.control (.start true true) trivial delivery_steps.2.2.2.2.1)
  exact PipelinePath.snoc h1 (.control (.send true) trivial delivery_steps.2.2.2.2.2.1)

theorem accept_target : AcceptStep theory true true beforeTarget afterTarget :=
  .paired delivery_steps.2.2.2.2.2.2.1 (.receive group_steps.2.2.2.2.2.2.1)

theorem store_manifest : PipelinePath afterTarget beforeFinish := by
  have h0 : PipelinePath afterTarget afterTarget := .refl
  have h1 : PipelinePath afterTarget (state dlAcceptedTarget rgReceived disk7) := PipelinePath.snoc h0 (.protocol (.storage (.Put false (.manifest true))
    (put_step disk6 false (.manifest true) rfl)))
  have h2 : PipelinePath afterTarget (state dlAcceptedTarget rgReceived disk8) := PipelinePath.snoc h1 (.protocol (.storage (.Put true (.manifest true))
    (put_step disk7 true (.manifest true) rfl)))
  exact PipelinePath.snoc h2 (.protocol (.storage (.Ack (.manifest true) ())
    (ack_step disk8 (.manifest true) (by
      intro r
      cases r <;> simp [disk8, disk7, disk6, disk5, disk4, disk3, disk2, disk1, disk0, put, ack]))))

theorem finish : ParaleanAdmission.FinishStep theory true true beforeFinish completed := by
  refine ParaleanAdmission.FinishStep.paired (th := theory) ?_ ?_
  · exact delivery_steps.2.2.2.2.2.2.2
  · exact .registry group_steps.2.2.2.2.2.2.2 (by
      simp [ParaleanGroupComposition.Guard, protocolTheory, disk9, ack])

theorem destroy_replica : ParaleanAdmission.Next theory completed failed :=
  .protocol (.storage (.Lose false) lose_step)


def diskCatalog1 := put disk9 false (.catalog 1)
def diskCatalog2 := put diskCatalog1 true (.catalog 1)
def diskCatalog := ack diskCatalog2 (.catalog 1)
def beforeCatalog : CState := ⟨state dlAcceptedTarget rgReceived diskCatalog2, rec0⟩
def catalogCommitted : CState := ⟨state dlAcceptedTarget rgReceived diskCatalog, recCommitted⟩
def completedWithCatalog : CState := ⟨state dlDone rgCommitted diskCatalog, recCommitted⟩
def diskCatalogLost : Disk :=
  { diskCatalog with live := id, stored := fun r o => if r then diskCatalog.stored r o else false }
def recForgotten := { recCommitted with writer := false }
def afterFailures : CState := ⟨state dlDone rgCommitted diskCatalogLost, recForgotten⟩

theorem recovery_assumptions : ParaleanRecovery.CoupledAssumptions
    (ParaleanRecovery.ofAdmission theory recoveryTheory encode) := by
  refine ⟨assumptions.2.1.2, ?_, ⟨rfl, rfl, rfl, rfl, rfl⟩,
    ParaleanRecovery.ofAdmission_objects_separate theory recoveryTheory encode ?_⟩
  · decide
  · intro a b he; cases a <;> cases b <;> simp [encode] at he ⊢

theorem recovery_initial : ParaleanRecovery.RecoveryInit recoveryTheory rec0 := by
  simp [ParaleanRecovery.RecoveryInit, ParaleanRecovery.Init, ParaleanRecovery.initializer.ext.tr,
    rec0, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanRecovery.canonicalFieldRep,
    Veil.canonicalFieldRepresentation, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

theorem before_finish_reachable : ParaleanCompletionRecovery.Reachable theory recoveryTheory encode (compose beforeFinish) := by
  have h0 : ParaleanCompletionRecovery.Reachable theory recoveryTheory encode (compose initial) :=
    .initial ⟨initial_valid, recovery_initial⟩
  have h1 := prepare_and_send.reachable h0
  have h2 := ParaleanCompletionRecovery.Reachable.step h1
    (lift_unfinished (accept_helper.to_next theory true false _ _) (by intro n; rfl))
  have h3 := between_receipts.reachable h2
  have h4 := ParaleanCompletionRecovery.Reachable.step h3
    (lift_unfinished (accept_target.to_next theory true true _ _) (by intro n; rfl))
  exact store_manifest.reachable h4

theorem catalog_commit : ParaleanCompletionRecovery.Next theory recoveryTheory encode beforeCatalog catalogCommitted := by
  have hr : ParaleanRecovery.RecoveryNext recoveryTheory rec0 (.commit true false) recCommitted := by
    simp [ParaleanRecovery.RecoveryNext, ParaleanRecovery.Next, ParaleanRecovery.NextAct,
      ParaleanRecovery.commit.ext.derived_eq, ParaleanRecovery.commit.ext.tr,
      ParaleanRecovery.buildable, recoveryTheory, groupTheory, rec0, recCommitted,
      getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
      instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanRecovery.canonicalFieldRep,
      Veil.canonicalFieldRepresentation, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]
  have hd := ack_step diskCatalog2 (.catalog 1) (by
    intro r; cases r <;> simp [diskCatalog2, diskCatalog1, put, disk9, disk8, disk7, disk6, disk5, disk4, disk3, disk2, disk1, disk0, ack])
  exact .coupled (.protocol (.storage (.Ack (.catalog 1) ()) hd)) rfl rfl
    (.commit true false () hr hd (by simp [state, recoveryTheory, theory, ParaleanRecovery.ofAdmission, ParaleanAdmission.protocolTheory, diskCatalog2, diskCatalog1, put, disk9, disk8, disk7, disk6, disk5, disk4, disk3, disk2, disk1, disk0, ack])
      (by intro d hd; cases d <;> simp [state, recoveryTheory, theory, ParaleanRecovery.ofAdmission, ParaleanAdmission.protocolTheory,
        diskCatalog2, diskCatalog1, put, disk9, disk8, disk7, disk6, disk5,
        disk4, disk3, disk2, disk1, disk0, ack]))

theorem catalog_before_completion : ParaleanCompletionRecovery.Reachable theory recoveryTheory encode catalogCommitted := by
  have h1 : ParaleanCompletionRecovery.Reachable theory recoveryTheory encode
      ⟨state dlAcceptedTarget rgReceived diskCatalog1, rec0⟩ :=
    .step before_finish_reachable
      (.coupled (.protocol (.storage (.Put false (.catalog 1))
        (put_step disk9 false (.catalog 1) rfl))) rfl rfl
        (.storage (.Put false (.catalog 1)) (put_step disk9 false (.catalog 1) rfl) trivial))
  have h2 : ParaleanCompletionRecovery.Reachable theory recoveryTheory encode beforeCatalog :=
    .step h1 (.coupled (.protocol (.storage (.Put true (.catalog 1))
      (put_step diskCatalog1 true (.catalog 1) rfl))) rfl rfl
      (.storage (.Put true (.catalog 1)) (put_step diskCatalog1 true (.catalog 1) rfl) trivial))
  exact .step h2 catalog_commit

theorem guarded_finish : ParaleanCompletionRecovery.FinishStep theory recoveryTheory true true true
    catalogCommitted completedWithCatalog := by
  refine .guarded ?_ rfl rfl rfl
  exact .paired delivery_steps.2.2.2.2.2.2.2
    (.registry group_steps.2.2.2.2.2.2.2 (by
      simp [ParaleanGroupComposition.Guard, protocolTheory, diskCatalog, ack, diskCatalog2,
        diskCatalog1, put, disk9]))

theorem destroy_catalog_replica : ParaleanGroupComposition.StorageNext storageTheory diskCatalog
    (.Lose false) diskCatalogLost := by
  simp only [ParaleanGroupComposition.StorageNext, Durability.Next, Durability.NextAct,
    Durability.Lose.ext.derived_eq]
  dsimp [Durability.Lose.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanGroupComposition.diskFieldRep,
    Veil.canonicalFieldRepresentation]
  simp [storageTheory, diskCatalogLost, diskCatalog, diskCatalog2, diskCatalog1,
    disk9, disk8, disk7, disk6, disk5, disk4, disk3, disk2, disk1, disk0, put, ack,
    Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
    funext_iff, Bool.forall_bool, Bool.exists_bool]

def recScanned := { recCommitted with known := id, scanned := true }
def recReconstructed := { recScanned with heads := id, reconstructed := true }
def recSelected := { recReconstructed with selected := true, selectedRecord := true }
def locallySelected : CState := ⟨state dlDone rgCommitted diskCatalog, recSelected⟩

local instance : delta% (ParaleanRecovery.reconstruct._veil_dec_type_0
  (record := Bool) (workspace := Unit) (snapshot := Bool)
  (decl := Bool) (name := Fin 3) (token := Bool) (scan := Unit)
  (χ := ParaleanRecovery.CanonicalRep Bool Unit Bool Bool (Fin 3) Bool Unit)) :=
  fun _ _ _ => Classical.propDecidable _
local instance : delta% (ParaleanRecovery.reconstruct._veil_dec_type_1
  (record := Bool) (workspace := Unit) (snapshot := Bool)
  (decl := Bool) (name := Fin 3) (token := Bool) (scan := Unit)
  (χ := ParaleanRecovery.CanonicalRep Bool Unit Bool Bool (Fin 3) Bool Unit)) :=
  fun _ _ => Classical.propDecidable _

theorem local_selection_steps :
    ParaleanRecovery.RecoveryNext recoveryTheory recCommitted (.enumerate ()) recScanned ∧
    ParaleanRecovery.RecoveryNext recoveryTheory recScanned .reconstruct recReconstructed ∧
    ParaleanRecovery.RecoveryNext recoveryTheory recReconstructed (.historical true) recSelected := by
  repeat' apply And.intro
  all_goals simp [ParaleanRecovery.RecoveryNext, ParaleanRecovery.Next, ParaleanRecovery.NextAct,
    ParaleanRecovery.enumerate.ext.derived_eq, ParaleanRecovery.reconstruct.ext.derived_eq,
    ParaleanRecovery.historical.ext.derived_eq, ParaleanRecovery.enumerate.ext.tr,
    ParaleanRecovery.reconstruct.ext.tr, ParaleanRecovery.historical.ext.tr,
    ParaleanRecovery.admissible, ParaleanRecovery.buildable, recScanned, recReconstructed,
    recSelected, recCommitted, rec0, recoveryTheory, groupTheory, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanRecovery.canonicalFieldRep, Veil.canonicalFieldRepresentation,
    Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
    funext_iff, Bool.forall_bool, Bool.exists_bool]

theorem forget_desktop : ParaleanRecovery.RecoveryNext recoveryTheory recCommitted .loseDesktop recForgotten := by
  simp [ParaleanRecovery.RecoveryNext, ParaleanRecovery.Next, ParaleanRecovery.NextAct,
    ParaleanRecovery.loseDesktop.ext.derived_eq, ParaleanRecovery.loseDesktop.ext.tr,
    recForgotten, recCommitted, rec0, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanRecovery.canonicalFieldRep,
    Veil.canonicalFieldRepresentation, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

theorem completion_then_actual_losses :
    ParaleanCompletionRecovery.Reachable theory recoveryTheory encode completedWithCatalog ∧
    ParaleanCompletionRecovery.FailurePath theory recoveryTheory encode completedWithCatalog afterFailures ∧
    ParaleanCompletionRecovery.Reachable theory recoveryTheory encode afterFailures ∧
    afterFailures.admission.delivery.done true = true ∧
    afterFailures.admission.delivery.result true = true ∧
    (∀ c, afterFailures.recovery.known c = false) ∧ afterFailures.recovery.writer = false ∧
    afterFailures.admission.protocol.storage.live false = false ∧
    afterFailures.admission.protocol.storage.live true = true ∧
    afterFailures.admission.protocol.storage.stored true (.catalog 1) = true ∧
    (∀ g, groupTheory.contents true g = true) := by
  have hc := ParaleanCompletionRecovery.Reachable.step catalog_before_completion (.finish true true true guarded_finish)
  have hp : ParaleanCompletionRecovery.FailurePath theory recoveryTheory encode completedWithCatalog afterFailures :=
    .snoc (.snoc .refl (.storage false destroy_catalog_replica)) (.desktop forget_desktop)
  exact ⟨hc, hp, hp.reachable theory recoveryTheory encode hc,
    rfl, rfl, by intro c; rfl, rfl, rfl, rfl, by simp [afterFailures, state,
      diskCatalogLost, diskCatalog, diskCatalog2, diskCatalog1, put, ack], by intro g; rfl⟩


/-- The lost ID was present before forgetting; this is not an already-empty cache. -/
theorem selected_identifier_then_losses :
    ParaleanCompletionRecovery.Reachable theory recoveryTheory encode locallySelected ∧
    locallySelected.recovery.selectedRecord = true ∧ locallySelected.recovery.known true = true ∧
    ParaleanCompletionRecovery.FailurePath theory recoveryTheory encode locallySelected afterFailures ∧
    afterFailures.recovery.selectedRecord = false ∧ (∀ c, afterFailures.recovery.known c = false) := by
  have hr := completion_then_actual_losses.1
  have h₁ : ParaleanCompletionRecovery.Next theory recoveryTheory encode completedWithCatalog
      ⟨state dlDone rgCommitted diskCatalog, recScanned⟩ := by
    refine .coupled .stutter rfl rfl (.recovery (.enumerate ()) ?_ ?_ local_selection_steps.1)
    · intro c epoch h; cases h
    · intro v h c hc
      cases v
      cases c
      · simp [ParaleanRecovery.ofAdmission, recoveryTheory] at hc
      · simp [ParaleanRecovery.StorageReady, ParaleanRecovery.ofAdmission, protocolTheory,
          theory, recoveryTheory, groupTheory, encode, state, diskCatalog, diskCatalog2, diskCatalog1,
          disk9, disk8, disk7, disk6, disk5, disk4, disk3, disk2, disk1, disk0, put, ack,
          Bool.forall_bool]
  have h₂ : ParaleanCompletionRecovery.Next theory recoveryTheory encode
      ⟨state dlDone rgCommitted diskCatalog, recScanned⟩
      ⟨state dlDone rgCommitted diskCatalog, recReconstructed⟩ :=
    .coupled .stutter rfl rfl (.recovery .reconstruct (by intro c epoch h; cases h)
      (by intro v h; cases h) local_selection_steps.2.1)
  have h₃ : ParaleanCompletionRecovery.Next theory recoveryTheory encode
      ⟨state dlDone rgCommitted diskCatalog, recReconstructed⟩ locallySelected :=
    .coupled .stutter rfl rfl (.recovery (.historical true) (by intro c epoch h; cases h)
      (by intro v h; cases h) local_selection_steps.2.2)
  have hl : ParaleanRecovery.RecoveryNext recoveryTheory recSelected .loseDesktop recForgotten := by
    simp [ParaleanRecovery.RecoveryNext, ParaleanRecovery.Next, ParaleanRecovery.NextAct,
      ParaleanRecovery.loseDesktop.ext.derived_eq, ParaleanRecovery.loseDesktop.ext.tr,
      recSelected, recReconstructed, recScanned, recForgotten, recCommitted, rec0,
      getFrom, setIn, readFrom, Veil.FieldRepresentation.get, instIsSubStateOfRefl,
      instIsSubReaderOfRefl, ParaleanRecovery.canonicalFieldRep, Veil.canonicalFieldRepresentation,
      Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp]
  exact ⟨.step (.step (.step hr h₁) h₂) h₃, rfl, rfl,
    .snoc (.snoc .refl (.storage false destroy_catalog_replica)) (.desktop hl), rfl,
    by intro c; rfl⟩

theorem physical_scan : ParaleanRecovery.PhysicalScan
    (ParaleanRecovery.ofAdmission theory recoveryTheory encode) afterFailures.admission.protocol.storage () () := by
  intro c
  cases c <;> simp [ParaleanRecovery.PhysicalScan, ParaleanRecovery.QuorumCatalog,
    ParaleanRecovery.ofAdmission, protocolTheory, theory, recoveryTheory, encode,
    afterFailures, state, storageTheory, diskCatalogLost, diskCatalog, diskCatalog2,
    diskCatalog1, disk9, disk8, disk7, disk6, disk5, disk4, disk3, disk2, disk1, disk0,
    put, ack, Bool.exists_bool]

theorem ready_scan : ParaleanRecovery.ReadyScan
    (ParaleanRecovery.ofAdmission theory recoveryTheory encode) afterFailures.admission.protocol.storage () := by
  intro c
  cases c <;> simp [ParaleanRecovery.StorageReady, ParaleanRecovery.ofAdmission,
    protocolTheory, theory, recoveryTheory, groupTheory, encode, afterFailures, state,
    diskCatalogLost, diskCatalog, diskCatalog2, diskCatalog1, disk9, disk8, disk7,
    disk6, disk5, disk4, disk3, disk2, disk1, disk0, put, ack, Bool.forall_bool]

/-- One nonempty run admits two helper names and a dependent target, acknowledges
the catalogue before completion, destroys an acknowledging replica, erases all
local record IDs, and recovers the exact completed snapshot from remaining bytes. -/
theorem nonempty_completion_loss_recovery :
    ParaleanCompletionRecovery.Reachable theory recoveryTheory encode afterFailures ∧
    (∀ c, afterFailures.recovery.known c = false) ∧ afterFailures.recovery.writer = false ∧
    afterFailures.admission.delivery.done true = true ∧
    afterFailures.admission.delivery.checked true true = true ∧
    deliveryTheory.required true = true ∧ deliveryTheory.realizes true true = true ∧
    groupTheory.deps true false = true ∧ groupTheory.member false 0 = true ∧
    groupTheory.member false 1 = true ∧ groupTheory.member true 2 = true ∧
    ∃ s₁ s₂ recovered, ParaleanCompletionRecovery.Next theory recoveryTheory encode afterFailures s₁ ∧
      ParaleanCompletionRecovery.Next theory recoveryTheory encode s₁ s₂ ∧
      ParaleanCompletionRecovery.Next theory recoveryTheory encode s₂ recovered ∧
      ParaleanCompletionRecovery.Reachable theory recoveryTheory encode recovered ∧
      recovered.recovery.selected = true ∧ recovered.recovery.selectedRecord = true ∧
      recoveryTheory.image recovered.recovery.selectedRecord = true ∧
      recovered.recovery.writer = false ∧ recovered.recovery.fence = 0 ∧
      recovered.admission.protocol.storage.live false = false ∧
      recovered.admission.protocol.storage.live true = true ∧
      recovered.admission.protocol.storage.stored true (.catalog 1) = true ∧
      recovered.admission.protocol.storage.stored true (.manifest true) = true ∧
      (∀ g, recovered.admission.protocol.storage.stored true (.payload g) = true) := by
  have hr := selected_identifier_then_losses.2.2.2.1.reachable theory recoveryTheory encode
    selected_identifier_then_losses.1
  obtain ⟨s₁, s₂, recovered, ht₁, ht₂, ht₃, reachable, selected, recordEq, writer, fence, disk⟩ :=
    ParaleanCompletionRecovery.physical_recovery_extends_composed_prefix theory recoveryTheory encode
      assumptions recovery_assumptions hr () (by intro r h; cases r <;> simp [theory, storageTheory] at h ⊢; rfl)
      () physical_scan ready_scan true rfl
  refine ⟨hr, by intro c; rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    s₁, s₂, recovered, ht₁, ht₂, ht₃, reachable, selected, recordEq, ?_, writer, fence, ?_⟩
  · rw [recordEq]; rfl
  · rw [disk]
    simp [afterFailures, state, diskCatalogLost, diskCatalog, diskCatalog2, diskCatalog1,
      disk9, disk8, disk7, disk6, disk5, disk4, disk3, disk2, disk1, disk0, put, ack, Bool.forall_bool]

#print axioms selected_identifier_then_losses
#print axioms nonempty_completion_loss_recovery
#print axioms completion_then_actual_losses
end Execution
end ParaleanCompletionRecovery.Example
