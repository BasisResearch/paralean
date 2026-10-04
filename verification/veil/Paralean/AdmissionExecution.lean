import Paralean.Admission

/-! One connected execution admits a two-name helper group and its dependent
target, accepts both receipts at another worker, durably completes the task,
then destroys a replica that acknowledged all three stored objects. -/
namespace ParaleanAdmission
noncomputable section Execution
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

private abbrev Obj := StoredObject Bool Bool
private abbrev Disk := ParaleanGroupComposition.DiskState Bool Obj Unit Unit
private abbrev Registry := ParaleanGroups.CanonicalState Bool Bool (Fin 3) Bool
private abbrev Delivery := ParaleanDelivery.CanonicalState Bool Bool Bool Bool Bool (Fin 3)
private abbrev ModelState := State Bool Bool (Fin 3) Bool Bool Bool Bool Unit Unit

private def groupTheory : ParaleanGroups.Theory Bool Bool (Fin 3) Bool where
  valid := fun _ => true
  deps := fun g h => g && !h
  ancestors := fun _ _ => false
  member := fun g x => if g then decide (x = 2) else decide (x ≠ 2)
  revisions := fun _ _ _ => false
  contents := fun S _ => S
  exportable := fun _ => true
  emptySnapshot := false

private def storageTheory : Durability.Theory Bool Obj Unit Unit where
  memberW := fun _ _ => true
  memberR := fun r _ => r
  meet := fun _ _ => true

private def deliveryTheory : ParaleanDelivery.Theory Bool Bool Bool Bool Bool (Fin 3) where
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

private def theory : Theory Bool Bool (Fin 3) Bool Bool Bool Bool Unit Unit :=
  ⟨deliveryTheory, groupTheory, storageTheory⟩
private def state (dl : Delivery) (rg : Registry) (disk : Disk) : ModelState := ⟨dl, ⟨rg, disk⟩⟩

private def rg0 : Registry where
  published := fun _ => false
  known := fun _ _ => false
  pending := fun _ _ => false
  head := fun _ => false
  alive := fun _ => true
  online := fun _ => true
  stable := false
  clock := 0
  rank := fun _ => 0
private def rgPreparedHelper : Registry :=
  { rg0 with pending := fun n g => !n && !g }
private def rgHelper : Registry :=
  { rg0 with
    published := fun g => !g
    known := fun n g => !n && !g
    clock := 1 }
private def rgPreparedTarget : Registry :=
  { rgHelper with pending := fun n g => !n && g }
private def rgPublished : Registry :=
  { rg0 with
    published := fun _ => true
    known := fun n _ => !n
    clock := 2
    rank := fun g => if g then 1 else 0 }
private def rgReceivedHelper : Registry :=
  { rgPublished with known := fun n g => !n || !g }
private def rgReceived : Registry :=
  { rgPublished with known := fun _ _ => true }
private def rgCommitted : Registry :=
  { rgReceived with head := id }

private def dl0 : Delivery where
  flight := fun _ => false
  checked := fun _ _ => false
  current := fun _ => false
  epoch := fun _ => 0
  active := fun _ => false
  accepted := fun _ => false
  acceptedObject := fun _ => false
  done := fun _ => false
  result := fun _ => false
private def dlStartedHelper : Delivery :=
  { dl0 with epoch := fun n => if n then 1 else 0, active := id }
private def dlSentHelper : Delivery :=
  { dlStartedHelper with flight := fun m => !m }
private def dlAcceptedHelper : Delivery :=
  { dlStartedHelper with checked := fun g r => !g && !r, accepted := id }
private def dlStartedTarget : Delivery :=
  { dlAcceptedHelper with
    current := id
    epoch := fun n => if n then 2 else 0
    accepted := fun _ => false }
private def dlSentTarget : Delivery := { dlStartedTarget with flight := id }
private def dlAcceptedTarget : Delivery :=
  { dlStartedTarget with
    checked := fun g r => decide (g = r)
    accepted := id
    acceptedObject := id }
private def dlDone : Delivery := { dlAcceptedTarget with done := id, result := id }

private def disk0 : Disk := ⟨fun _ _ => false, fun _ => true, fun _ => false, fun _ => ()⟩
private def put (disk : Disk) (r : Bool) (o : Obj) : Disk :=
  { disk with stored := fun n p => if r = n ∧ o = p then true else disk.stored n p }
private def ack (disk : Disk) (o : Obj) : Disk :=
  { disk with acknowledged := fun p => if o = p then true else disk.acknowledged p }
private def disk1 := put disk0 false (.payload false)
private def disk2 := put disk1 true (.payload false)
private def disk3 := ack disk2 (.payload false)
private def disk4 := put disk3 false (.payload true)
private def disk5 := put disk4 true (.payload true)
private def disk6 := ack disk5 (.payload true)
private def disk7 := put disk6 false (.manifest true)
private def disk8 := put disk7 true (.manifest true)
private def disk9 := ack disk8 (.manifest true)
private def diskLost : Disk :=
  { disk9 with live := id, stored := fun r o => if r then disk9.stored r o else false }

private theorem assumptions : Assumptions theory := by
  refine ⟨?_, ?_, ?_⟩
  · simp [DeliveryAssumptions, ParaleanDelivery.Assumptions, ParaleanDelivery.receipt_sound,
      theory, deliveryTheory, groupTheory, readFrom, instIsSubReaderOfRefl]
  · constructor
    · decide
    · simp [ParaleanGroupComposition.StorageAssumptions, Durability.Assumptions,
        Durability.assumption_0, protocolTheory, theory, storageTheory, readFrom, instIsSubReaderOfRefl]
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem group_steps :
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

private theorem delivery_steps :
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

private theorem put_step (disk : Disk) (r : Bool) (o : Obj) (hl : disk.live r = true) :
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

private theorem ack_step (disk : Disk) (o : Obj)
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

private theorem lose_step :
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

private inductive PipelinePath : ModelState → ModelState → Prop where
  | refl {s} : PipelinePath s s
  | snoc {s t u} : PipelinePath s t → Next theory t u → PipelinePath s u

private theorem PipelinePath.reachable {s t : ModelState}
    (hr : Reachable theory s) (path : PipelinePath s t) : Reachable theory t := by
  induction path with
  | refl => exact hr
  | snoc _ ht ih => exact .step ih ht

private abbrev initial := state dl0 rg0 disk0
private abbrev beforeHelper := state dlSentHelper rgPublished disk6
private abbrev afterHelper := state dlAcceptedHelper rgReceivedHelper disk6
private abbrev beforeTarget := state dlSentTarget rgReceivedHelper disk6
private abbrev afterTarget := state dlAcceptedTarget rgReceived disk6
private abbrev beforeFinish := state dlAcceptedTarget rgReceived disk9
private abbrev completed := state dlDone rgCommitted disk9
private abbrev failed := state dlDone rgCommitted diskLost

private theorem initial_valid : Initial theory initial := by
  refine ⟨delivery_steps.1, group_steps.1, ?_⟩
  simp [ParaleanGroupComposition.StorageInit, Durability.Init, Durability.initializer.ext.tr,
    initial, state, disk0, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanGroupComposition.diskFieldRep,
    Veil.canonicalFieldRepresentation, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

private theorem prepare_and_send : PipelinePath initial beforeHelper := by
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

private theorem accept_helper : AcceptStep theory true false beforeHelper afterHelper :=
  .paired delivery_steps.2.2.2.1 (.receive group_steps.2.2.2.2.2.1)

private theorem between_receipts : PipelinePath afterHelper beforeTarget := by
  have h0 : PipelinePath afterHelper afterHelper := .refl
  have h1 : PipelinePath afterHelper (state dlStartedTarget rgReceivedHelper disk6) :=
    PipelinePath.snoc h0 (.control (.start true true) trivial delivery_steps.2.2.2.2.1)
  exact PipelinePath.snoc h1 (.control (.send true) trivial delivery_steps.2.2.2.2.2.1)

private theorem accept_target : AcceptStep theory true true beforeTarget afterTarget :=
  .paired delivery_steps.2.2.2.2.2.2.1 (.receive group_steps.2.2.2.2.2.2.1)

private theorem store_manifest : PipelinePath afterTarget beforeFinish := by
  have h0 : PipelinePath afterTarget afterTarget := .refl
  have h1 : PipelinePath afterTarget (state dlAcceptedTarget rgReceived disk7) := PipelinePath.snoc h0 (.protocol (.storage (.Put false (.manifest true))
    (put_step disk6 false (.manifest true) rfl)))
  have h2 : PipelinePath afterTarget (state dlAcceptedTarget rgReceived disk8) := PipelinePath.snoc h1 (.protocol (.storage (.Put true (.manifest true))
    (put_step disk7 true (.manifest true) rfl)))
  exact PipelinePath.snoc h2 (.protocol (.storage (.Ack (.manifest true) ())
    (ack_step disk8 (.manifest true) (by
      intro r
      cases r <;> simp [disk8, disk7, disk6, disk5, disk4, disk3, disk2, disk1, disk0, put, ack]))))

private theorem finish : FinishStep theory true true beforeFinish completed := by
  refine FinishStep.paired (th := theory) ?_ ?_
  · exact delivery_steps.2.2.2.2.2.2.2
  · exact .registry group_steps.2.2.2.2.2.2.2 (by
      simp [ParaleanGroupComposition.Guard, protocolTheory, disk9, ack])

private theorem destroy_replica : Next theory completed failed :=
  .protocol (.storage (.Lose false) lose_step)

/-- All phases belong to one connected run. Both receipts introduce a previously
unknown published group at the consumer. Disk destruction occurs after FinishStep. -/
theorem combined_receipt_commit_disk_failure :
    Assumptions theory ∧ Initial theory initial ∧
    PipelinePath initial beforeHelper ∧
    AcceptStep theory true false beforeHelper afterHelper ∧
    PipelinePath afterHelper beforeTarget ∧
    AcceptStep theory true true beforeTarget afterTarget ∧
    PipelinePath afterTarget beforeFinish ∧
    FinishStep theory true true beforeFinish completed ∧
    Next theory completed failed ∧
    ParaleanGroupComposition.StorageNext storageTheory completed.protocol.storage
      (.Lose false) failed.protocol.storage ∧
    Reachable theory failed ∧
    beforeHelper.protocol.registry.known true false = false ∧
    beforeTarget.protocol.registry.known true true = false ∧
    failed.delivery.done true = true ∧ failed.delivery.result true = true ∧
    failed.protocol.registry.head true = true ∧ deliveryTheory.required true = true ∧
    groupTheory.deps true false = true ∧
    groupTheory.member false 0 = true ∧ groupTheory.member false 1 = true ∧
    groupTheory.member true 2 = true ∧
    failed.protocol.storage.acknowledged (.manifest true) = true ∧
    failed.protocol.storage.stored true (.manifest true) = true ∧
    (∀ g, groupTheory.contents (failed.protocol.registry.head true) g = true ∧
      failed.delivery.checked g g = true ∧ deliveryTheory.realizes g g = true ∧
      failed.protocol.registry.published g = true ∧
      failed.protocol.storage.acknowledged (.payload g) = true ∧
      failed.protocol.storage.stored true (.payload g) = true) ∧
    (∀ g, completed.protocol.storage.stored false (.payload g) = true) ∧
    completed.protocol.storage.stored false (.manifest true) = true ∧
    failed.protocol.storage.live true = true ∧ failed.protocol.storage.live false = false ∧
    (∀ o, failed.protocol.storage.stored false o = false) := by
  have h0 : Reachable theory initial := .initial initial_valid
  have h1 := prepare_and_send.reachable h0
  have h2 := Reachable.step h1 (accept_helper.to_next theory true false _ _)
  have h3 := between_receipts.reachable h2
  have h4 := Reachable.step h3 (accept_target.to_next theory true true _ _)
  have h5 := store_manifest.reachable h4
  have h6 := Reachable.step h5 (finish.to_next theory true true _ _)
  have h7 := Reachable.step h6 destroy_replica
  refine ⟨assumptions, initial_valid, prepare_and_send, accept_helper, between_receipts,
    accept_target, store_manifest, finish, destroy_replica, lose_step, h7, ?_⟩
  simp [beforeHelper, beforeTarget, completed, failed, state, dlDone, dlAcceptedTarget,
    dlStartedTarget, dlAcceptedHelper, dlStartedHelper, dl0, rgCommitted, rgReceived,
    rgReceivedHelper, rgPublished, rg0, deliveryTheory, groupTheory,
    diskLost, disk9, disk8, disk7, disk6, disk5, disk4, disk3, disk2, disk1, disk0,
    put, ack, Bool.forall_bool]

end Execution
#print axioms combined_receipt_commit_disk_failure
end ParaleanAdmission
