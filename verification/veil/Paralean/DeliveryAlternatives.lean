import Paralean.Delivery

/-! Two distinct objects can complete the same immutable required contract. -/
namespace ParaleanDelivery
noncomputable section Alternatives
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
local instance : delta% (finish._veil_dec_type_0
    (node := Unit) (obj := Bool) (request := Unit) (packet := Bool)
    (snapshot := Bool) (name := Unit) (χ := CanonicalRep Unit Bool Unit Bool Bool Unit)) :=
  fun _ _ _ => Classical.propDecidable _

private def alternativeTheory : Theory Unit Bool Unit Bool Bool Unit where
  packetRequest := fun _ => ()
  packetObject := id
  packetEpoch := fun _ => 1
  packetNode := fun _ => ()
  receiptRequest := fun _ => ()
  receiptObject := id
  receiptEpoch := fun _ => 1
  receiptNode := fun _ => ()
  intact := fun _ => true
  verified := fun _ => true
  valid := fun _ => true
  realizes := fun _ _ => true
  required := fun _ => true
  deps := fun _ _ => false
  member := fun _ _ => true
  contents := fun S o => decide (o = S)
  exportable := fun _ => true

private def alternativeInitial : CanonicalState Unit Bool Unit Bool Bool Unit where
  flight := fun _ => false
  checked := fun _ _ => false
  current := fun _ => ()
  epoch := fun _ => 0
  active := fun _ => false
  accepted := fun _ => false
  acceptedObject := fun _ => false
  done := fun _ => false
  result := fun _ => false
private def alternativeStarted : CanonicalState Unit Bool Unit Bool Bool Unit :=
  { alternativeInitial with epoch := fun _ => 1, active := fun _ => true }
private def alternativeSent (o : Bool) : CanonicalState Unit Bool Unit Bool Bool Unit :=
  { alternativeStarted with flight := fun m => decide (m = o) }
private def alternativeAccepted (o : Bool) : CanonicalState Unit Bool Unit Bool Bool Unit :=
  { alternativeStarted with
    checked := fun g _ => decide (g = o)
    accepted := fun _ => true
    acceptedObject := fun _ => o }
private def alternativeDone (o : Bool) : CanonicalState Unit Bool Unit Bool Bool Unit :=
  { alternativeAccepted o with done := fun _ => true, result := fun _ => o }

private theorem alternative_steps (o : Bool) :
    Assumptions (Theory Unit Bool Unit Bool Bool Unit) Unit Bool Unit Bool Bool Unit alternativeTheory ∧
    Initial alternativeTheory alternativeInitial ∧
    Step alternativeTheory alternativeInitial (.start () ()) alternativeStarted ∧
    Step alternativeTheory alternativeStarted (.send o) (alternativeSent o) ∧
    Step alternativeTheory (alternativeSent o) (.accept () o) (alternativeAccepted o) ∧
    Step alternativeTheory (alternativeAccepted o) (.finish () o) (alternativeDone o) := by
  cases o <;> repeat' apply And.intro
  all_goals simp [Assumptions, receipt_sound, Initial, Init, initializer.ext.tr,
    Step, Next, NextAct, start.ext.derived_eq, send.ext.derived_eq,
    accept.ext.derived_eq, finish.ext.derived_eq,
    start.ext.tr, send.ext.tr, accept.ext.tr, finish.ext.tr, ready,
    alternativeTheory, alternativeInitial, alternativeStarted, alternativeSent,
    alternativeAccepted, alternativeDone, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    canonicalFieldRep, Veil.canonicalFieldRepresentation,
    Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]

/-- Both choices have a complete generated execution from the same initial state. -/
theorem alternative_results_complete :
    Assumptions (Theory Unit Bool Unit Bool Bool Unit) Unit Bool Unit Bool Bool Unit alternativeTheory ∧
    alternativeTheory.required () = true ∧
    ∀ o : Bool, Reached alternativeTheory (alternativeDone o) ∧
      (alternativeDone o).acceptedObject () = o ∧
      (alternativeDone o).done () = true ∧ (alternativeDone o).result () = o ∧
      alternativeTheory.contents o o = true ∧ (alternativeDone o).checked o () = true ∧
      alternativeTheory.realizes o () = true := by
  refine ⟨(alternative_steps false).1, rfl, ?_⟩
  intro o
  obtain ⟨_, hi, hstart, hsend, haccept, hfinish⟩ := alternative_steps o
  have h0 : Reached alternativeTheory alternativeInitial := .initial hi
  have h1 : Reached alternativeTheory alternativeStarted := .step h0 (.start () ()) hstart
  have h2 : Reached alternativeTheory (alternativeSent o) := .step h1 (.send o) hsend
  have h3 : Reached alternativeTheory (alternativeAccepted o) := .step h2 (.accept () o) haccept
  have hr : Reached alternativeTheory (alternativeDone o) := .step h3 (.finish () o) hfinish
  refine ⟨hr, rfl, rfl, rfl, ?_, ?_, rfl⟩ <;> simp [alternativeTheory, alternativeDone, alternativeAccepted]

end Alternatives
#print axioms alternative_results_complete
end ParaleanDelivery
