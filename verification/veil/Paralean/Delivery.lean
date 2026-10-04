import Paralean.Groups

/-! Packet admission and completion. Request identities denote immutable full
envelopes (workspace, document/version, environment, target, checker and policy).
A separate epoch prevents reuse of a response across cancellation or restart.
Transport may duplicate, reorder or lose arbitrary packets. Only checked receipts
bound to the exact request and object can change the accepted result. -/
set_option veil.smt.trust false
set_option maxHeartbeats 2000000

veil module ParaleanDelivery
type node
type obj
type request
type packet
type snapshot
type name

immutable function packetRequest : packet → request
immutable function packetObject : packet → obj
immutable function packetEpoch : packet → Nat
immutable function packetNode : packet → node
immutable function receiptRequest : packet → request
immutable function receiptObject : packet → obj
immutable function receiptEpoch : packet → Nat
immutable function receiptNode : packet → node
immutable relation intact : packet → Bool
immutable relation verified : packet → Bool
immutable relation valid : obj → Bool
immutable relation realizes : obj → request → Bool
immutable relation required : request → Bool
immutable relation deps : obj → obj → Bool
immutable relation member : obj → name → Bool
immutable relation contents : snapshot → obj → Bool
immutable relation exportable : snapshot → Bool
relation flight : packet → Bool
relation checked : obj → request → Bool
function current : node → request
function epoch : node → Nat
relation active : node → Bool
relation accepted : node → Bool
function acceptedObject : node → obj
relation done : node → Bool
function result : node → snapshot
#gen_state

/- Trusted receipt verification concerns precisely its signed object and request.
Envelope equality, signed object matching and epoch checks are protocol code. -/
assumption [receipt_sound] ∀ m, verified m →
  valid (receiptObject m) ∧ realizes (receiptObject m) (receiptRequest m)

ghost relation buildable (S : snapshot) :=
  (∀ o, contents S o → valid o) ∧
  (∀ o p, contents S o → deps o p → contents S p) ∧
  (∀ o p x, contents S o → contents S p → member o x → member p x → o = p) ∧
  exportable S

ghost relation ready (S : snapshot) :=
  (∀ o, contents S o → ∃ r, checked o r) ∧
  (∀ o p, contents S o → deps o p → contents S p) ∧
  (∀ o p x, contents S o → contents S p → member o x → member p x → o = p) ∧
  exportable S ∧
  (∀ r, required r → ∃ o, contents S o ∧ checked o r)

after_init {
  flight M := false
  checked O R := false
  current N := (default : request)
  epoch N := 0
  active N := false
  accepted N := false
  acceptedObject N := (default : obj)
  done N := false
  result N := (default : snapshot)
}

/- Every fresh command or restart changes the epoch, even for the same envelope. -/
action start (n : node) (r : request) {
  current n := r
  epoch n := epoch n + 1
  active n := true
  accepted n := false
  done n := false
}
action cancel (n : node) {
  epoch n := epoch n + 1
  active n := false
  accepted n := false
  done n := false
}
/- Sending an already queued packet models duplication. Order is unconstrained. -/
action send (m : packet) { flight m := true }
action drop (m : packet) { flight m := false }
action accept (n : node) (m : packet) {
  require active n ∧ flight m
  require intact m ∧ verified m
  require packetRequest m = current n ∧ packetEpoch m = epoch n
  require packetNode m = n
  require receiptRequest m = packetRequest m
  require receiptObject m = packetObject m
  require receiptEpoch m = packetEpoch m ∧ receiptNode m = packetNode m
  checked (packetObject m) (packetRequest m) := true
  accepted n := true
  acceptedObject n := packetObject m
  flight m := false
}
action finish (n : node) (S : snapshot) {
  require active n
  require ready S
  result n := S
  done n := true
}

invariant [CheckedSound] ∀ o r, checked o r → valid o ∧ realizes o r
invariant [AcceptedSound] ∀ n, accepted n →
  active n ∧ checked (acceptedObject n) (current n)
invariant [CompletionSound] ∀ n, done n →
  buildable (result n) ∧
  (∀ r, required r → ∃ o, contents (result n) o ∧ checked o r ∧ realizes o r)
#gen_spec

section Proofs
variable (ρ σ node obj request packet snapshot name : Type)
variable [DecidableEq node] [Inhabited node]
variable [DecidableEq obj] [Inhabited obj]
variable [DecidableEq request] [Inhabited request]
variable [DecidableEq packet] [Inhabited packet]
variable [DecidableEq snapshot] [Inhabited snapshot]
variable [DecidableEq name] [Inhabited name]
variable (χ : State.Label → Type)
variable [χ_rep : ∀ f, Veil.FieldRepresentation
  (State.Label.toDomain node obj request packet snapshot name f) (State.Label.toCodomain node obj request packet snapshot name f) (χ f)]
variable [∀ f, Veil.LawfulFieldRepresentation
  (State.Label.toDomain node obj request packet snapshot name f) (State.Label.toCodomain node obj request packet snapshot name f) (χ f) (χ_rep f)]
variable [IsSubStateOf (State χ) σ]
variable [IsSubReaderOf (Theory node obj request packet snapshot name) ρ]
variable [finish_dec : delta% (finish._veil_dec_type_0
  (node := node) (obj := obj) (request := request) (packet := packet)
  (snapshot := snapshot) (name := name) (χ := χ))]


omit finish_dec in
theorem start_preserves (n : node) (r : request) :
  Veil.Transition.meetsSpecificationIfSuccessfulAssuming
    (start.ext.tr ρ σ node obj request packet snapshot name χ n r)
    (Assumptions ρ node obj request packet snapshot name)
    (Invariants ρ σ node obj request packet snapshot name χ)
    (Invariants ρ σ node obj request packet snapshot name χ) := by
  unveil
  grind (splits := 30)

omit finish_dec in
theorem cancel_preserves (n : node) :
  Veil.Transition.meetsSpecificationIfSuccessfulAssuming
    (cancel.ext.tr ρ σ node obj request packet snapshot name χ n)
    (Assumptions ρ node obj request packet snapshot name)
    (Invariants ρ σ node obj request packet snapshot name χ)
    (Invariants ρ σ node obj request packet snapshot name χ) := by
  unveil
  grind (splits := 30)

omit finish_dec in
theorem send_preserves (m : packet) :
  Veil.Transition.meetsSpecificationIfSuccessfulAssuming
    (send.ext.tr ρ σ node obj request packet snapshot name χ m)
    (Assumptions ρ node obj request packet snapshot name)
    (Invariants ρ σ node obj request packet snapshot name χ)
    (Invariants ρ σ node obj request packet snapshot name χ) := by
  unveil
  grind (splits := 30)

omit finish_dec in
theorem drop_preserves (m : packet) :
  Veil.Transition.meetsSpecificationIfSuccessfulAssuming
    (drop.ext.tr ρ σ node obj request packet snapshot name χ m)
    (Assumptions ρ node obj request packet snapshot name)
    (Invariants ρ σ node obj request packet snapshot name χ)
    (Invariants ρ σ node obj request packet snapshot name χ) := by
  unveil
  grind (splits := 30)

omit finish_dec in
theorem accept_preserves (n : node) (m : packet) :
  Veil.Transition.meetsSpecificationIfSuccessfulAssuming
    (accept.ext.tr ρ σ node obj request packet snapshot name χ n m)
    (Assumptions ρ node obj request packet snapshot name)
    (Invariants ρ σ node obj request packet snapshot name χ)
    (Invariants ρ σ node obj request packet snapshot name χ) := by
  unveil
  grind (splits := 30)

theorem finish_preserves (n : node) (S : snapshot) :
  Veil.Transition.meetsSpecificationIfSuccessfulAssuming
    (finish.ext.tr ρ σ node obj request packet snapshot name χ n S)
    (Assumptions ρ node obj request packet snapshot name)
    (Invariants ρ σ node obj request packet snapshot name χ)
    (Invariants ρ σ node obj request packet snapshot name χ) := by
  unveil
  grind (splits := 30)

omit finish_dec in
theorem initializer_preserves :
  Veil.Transition.meetsSpecificationIfSuccessfulAssuming
    (initializer.ext.tr ρ σ node obj request packet snapshot name χ)
    (Assumptions ρ node obj request packet snapshot name) (fun _ _ => True)
    (Invariants ρ σ node obj request packet snapshot name χ) := by
  unveil
  grind

variable [Inhabited σ]
omit finish_dec in
theorem Init_preserves (th : ρ) (s : σ)
    (ha : Assumptions ρ node obj request packet snapshot name th)
    (hi : Init ρ σ node obj request packet snapshot name χ th s) :
    Invariants ρ σ node obj request packet snapshot name χ th s :=
  initializer_preserves ρ σ node obj request packet snapshot name χ th default s ⟨ha, trivial⟩ hi

omit [Inhabited σ] in
theorem Next_preserves (th : ρ) (s s' : σ)
    (label : Label node obj request packet snapshot name)
    (ha : Assumptions ρ node obj request packet snapshot name th)
    (hs : Invariants ρ σ node obj request packet snapshot name χ th s)
    (ht : Next ρ σ node obj request packet snapshot name χ th s label s') :
    Invariants ρ σ node obj request packet snapshot name χ th s' := by
  cases label <;> simp only [Next, NextAct,
    start.ext.derived_eq, cancel.ext.derived_eq, send.ext.derived_eq, drop.ext.derived_eq, accept.ext.derived_eq, finish.ext.derived_eq] at ht
  all_goals first
    | exact start_preserves ρ σ node obj request packet snapshot name χ _ _ th s s' ⟨ha, hs⟩ ht
    | exact cancel_preserves ρ σ node obj request packet snapshot name χ _ th s s' ⟨ha, hs⟩ ht
    | exact send_preserves ρ σ node obj request packet snapshot name χ _ th s s' ⟨ha, hs⟩ ht
    | exact drop_preserves ρ σ node obj request packet snapshot name χ _ th s s' ⟨ha, hs⟩ ht
    | exact accept_preserves ρ σ node obj request packet snapshot name χ _ _ th s s' ⟨ha, hs⟩ ht
    | exact finish_preserves ρ σ node obj request packet snapshot name χ _ _ th s s' ⟨ha, hs⟩ ht

inductive Reachable (th : ρ) : σ → Prop where
  | initial {s} : Init ρ σ node obj request packet snapshot name χ th s → Reachable th s
  | step {s s'} : Reachable th s → (label : Label node obj request packet snapshot name) →
      Next ρ σ node obj request packet snapshot name χ th s label s' → Reachable th s'

theorem reachable_invariants (th : ρ) (ha : Assumptions ρ node obj request packet snapshot name th)
    {s : σ} (hr : Reachable ρ σ node obj request packet snapshot name χ th s) :
    Invariants ρ σ node obj request packet snapshot name χ th s := by
  induction hr with
  | initial hi => exact Init_preserves ρ σ node obj request packet snapshot name χ th _ ha hi
  | step hr label ht ih =>
      exact Next_preserves ρ σ node obj request packet snapshot name χ th _ _ label ha ih ht
end Proofs
end ParaleanDelivery

namespace ParaleanDelivery
abbrev CanonicalRep (node obj request packet snapshot name : Type) (f : State.Label) :=
  Veil.CanonicalField (State.Label.toDomain node obj request packet snapshot name f)
    (State.Label.toCodomain node obj request packet snapshot name f)
abbrev CanonicalState (node obj request packet snapshot name : Type) := State (CanonicalRep node obj request packet snapshot name)

noncomputable section Canonical
variable {node obj request packet snapshot name : Type}
  [DecidableEq node] [Inhabited node]
  [DecidableEq obj] [Inhabited obj]
  [DecidableEq request] [Inhabited request]
  [DecidableEq packet] [Inhabited packet]
  [DecidableEq snapshot] [Inhabited snapshot]
  [DecidableEq name] [Inhabited name]
@[reducible] instance canonicalFieldRep : ∀ f, Veil.FieldRepresentation
  (State.Label.toDomain node obj request packet snapshot name f) (State.Label.toCodomain node obj request packet snapshot name f)
  (CanonicalRep node obj request packet snapshot name f) := by
  intro f
  cases f <;> (apply Veil.canonicalFieldRepresentation; infer_instance_for_iterated_prod)
instance canonicalFieldRepLawful : ∀ f, Veil.LawfulFieldRepresentation
  (State.Label.toDomain node obj request packet snapshot name f) (State.Label.toCodomain node obj request packet snapshot name f)
  (CanonicalRep node obj request packet snapshot name f) (canonicalFieldRep f) := by
  intro f
  cases f <;> apply Veil.canonicalFieldRepresentationLawful
attribute [local instance] Classical.propDecidable
local instance : delta% (finish._veil_dec_type_0
  (node := node) (obj := obj) (request := request) (packet := packet)
  (snapshot := snapshot) (name := name) (χ := CanonicalRep node obj request packet snapshot name)) :=
  fun _ _ _ => Classical.propDecidable _
abbrev Step := Next (Theory node obj request packet snapshot name) (CanonicalState node obj request packet snapshot name)
  node obj request packet snapshot name (CanonicalRep node obj request packet snapshot name)
abbrev Safe := Invariants (Theory node obj request packet snapshot name) (CanonicalState node obj request packet snapshot name)
  node obj request packet snapshot name (CanonicalRep node obj request packet snapshot name)
abbrev Initial := Init (Theory node obj request packet snapshot name) (CanonicalState node obj request packet snapshot name)
  node obj request packet snapshot name (CanonicalRep node obj request packet snapshot name)
abbrev Reached := Reachable (Theory node obj request packet snapshot name) (CanonicalState node obj request packet snapshot name)
  node obj request packet snapshot name (CanonicalRep node obj request packet snapshot name)

def Admissible (th : Theory node obj request packet snapshot name) (s : CanonicalState node obj request packet snapshot name)
    (n : node) (m : packet) : Prop :=
  s.active n = true ∧ s.flight m = true ∧
  th.intact m = true ∧ th.verified m = true ∧
  th.packetRequest m = s.current n ∧ th.packetEpoch m = s.epoch n ∧
  th.packetNode m = n ∧
  th.receiptRequest m = th.packetRequest m ∧
  th.receiptObject m = th.packetObject m ∧
  th.receiptEpoch m = th.packetEpoch m ∧ th.receiptNode m = th.packetNode m

theorem accept_enabled_iff (th : Theory node obj request packet snapshot name) (s : CanonicalState node obj request packet snapshot name)
    (n : node) (m : packet) :
    (∃ s', Step th s (.accept n m) s') ↔ Admissible th s n m := by
  simp only [Step, Next, NextAct, accept.ext.derived_eq]
  dsimp [accept.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
    Veil.canonicalFieldRepresentation]
  simp [Admissible]

theorem accept_guarded (th : Theory node obj request packet snapshot name) (s s' : CanonicalState node obj request packet snapshot name)
    (n : node) (m : packet) (ht : Step th s (.accept n m) s') :
    Admissible th s n m :=
  (accept_enabled_iff th s n m).1 ⟨s', ht⟩

theorem stale_rejected (th : Theory node obj request packet snapshot name) (s s' : CanonicalState node obj request packet snapshot name)
    (n : node) (m : packet) (h : th.packetEpoch m ≠ s.epoch n) :
    ¬Step th s (.accept n m) s' := by
  intro ht
  have hg := accept_guarded th s s' n m ht
  unfold Admissible at hg
  grind

theorem corrupt_rejected (th : Theory node obj request packet snapshot name) (s s' : CanonicalState node obj request packet snapshot name)
    (n : node) (m : packet) (h : th.intact m = false) :
    ¬Step th s (.accept n m) s' := by
  intro ht
  have hi := (accept_guarded th s s' n m ht).2.2.1
  simp_all

theorem receipt_mismatch_rejected (th : Theory node obj request packet snapshot name)
    (s s' : CanonicalState node obj request packet snapshot name) (n : node) (m : packet)
    (h : th.receiptRequest m ≠ th.packetRequest m ∨
      th.receiptObject m ≠ th.packetObject m) :
    ¬Step th s (.accept n m) s' := by
  intro ht
  have hg := accept_guarded th s s' n m ht
  unfold Admissible at hg
  grind

theorem finish_enabled_iff (th : Theory node obj request packet snapshot name) (s : CanonicalState node obj request packet snapshot name)
    (n : node) (S : snapshot) :
    (∃ s', Step th s (.finish n S) s') ↔ s.active n = true ∧ ready S th s := by
  simp only [Step, Next, NextAct, finish.ext.derived_eq]
  dsimp [finish.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
    Veil.canonicalFieldRepresentation]
  simp [ready, getFrom, readFrom, Veil.FieldRepresentation.get]

theorem empty_cannot_complete (th : Theory node obj request packet snapshot name)
    (s s' : CanonicalState node obj request packet snapshot name) (n : node) (S : snapshot)
    (empty : ∀ o, th.contents S o = false) (r : request) (needed : th.required r = true) :
    ¬Step th s (.finish n S) s' := by
  intro ht
  have hr := ((finish_enabled_iff th s n S).1 ⟨s', ht⟩).2
  dsimp [ready, getFrom, readFrom, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    canonicalFieldRep, Veil.FieldRepresentation.get, Veil.canonicalFieldRepresentation] at hr
  obtain ⟨o, hh, _⟩ := hr.2.2.2.2 r needed
  simp_all

theorem reachable_safe (th : Theory node obj request packet snapshot name)
    (ha : Assumptions (Theory node obj request packet snapshot name) node obj request packet snapshot name th)
    {s : CanonicalState node obj request packet snapshot name} (hr : Reached th s) : Safe th s :=
  reachable_invariants _ _ node obj request packet snapshot name (CanonicalRep node obj request packet snapshot name) th ha hr

theorem completion_targets (th : Theory node obj request packet snapshot name) (s : CanonicalState node obj request packet snapshot name)
    (hs : Safe th s) (n : node) (hd : s.done n = true) :
    buildable (s.result n) th s ∧
    ∀ r, th.required r = true → ∃ o, th.contents (s.result n) o = true ∧
      s.checked o r = true ∧ th.realizes o r = true := by
  exact hs.2.2 n hd

def SameArtifacts (th : Theory node obj request packet snapshot name)
    (rg : ParaleanGroups.Theory node obj name snapshot) : Prop :=
  th.valid = rg.valid ∧ th.deps = rg.deps ∧ th.member = rg.member ∧
  th.contents = rg.contents ∧ th.exportable = rg.exportable

theorem completion_group_buildable (th : Theory node obj request packet snapshot name)
    (s : CanonicalState node obj request packet snapshot name) (hs : Safe th s) (n : node)
    (hd : s.done n = true) (gt : ParaleanGroups.Theory node obj name snapshot)
    (rg : ParaleanGroups.CanonicalState node obj name snapshot)
    (hm : SameArtifacts th gt) :
    ParaleanGroups.buildable (s.result n) gt rg := by
  have hb := (completion_targets th s hs n hd).1
  rcases hm with ⟨hv, hd, hm, hc, he⟩
  dsimp [buildable, ParaleanGroups.buildable, getFrom, readFrom,
    instIsSubStateOfRefl, instIsSubReaderOfRefl] at *
  simpa only [hv, hd, hm, hc, he] using hb

end Canonical
end ParaleanDelivery

namespace ParaleanArtifacts
/-- Distinct constructors make cross-kind aliasing impossible in the abstract store. -/
inductive Object (package checkpoint : Type) where
  | payload : package → Object package checkpoint
  | manifest : checkpoint → Object package checkpoint
  | catalog : Nat → Object package checkpoint
  | publication : package → Object package checkpoint
  deriving DecidableEq, Inhabited

theorem payload_injective {package checkpoint : Type} :
    Function.Injective (@Object.payload package checkpoint) := by
  intro a b h
  cases h
  rfl
theorem manifest_injective {package checkpoint : Type} :
    Function.Injective (@Object.manifest package checkpoint) := by
  intro a b h
  cases h
  rfl
theorem kinds_disjoint {package checkpoint : Type} (p : package) (s : checkpoint) :
    Object.payload p ≠ Object.manifest s := by
  intro h
  cases h

theorem catalog_injective {package checkpoint : Type} :
    Function.Injective (@Object.catalog package checkpoint) := by
  intro a b h
  cases h
  rfl

theorem catalog_payload_disjoint {package checkpoint : Type} (c : Nat) (p : package) :
    (Object.catalog c : Object package checkpoint) ≠ Object.payload p := by
  intro h
  cases h

theorem catalog_manifest_disjoint {package checkpoint : Type} (c : Nat) (s : checkpoint) :
    (Object.catalog c : Object package checkpoint) ≠ Object.manifest s := by
  intro h
  cases h

theorem publication_injective {package checkpoint : Type} :
    Function.Injective (@Object.publication package checkpoint) := by
  intro a b h
  cases h
  rfl

theorem publication_payload_disjoint {package checkpoint : Type} (g p : package) :
    (Object.publication g : Object package checkpoint) ≠ Object.payload p := by
  intro h
  cases h

theorem publication_manifest_disjoint {package checkpoint : Type} (g : package) (s : checkpoint) :
    (Object.publication g : Object package checkpoint) ≠ Object.manifest s := by
  intro h
  cases h

theorem publication_catalog_disjoint {package checkpoint : Type} (g : package) (c : Nat) :
    (Object.publication g : Object package checkpoint) ≠ Object.catalog c := by
  intro h
  cases h

/-- A full immutable job envelope. Equality binds every listed field. -/
structure Envelope where
  workspace : Nat
  workerGeneration : Nat
  document : String
  documentVersion : Nat
  environment : Nat
  target : String
  targetContract : Nat
  checker : Nat
  policy : Nat
  deriving DecidableEq, Repr, Inhabited
end ParaleanArtifacts

namespace ParaleanDelivery
noncomputable section Effects
variable {node obj request packet snapshot name : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq obj] [Inhabited obj]
  [DecidableEq request] [Inhabited request] [DecidableEq packet] [Inhabited packet]
  [DecidableEq snapshot] [Inhabited snapshot] [DecidableEq name] [Inhabited name]
attribute [local instance] Classical.propDecidable

theorem accept_effect (th : Theory node obj request packet snapshot name)
    (s s' : CanonicalState node obj request packet snapshot name)
    (n : node) (m : packet) (ht : Step th s (.accept n m) s') :
    s'.checked (th.packetObject m) (s.current n) = true ∧
    s'.acceptedObject n = th.packetObject m ∧
    s'.accepted n = true ∧ s'.flight m = false := by
  have hg := accept_guarded th s s' n m ht
  simp only [Step, Next, NextAct, accept.ext.derived_eq] at ht
  dsimp [accept.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
    Veil.canonicalFieldRepresentation] at ht
  repeat' rcases ht with ⟨hh, ht⟩
  try subst s'
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp, Admissible] at *
  grind

theorem start_epoch (th : Theory node obj request packet snapshot name)
    (s s' : CanonicalState node obj request packet snapshot name)
    (n : node) (r : request) (ht : Step th s (.start n r) s') :
    s'.epoch n = s.epoch n + 1 := by
  simp only [Step, Next, NextAct, start.ext.derived_eq] at ht
  dsimp [start.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
    Veil.canonicalFieldRepresentation] at ht
  subst s'
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

theorem old_response_after_restart (th : Theory node obj request packet snapshot name)
    (s s' s'' : CanonicalState node obj request packet snapshot name)
    (n : node) (r : request) (m : packet) (ht : Step th s (.start n r) s')
    (old : th.packetEpoch m = s.epoch n) : ¬Step th s' (.accept n m) s'' := by
  apply stale_rejected th s' s'' n m
  rw [old, start_epoch th s s' n r ht]
  exact Nat.ne_of_lt (Nat.lt_succ_self _)

theorem transport_no_admission (th : Theory node obj request packet snapshot name)
    (s s' : CanonicalState node obj request packet snapshot name)
    (m : packet) (label : Label node obj request packet snapshot name)
    (hl : label = .send m ∨ label = .drop m) (ht : Step th s label s') :
    s'.checked = s.checked ∧ s'.accepted = s.accepted ∧ s'.done = s.done := by
  rcases hl with rfl | rfl
  all_goals
    simp only [Step, Next, NextAct, send.ext.derived_eq, drop.ext.derived_eq] at ht
    dsimp [send.ext.tr, drop.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
      instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
      Veil.canonicalFieldRepresentation] at ht
    subst s'
    exact ⟨rfl, rfl, rfl⟩

end Effects
#print axioms reachable_safe
#print axioms accept_enabled_iff
#print axioms finish_enabled_iff
#print axioms empty_cannot_complete
#print axioms old_response_after_restart
#print axioms completion_group_buildable
end ParaleanDelivery

namespace ParaleanDelivery
noncomputable section Recipient
variable {node obj request packet snapshot name : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq obj] [Inhabited obj]
  [DecidableEq request] [Inhabited request] [DecidableEq packet] [Inhabited packet]
  [DecidableEq snapshot] [Inhabited snapshot] [DecidableEq name] [Inhabited name]
theorem wrong_worker_rejected (th : Theory node obj request packet snapshot name)
    (s s' : CanonicalState node obj request packet snapshot name)
    (n : node) (m : packet) (h : th.packetNode m ≠ n) :
    ¬Step th s (.accept n m) s' := by
  intro ht
  have hg := accept_guarded th s s' n m ht
  unfold Admissible at hg
  grind

theorem relabelled_receipt_rejected (th : Theory node obj request packet snapshot name)
    (s s' : CanonicalState node obj request packet snapshot name)
    (n : node) (m : packet) (h : th.receiptEpoch m ≠ th.packetEpoch m ∨
      th.receiptNode m ≠ th.packetNode m) :
    ¬Step th s (.accept n m) s' := by
  intro ht
  have hg := accept_guarded th s s' n m ht
  unfold Admissible at hg
  grind

end Recipient
#print axioms wrong_worker_rejected
#print axioms relabelled_receipt_rejected
end ParaleanDelivery

namespace ParaleanDelivery
noncomputable section FinishEffect
variable {node obj request packet snapshot name : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq obj] [Inhabited obj]
  [DecidableEq request] [Inhabited request] [DecidableEq packet] [Inhabited packet]
  [DecidableEq snapshot] [Inhabited snapshot] [DecidableEq name] [Inhabited name]
attribute [local instance] Classical.propDecidable
local instance : delta% (finish._veil_dec_type_0
  (node := node) (obj := obj) (request := request) (packet := packet)
  (snapshot := snapshot) (name := name)
  (χ := CanonicalRep node obj request packet snapshot name)) :=
  fun _ _ _ => Classical.propDecidable _

theorem finish_effect (th : Theory node obj request packet snapshot name)
    (s s' : CanonicalState node obj request packet snapshot name)
    (n : node) (S : snapshot) (ht : Step th s (.finish n S) s') :
    s'.done n = true ∧ s'.result n = S := by
  simp only [Step, Next, NextAct, finish.ext.derived_eq] at ht
  dsimp [finish.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
    Veil.canonicalFieldRepresentation] at ht
  repeat' rcases ht with ⟨hh, ht⟩
  try subst s'
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]
end FinishEffect
end ParaleanDelivery

namespace ParaleanDelivery
noncomputable section Execution
attribute [local instance] Classical.propDecidable

private def executionTheory : Theory Bool Unit Unit Bool Bool Unit where
  packetRequest := fun _ => ()
  packetObject := fun _ => ()
  packetEpoch := fun _ => 1
  packetNode := id
  receiptRequest := fun _ => ()
  receiptObject := fun _ => ()
  receiptEpoch := fun _ => 1
  receiptNode := id
  intact := fun _ => true
  verified := fun _ => true
  valid := fun _ => true
  realizes := fun _ _ => true
  required := fun _ => true
  deps := fun _ _ => false
  member := fun _ _ => true
  contents := fun S _ => S
  exportable := fun _ => true

private def executionInitial : CanonicalState Bool Unit Unit Bool Bool Unit where
  flight := fun _ => false
  checked := fun _ _ => false
  current := fun _ => ()
  epoch := fun _ => 0
  active := fun _ => false
  accepted := fun _ => false
  acceptedObject := fun _ => ()
  done := fun _ => false
  result := fun _ => false
private def executionStarted : CanonicalState Bool Unit Unit Bool Bool Unit :=
  { executionInitial with epoch := fun n => if n then 1 else 0, active := id }
private def executionSent : CanonicalState Bool Unit Unit Bool Bool Unit :=
  { executionStarted with flight := id }
private def executionAccepted : CanonicalState Bool Unit Unit Bool Bool Unit :=
  { executionStarted with checked := fun _ _ => true, accepted := id }
private def executionDone : CanonicalState Bool Unit Unit Bool Bool Unit :=
  { executionAccepted with done := id, result := id }

set_option linter.unusedSimpArgs false in
/-- Actual generated transitions finish a nonempty required target, despite a duplicate send. -/
theorem nonempty_completion_execution :
    Assumptions (Theory Bool Unit Unit Bool Bool Unit) Bool Unit Unit Bool Bool Unit executionTheory ∧
    Initial executionTheory executionInitial ∧
    Step executionTheory executionInitial (.start true ()) executionStarted ∧
    Step executionTheory executionStarted (.send true) executionSent ∧
    Step executionTheory executionSent (.send true) executionSent ∧
    Step executionTheory executionSent (.accept true true) executionAccepted ∧
    Step executionTheory executionAccepted (.finish true true) executionDone ∧
    executionDone.done true = true ∧ executionTheory.required () = true ∧
    executionTheory.contents (executionDone.result true) () = true := by
  repeat' apply And.intro
  all_goals simp [Assumptions, receipt_sound, Initial, Init, initializer.ext.tr,
    Step, Next, NextAct, start.ext.derived_eq, send.ext.derived_eq,
    accept.ext.derived_eq, finish.ext.derived_eq,
    start.ext.tr, send.ext.tr, accept.ext.tr, finish.ext.tr, ready,
    executionTheory, executionInitial, executionStarted, executionSent,
    executionAccepted, executionDone, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    canonicalFieldRep, Veil.canonicalFieldRepresentation,
    Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool]

end Execution
#print axioms nonempty_completion_execution
#print axioms finish_effect
#print axioms accept_effect
#print axioms corrupt_rejected
#print axioms receipt_mismatch_rejected
#print axioms transport_no_admission
end ParaleanDelivery
