import Veil

/-! Registry protocol corresponding to verification/tla/Registry.tla.
The clock and rank fields are proof-only admission history. They are not
protocol clocks, storage quorums, or synchronization requirements. -/

set_option veil.smt.trust false
set_option linter.unusedSimpArgs false

veil module ParaleanRegistry

type node
type decl
type name
type snapshot

immutable relation valid (d : decl) : Bool
immutable relation deps (d : decl) (e : decl) : Bool
immutable relation ancestors (d : decl) (e : decl) : Bool
immutable function declName : decl → name
immutable relation contents (S : snapshot) (d : decl) : Bool
immutable relation exportable (S : snapshot) : Bool
immutable individual emptySnapshot : snapshot

relation published (d : decl) : Bool
relation known (n : node) (d : decl) : Bool
relation pending (n : node) (d : decl) : Bool
function head : node → snapshot
relation alive (n : node) : Bool
relation online (n : node) : Bool
individual stable : Bool
individual clock : Nat
function rank : decl → Nat

assumption [valid_ancestry]
  ∀ d, valid d → ∀ a, ancestors d a →
    declName a = declName d ∧ (∀ b, ancestors a b → ancestors d b)

assumption [empty_contents] ∀ d, ¬contents emptySnapshot d
assumption [empty_exportable] exportable emptySnapshot

ghost relation buildable (S : snapshot) :=
  (∀ d, contents S d → valid d) ∧
  (∀ d e, contents S d → deps d e → contents S e) ∧
  (∀ d e, contents S d → contents S e → declName d = declName e → d = e) ∧
  exportable S

ghost relation isHead (n : node) (d : decl) :=
  known n d ∧ ¬∃ e, known n e ∧ ancestors e d

ghost relation current (n : node) (S : snapshot) :=
  ∀ d, contents S d → (∀ e, declName e = declName d → (isHead n e ↔ e = d))

after_init {
  published D := false
  known N D := false
  pending N D := false
  head N := emptySnapshot
  alive N := true
  online N := true
  stable := false
  clock := 0
  rank D := 0
}

action prepare (n : node) (d : decl) {
  require alive n
  require valid d
  require ∀ e, deps d e → known n e
  require ∀ e, ancestors d e → known n e
  require ¬deps d d ∧ ¬ancestors d d
  pending n d := true
}

action publish (n : node) (d : decl) {
  require alive n ∧ online n
  require pending n d
  if ¬published d then
    rank d := clock
    clock := clock + 1
  published d := true
  known n d := true
  pending n d := false
}

action receive (n : node) (d : decl) {
  require alive n ∧ online n
  require published d
  require ¬known n d
  known n d := true
}

action commit (n : node) (S : snapshot) {
  require alive n ∧ online n
  require ∀ d, contents S d → known n d
  require buildable S
  require current n S
  head n := S
}

action crash (n : node) {
  require ¬stable
  require alive n
  alive n := false
  known n D := false
  pending n D := false
}

action recover (n : node) {
  require ¬alive n
  alive n := true
}

action partition (n : node) {
  require ¬stable
  require online n
  online n := false
}

action reconnect (n : node) {
  require ¬online n
  online n := true
}

action heal {
  require ¬stable
  stable := true
  alive N := true
  online N := true
}

safety [registrySafety]
  (∀ d, published d → valid d) ∧
  (∀ d e, published d → deps d e → published e) ∧
  (∀ n d, known n d → published d) ∧
  (∀ n d, pending n d → valid d ∧ (∀ e, deps d e → published e)) ∧
  (∀ n, buildable (head n)) ∧
  (∀ n d, contents (head n) d → published d) ∧
  (∀ d, published d → rank d < clock) ∧
  (∀ d e, published d → deps d e → rank e < rank d)

/- Admission preserves ancestor publication and assigns older ancestors smaller ranks. -/
ghost relation ancestorSafety :=
  (∀ d e, published d → ancestors d e → published e) ∧
  (∀ n d, pending n d → ∀ e, ancestors d e → published e) ∧
  (∀ d e, published d → ancestors d e → rank e < rank d)

#gen_spec

abbrev CanonicalRep (node decl name snapshot : Type) (f : State.Label) :=
  Veil.CanonicalField (State.Label.toDomain node decl name snapshot f)
    (State.Label.toCodomain node decl name snapshot f)

abbrev CanonicalState (node decl name snapshot : Type) :=
  State (CanonicalRep node decl name snapshot)

noncomputable section Proofs
variable {node decl name snapshot : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq decl] [Inhabited decl]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]
@[reducible] instance canonicalFieldRep : ∀ f, Veil.FieldRepresentation
    (State.Label.toDomain node decl name snapshot f)
    (State.Label.toCodomain node decl name snapshot f)
    (CanonicalRep node decl name snapshot f) := by
  intro f
  cases f <;> (apply Veil.canonicalFieldRepresentation; infer_instance_for_iterated_prod)

instance canonicalFieldRepLawful : ∀ f, Veil.LawfulFieldRepresentation
    (State.Label.toDomain node decl name snapshot f)
    (State.Label.toCodomain node decl name snapshot f)
    (CanonicalRep node decl name snapshot f) (canonicalFieldRep f) := by
  intro f
  cases f <;> apply Veil.canonicalFieldRepresentationLawful

local instance : delta% @prepare._veil_dec_type_0 node decl name snapshot
    (CanonicalRep node decl name snapshot) canonicalFieldRep :=
  fun _ _ _ _ => Classical.propDecidable _
local instance : delta% @prepare._veil_dec_type_1 node decl name snapshot
    (CanonicalRep node decl name snapshot) canonicalFieldRep :=
  fun _ _ _ _ => Classical.propDecidable _
local instance : delta% (commit._veil_dec_type_0 (node := node) (decl := decl)
    (name := name) (snapshot := snapshot) (χ := CanonicalRep node decl name snapshot)) :=
  fun _ _ _ _ => Classical.propDecidable _
local instance : delta% (commit._veil_dec_type_1 (node := node) (decl := decl) (name := name) (snapshot := snapshot)) :=
  fun _ _ => Classical.propDecidable _
local instance : delta% (commit._veil_dec_type_2 (node := node) (decl := decl)
    (name := name) (snapshot := snapshot) (χ := CanonicalRep node decl name snapshot)) :=
  fun _ _ _ _ => Classical.propDecidable _

abbrev TheoryAssumptions := Assumptions (Theory node decl name snapshot) node decl name snapshot
abbrev Safe := Invariants (Theory node decl name snapshot) (CanonicalState node decl name snapshot)
  node decl name snapshot (CanonicalRep node decl name snapshot)

abbrev AncestorSafe := fun (th : Theory node decl name snapshot)
  (st : CanonicalState node decl name snapshot) => ancestorSafety th st

abbrev AncestorPre := fun (th : Theory node decl name snapshot)
  (st : CanonicalState node decl name snapshot) => Safe th st ∧ AncestorSafe th st

theorem prepare_safe (n : node) (d : decl) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (prepare.ext (ρ := Theory node decl name snapshot)
        (σ := CanonicalState node decl name snapshot) n d)
      TheoryAssumptions Safe (fun th st => registrySafety th st) := by
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem publish_safe (n : node) (d : decl) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (publish.ext (ρ := Theory node decl name snapshot)
        (σ := CanonicalState node decl name snapshot) n d)
      TheoryAssumptions Safe (fun th st => registrySafety th st) := by
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  rcases hinv with ⟨hvalid, hclosed, hknown, hpending, hhead, hheads, hrank, horder⟩
  intro halive honline hp
  have hnew := hpending n d hp
  split_ifs with hpub
  · grind
  · have old_deps_ne : ∀ a b, st.published a = true → th.deps a b = true → d ≠ b := by
      intro a b ha hab heq
      apply hpub
      subst b
      exact hclosed a d ha hab
    have new_deps_ne : ∀ b, th.deps d b = true → d ≠ b := by
      intro b hb heq
      apply hpub
      subst b
      exact hnew.2 d hb
    grind

theorem receive_safe (n : node) (d : decl) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (receive.ext (ρ := Theory node decl name snapshot)
        (σ := CanonicalState node decl name snapshot) n d)
      TheoryAssumptions Safe (fun th st => registrySafety th st) := by
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem commit_safe (n : node) (S : snapshot) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (commit.ext (ρ := Theory node decl name snapshot)
        (σ := CanonicalState node decl name snapshot) n S)
      TheoryAssumptions Safe (fun th st => registrySafety th st) := by
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem crash_safe (n : node) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (crash.ext (ρ := Theory node decl name snapshot)
        (σ := CanonicalState node decl name snapshot) n)
      TheoryAssumptions Safe (fun th st => registrySafety th st) := by
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem recover_safe (n : node) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (recover.ext (ρ := Theory node decl name snapshot)
        (σ := CanonicalState node decl name snapshot) n)
      TheoryAssumptions Safe (fun th st => registrySafety th st) := by
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem partition_safe (n : node) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (partition.ext (ρ := Theory node decl name snapshot)
        (σ := CanonicalState node decl name snapshot) n)
      TheoryAssumptions Safe (fun th st => registrySafety th st) := by
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem reconnect_safe (n : node) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (reconnect.ext (ρ := Theory node decl name snapshot)
        (σ := CanonicalState node decl name snapshot) n)
      TheoryAssumptions Safe (fun th st => registrySafety th st) := by
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem heal_safe  :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (heal.ext (ρ := Theory node decl name snapshot)
        (σ := CanonicalState node decl name snapshot) )
      TheoryAssumptions Safe (fun th st => registrySafety th st) := by
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem initializer_safe :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (initializer.ext (ρ := Theory node decl name snapshot)
        (σ := CanonicalState node decl name snapshot))
      TheoryAssumptions (fun _ _ => True) (fun th st => registrySafety th st) := by
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem prepare_ancestor_safe (n : node) (d : decl) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (prepare.ext (ρ := Theory node decl name snapshot)
        (σ := CanonicalState node decl name snapshot) n d)
      TheoryAssumptions AncestorPre AncestorSafe := by
  unfold AncestorPre AncestorSafe
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem publish_ancestor_safe (n : node) (d : decl) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (publish.ext (ρ := Theory node decl name snapshot)
        (σ := CanonicalState node decl name snapshot) n d)
      TheoryAssumptions AncestorPre AncestorSafe := by
  unfold AncestorPre AncestorSafe
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  rcases hinv with ⟨hs, hclosed, hpending, horder⟩
  have hrank := hs.2.2.2.2.2.2.1
  intro halive honline hp
  have hnew := hpending n d hp
  split_ifs with hpub
  · grind
  · have old_ancestors_ne : ∀ a b, st.published a = true →
        th.ancestors a b = true → d ≠ b := by
      intro a b ha hab heq
      apply hpub
      subst b
      exact hclosed a d ha hab
    have new_ancestors_ne : ∀ b, th.ancestors d b = true → d ≠ b := by
      intro b hb heq
      apply hpub
      subst b
      exact hnew d hb
    grind

theorem receive_ancestor_safe (n : node) (d : decl) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (receive.ext (ρ := Theory node decl name snapshot)
        (σ := CanonicalState node decl name snapshot) n d)
      TheoryAssumptions AncestorPre AncestorSafe := by
  unfold AncestorPre AncestorSafe
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem commit_ancestor_safe (n : node) (S : snapshot) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (commit.ext (ρ := Theory node decl name snapshot)
        (σ := CanonicalState node decl name snapshot) n S)
      TheoryAssumptions AncestorPre AncestorSafe := by
  unfold AncestorPre AncestorSafe
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem crash_ancestor_safe (n : node) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (crash.ext (ρ := Theory node decl name snapshot)
        (σ := CanonicalState node decl name snapshot) n)
      TheoryAssumptions AncestorPre AncestorSafe := by
  unfold AncestorPre AncestorSafe
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem recover_ancestor_safe (n : node) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (recover.ext (ρ := Theory node decl name snapshot)
        (σ := CanonicalState node decl name snapshot) n)
      TheoryAssumptions AncestorPre AncestorSafe := by
  unfold AncestorPre AncestorSafe
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem partition_ancestor_safe (n : node) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (partition.ext (ρ := Theory node decl name snapshot)
        (σ := CanonicalState node decl name snapshot) n)
      TheoryAssumptions AncestorPre AncestorSafe := by
  unfold AncestorPre AncestorSafe
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem reconnect_ancestor_safe (n : node) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (reconnect.ext (ρ := Theory node decl name snapshot)
        (σ := CanonicalState node decl name snapshot) n)
      TheoryAssumptions AncestorPre AncestorSafe := by
  unfold AncestorPre AncestorSafe
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem heal_ancestor_safe  :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (heal.ext (ρ := Theory node decl name snapshot)
        (σ := CanonicalState node decl name snapshot) )
      TheoryAssumptions AncestorPre AncestorSafe := by
  unfold AncestorPre AncestorSafe
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

abbrev RegistryNext := Next (Theory node decl name snapshot) (CanonicalState node decl name snapshot)
  node decl name snapshot (CanonicalRep node decl name snapshot)

abbrev RegistryInit := Init (Theory node decl name snapshot) (CanonicalState node decl name snapshot)
  node decl name snapshot (CanonicalRep node decl name snapshot)

private theorem vc_step_from
    (pre : Theory node decl name snapshot → CanonicalState node decl name snapshot → Prop)
    (act : Veil.VeilM Veil.Mode.external (Theory node decl name snapshot)
      (CanonicalState node decl name snapshot) Unit)
    (h : act.meetsSpecificationIfSuccessfulAssuming TheoryAssumptions pre
      (fun th st => registrySafety th st))
    (th : Theory node decl name snapshot) (st st' : CanonicalState node decl name snapshot)
    (ha : TheoryAssumptions th) (hi : pre th st)
    (ht : act.toTransitionDerived th st st') : Safe th st' := by
  have htr : act.toTransition.meetsSpecificationIfSuccessful
      (fun th st => TheoryAssumptions th ∧ pre th st)
      (fun th st => registrySafety th st) := by
    rw [Veil.Transition.meetsSpecificationIfSuccessful_eq]
    exact h
  rw [Veil.VeilM.toTransitionDerived_sound] at htr
  exact htr th st st' ⟨ha, hi⟩ ht

theorem next_safe
    (th : Theory node decl name snapshot) (st st' : CanonicalState node decl name snapshot)
    (label : Label node decl name snapshot)
    (ha : TheoryAssumptions th) (hi : Safe th st)
    (ht : RegistryNext th st label st') : Safe th st' := by
  cases label with
  | prepare n d => exact vc_step_from Safe _ (prepare_safe n d) th st st' ha hi ht
  | publish n d => exact vc_step_from Safe _ (publish_safe n d) th st st' ha hi ht
  | receive n d => exact vc_step_from Safe _ (receive_safe n d) th st st' ha hi ht
  | commit n S => exact vc_step_from Safe _ (commit_safe n S) th st st' ha hi ht
  | crash n => exact vc_step_from Safe _ (crash_safe n) th st st' ha hi ht
  | recover n => exact vc_step_from Safe _ (recover_safe n) th st st' ha hi ht
  | partition n => exact vc_step_from Safe _ (partition_safe n) th st st' ha hi ht
  | reconnect n => exact vc_step_from Safe _ (reconnect_safe n) th st st' ha hi ht
  | heal => exact vc_step_from Safe _ heal_safe th st st' ha hi ht

private theorem initializer_transition_safe :
    Veil.Transition.meetsSpecificationIfSuccessfulAssuming
      (initializer.ext.tr (Theory node decl name snapshot) (CanonicalState node decl name snapshot)
        node decl name snapshot (CanonicalRep node decl name snapshot))
      TheoryAssumptions (fun _ _ => True) (fun th st => registrySafety th st) := by
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  rcases htr with ⟨hpub, hknown, hpending, hhead, _⟩
  simp [hpub, hknown, hpending, ← hhead, has.2.1, has.2.2]

theorem initial_safe
    (th : Theory node decl name snapshot) (st : CanonicalState node decl name snapshot)
    (ha : TheoryAssumptions th) (ht : RegistryInit th st) : Safe th st := by
  exact initializer_transition_safe th default st ⟨ha, trivial⟩ ht

inductive Reachable (th : Theory node decl name snapshot) :
    CanonicalState node decl name snapshot → Prop where
  | initial {st} : RegistryInit th st → Reachable th st
  | step {st st'} {label : Label node decl name snapshot} : Reachable th st →
      RegistryNext th st label st' → Reachable th st'
  | stutter {st} : Reachable th st → Reachable th st

theorem reachable_safe
    (th : Theory node decl name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node decl name snapshot} (hr : Reachable th st) : Safe th st := by
  induction hr with
  | initial hi => exact initial_safe th _ ha hi
  | step hr ht ih => exact next_safe th _ _ _ ha ih ht
  | stutter hr ih => exact ih


private theorem vc_ancestor_step_from
    (act : Veil.VeilM Veil.Mode.external (Theory node decl name snapshot)
      (CanonicalState node decl name snapshot) Unit)
    (h : act.meetsSpecificationIfSuccessfulAssuming TheoryAssumptions AncestorPre AncestorSafe)
    (th : Theory node decl name snapshot) (st st' : CanonicalState node decl name snapshot)
    (ha : TheoryAssumptions th) (hs : Safe th st) (hi : AncestorSafe th st)
    (ht : act.toTransitionDerived th st st') : AncestorSafe th st' := by
  have htr : act.toTransition.meetsSpecificationIfSuccessful
      (fun th st => TheoryAssumptions th ∧ AncestorPre th st) AncestorSafe := by
    rw [Veil.Transition.meetsSpecificationIfSuccessful_eq]
    exact h
  rw [Veil.VeilM.toTransitionDerived_sound] at htr
  exact htr th st st' ⟨ha, hs, hi⟩ ht

theorem next_ancestor_safe
    (th : Theory node decl name snapshot) (st st' : CanonicalState node decl name snapshot)
    (label : Label node decl name snapshot)
    (ha : TheoryAssumptions th) (hs : Safe th st) (hi : AncestorSafe th st)
    (ht : RegistryNext th st label st') : AncestorSafe th st' := by
  cases label with
  | prepare n d => exact vc_ancestor_step_from _ (prepare_ancestor_safe n d) th st st' ha hs hi ht
  | publish n d => exact vc_ancestor_step_from _ (publish_ancestor_safe n d) th st st' ha hs hi ht
  | receive n d => exact vc_ancestor_step_from _ (receive_ancestor_safe n d) th st st' ha hs hi ht
  | commit n S => exact vc_ancestor_step_from _ (commit_ancestor_safe n S) th st st' ha hs hi ht
  | crash n => exact vc_ancestor_step_from _ (crash_ancestor_safe n) th st st' ha hs hi ht
  | recover n => exact vc_ancestor_step_from _ (recover_ancestor_safe n) th st st' ha hs hi ht
  | partition n => exact vc_ancestor_step_from _ (partition_ancestor_safe n) th st st' ha hs hi ht
  | reconnect n => exact vc_ancestor_step_from _ (reconnect_ancestor_safe n) th st st' ha hs hi ht
  | heal  => exact vc_ancestor_step_from _ (heal_ancestor_safe ) th st st' ha hs hi ht

private theorem initializer_transition_ancestor_safe :
    Veil.Transition.meetsSpecificationIfSuccessfulAssuming
      (initializer.ext.tr (Theory node decl name snapshot) (CanonicalState node decl name snapshot)
        node decl name snapshot (CanonicalRep node decl name snapshot))
      TheoryAssumptions (fun _ _ => True) AncestorSafe := by
  unfold AncestorSafe
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  rcases htr with ⟨hpub, hknown, hpending, hhead, _⟩
  simp [hpub, hpending]

theorem initial_ancestor_safe
    (th : Theory node decl name snapshot) (st : CanonicalState node decl name snapshot)
    (ha : TheoryAssumptions th) (ht : RegistryInit th st) : AncestorSafe th st := by
  exact initializer_transition_ancestor_safe th default st ⟨ha, trivial⟩ ht

theorem reachable_ancestor_safe
    (th : Theory node decl name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node decl name snapshot} (hr : Reachable th st) :
    AncestorSafe th st := by
  induction hr with
  | initial hi => exact initial_ancestor_safe th _ ha hi
  | step hr ht ih => exact next_ancestor_safe th _ _ _ ha (reachable_safe th ha hr) ih ht
  | stutter hr ih => exact ih


theorem dependency_acyclic
    (th : Theory node decl name snapshot) (st : CanonicalState node decl name snapshot)
    (hs : Safe th st) (T : decl → Prop)
    (hsub : ∀ d, T d → st.published d = true) (hne : ∃ d, T d) :
    ∃ d, T d ∧ ∀ e, T e → th.deps d e ≠ true := by
  classical
  have horder : ∀ d e, st.published d = true → th.deps d e = true →
      st.rank e < st.rank d := hs.2.2.2.2.2.2.2
  have minimal : ∀ k, ∀ d, T d → st.rank d = k →
      ∃ d, T d ∧ ∀ e, T e → th.deps d e ≠ true := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro d hd hr
      by_cases hblocked : ∃ e, T e ∧ th.deps d e = true
      · obtain ⟨e, he, hdep⟩ := hblocked
        exact ih (st.rank e) (hr ▸ horder d e (hsub d hd) hdep) e he rfl
      · exact ⟨d, hd, fun e he hdep => hblocked ⟨e, he, hdep⟩⟩
  obtain ⟨d, hd⟩ := hne
  exact minimal (st.rank d) d hd rfl

theorem known_published
    (th : Theory node decl name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node decl name snapshot} (hr : Reachable th st)
    (n : node) (d : decl) (hk : st.known n d = true) : st.published d = true :=
  (reachable_safe th ha hr).2.2.1 n d hk

theorem published_valid
    (th : Theory node decl name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node decl name snapshot} (hr : Reachable th st)
    (d : decl) (hp : st.published d = true) : th.valid d = true :=
  (reachable_safe th ha hr).1 d hp

theorem published_closed
    (th : Theory node decl name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node decl name snapshot} (hr : Reachable th st)
    (d e : decl) (hp : st.published d = true) (hd : th.deps d e = true) :
    st.published e = true :=
  (reachable_safe th ha hr).2.1 d e hp hd

theorem snapshot_safe
    (th : Theory node decl name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node decl name snapshot} (hr : Reachable th st) (n : node) :
    buildable (st.head n) th st ∧
      ∀ d, th.contents (st.head n) d = true → st.published d = true := by
  have hs := reachable_safe th ha hr
  exact ⟨hs.2.2.2.2.1 n, hs.2.2.2.2.2.1 n⟩

theorem reachable_acyclic
    (th : Theory node decl name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node decl name snapshot} (hr : Reachable th st)
    (T : decl → Prop) (hsub : ∀ d, T d → st.published d = true) (hne : ∃ d, T d) :
    ∃ d, T d ∧ ∀ e, T e → th.deps d e ≠ true :=
  dependency_acyclic th st (reachable_safe th ha hr) T hsub hne


theorem published_ancestors_closed
    (th : Theory node decl name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node decl name snapshot} (hr : Reachable th st)
    (d e : decl) (hp : st.published d = true) (he : th.ancestors d e = true) :
    st.published e = true :=
  (reachable_ancestor_safe th ha hr).1 d e hp he

theorem pending_ancestors_closed
    (th : Theory node decl name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node decl name snapshot} (hr : Reachable th st)
    (n : node) (d e : decl) (hp : st.pending n d = true) (he : th.ancestors d e = true) :
    st.published e = true :=
  (reachable_ancestor_safe th ha hr).2.1 n d hp e he

theorem published_ancestor_rank
    (th : Theory node decl name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node decl name snapshot} (hr : Reachable th st)
    (d e : decl) (hp : st.published d = true) (he : th.ancestors d e = true) :
    st.rank e < st.rank d :=
  (reachable_ancestor_safe th ha hr).2.2 d e hp he

theorem published_no_self_ancestor
    (th : Theory node decl name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node decl name snapshot} (hr : Reachable th st)
    (d : decl) (hp : st.published d = true) : th.ancestors d d ≠ true := by
  intro he
  exact Nat.lt_irrefl _ (published_ancestor_rank th ha hr d d hp he)

theorem ancestor_acyclic
    (th : Theory node decl name snapshot) (st : CanonicalState node decl name snapshot)
    (hs : AncestorSafe th st) (T : decl → Prop)
    (hsub : ∀ d, T d → st.published d = true) (hne : ∃ d, T d) :
    ∃ d, T d ∧ ∀ e, T e → th.ancestors d e ≠ true := by
  classical
  have horder := hs.2.2
  have minimal : ∀ k, ∀ d, T d → st.rank d = k →
      ∃ d, T d ∧ ∀ e, T e → th.ancestors d e ≠ true := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro d hd hr
      by_cases hblocked : ∃ e, T e ∧ th.ancestors d e = true
      · obtain ⟨e, he, hancestor⟩ := hblocked
        exact ih (st.rank e) (hr ▸ horder d e (hsub d hd) hancestor) e he rfl
      · exact ⟨d, hd, fun e he hancestor => hblocked ⟨e, he, hancestor⟩⟩
  obtain ⟨d, hd⟩ := hne
  exact minimal (st.rank d) d hd rfl

theorem reachable_ancestor_acyclic
    (th : Theory node decl name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node decl name snapshot} (hr : Reachable th st)
    (T : decl → Prop) (hsub : ∀ d, T d → st.published d = true) (hne : ∃ d, T d) :
    ∃ d, T d ∧ ∀ e, T e → th.ancestors d e ≠ true :=
  ancestor_acyclic th st (reachable_ancestor_safe th ha hr) T hsub hne

/-- Two causal heads sharing a name cannot be selected as a current version. -/
theorem collision_blocks_current
    (th : Theory node decl name snapshot) (st : CanonicalState node decl name snapshot)
    (n : node) (S : snapshot) (a b d : decl)
    (ha : isHead n a th st) (hb : isHead n b th st)
    (hna : th.declName a = th.declName d) (hnb : th.declName b = th.declName d)
    (hne : a ≠ b) (hd : th.contents S d = true) : ¬current n S th st := by
  intro hc
  have had : a = d := (hc d hd a hna).1 ha
  have hbd : b = d := (hc d hd b hnb).1 hb
  exact hne (had.trans hbd.symm)

#print axioms published_ancestors_closed
#print axioms pending_ancestors_closed
#print axioms published_ancestor_rank
#print axioms published_no_self_ancestor
#print axioms ancestor_acyclic
#print axioms reachable_ancestor_acyclic
#print axioms initial_ancestor_safe
#print axioms next_ancestor_safe
#print axioms reachable_ancestor_safe
#print axioms prepare_ancestor_safe
#print axioms publish_ancestor_safe
#print axioms receive_ancestor_safe
#print axioms commit_ancestor_safe
#print axioms crash_ancestor_safe
#print axioms recover_ancestor_safe
#print axioms partition_ancestor_safe
#print axioms reconnect_ancestor_safe
#print axioms heal_ancestor_safe
#print axioms known_published
#print axioms published_valid
#print axioms published_closed
#print axioms snapshot_safe
#print axioms reachable_acyclic
#print axioms collision_blocks_current
#print axioms next_safe
#print axioms initial_safe
#print axioms reachable_safe
#print axioms dependency_acyclic
#print axioms prepare_safe
#print axioms publish_safe
#print axioms receive_safe
#print axioms commit_safe
#print axioms crash_safe
#print axioms recover_safe
#print axioms partition_safe
#print axioms reconnect_safe
#print axioms heal_safe
#print axioms initializer_safe
end Proofs
end ParaleanRegistry
