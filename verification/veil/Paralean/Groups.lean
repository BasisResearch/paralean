import Veil
import Paralean.Registry
import Paralean.Composition
import Paralean.Convergence

/-! Atomic declaration-group protocol. Names and per-name revision edges are immutable.
The clock and rank fields are proof-only admission history. They are not
protocol clocks, storage quorums, or synchronization requirements. -/

set_option veil.smt.trust false
set_option linter.unusedSimpArgs false

veil module ParaleanGroups

type node
type group
type name
type snapshot

immutable relation valid (d : group) : Bool
immutable relation deps (d : group) (e : group) : Bool
immutable relation ancestors (d : group) (e : group) : Bool
immutable relation member (g : group) (x : name) : Bool
immutable relation revisions (g : group) (a : group) (x : name) : Bool
immutable relation contents (S : snapshot) (d : group) : Bool
immutable relation exportable (S : snapshot) : Bool
immutable individual emptySnapshot : snapshot

relation published (d : group) : Bool
relation known (n : node) (d : group) : Bool
relation pending (n : node) (d : group) : Bool
function head : node → snapshot
relation alive (n : node) : Bool
relation online (n : node) : Bool
individual stable : Bool
individual clock : Nat
function rank : group → Nat

assumption [valid_ancestry]
  (∀ g a, ancestors g a ↔ ∃ x, revisions g a x) ∧
  (∀ g a x, valid g → revisions g a x →
    member g x ∧ member a x ∧ (∀ b, revisions a b x → revisions g b x)) ∧
  (∀ g, valid g → ∃ x, member g x)

assumption [empty_contents] ∀ d, ¬contents emptySnapshot d
assumption [empty_exportable] exportable emptySnapshot

ghost relation buildable (S : snapshot) :=
  (∀ d, contents S d → valid d) ∧
  (∀ d e, contents S d → deps d e → contents S e) ∧
  (∀ d e x, contents S d → contents S e → member d x → member e x → d = e) ∧
  exportable S

ghost relation isHead (n : node) (d : group) (x : name) :=
  known n d ∧ member d x ∧ ¬∃ e, known n e ∧ revisions e d x

ghost relation current (n : node) (S : snapshot) :=
  ∀ d x, contents S d → member d x → ∀ e, (isHead n e x ↔ e = d)

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

action prepare (n : node) (d : group) {
  require alive n
  require valid d
  require ∀ e, deps d e → known n e
  require ∀ e, ancestors d e → known n e
  require ¬deps d d ∧ ¬ancestors d d
  pending n d := true
}

action publish (n : node) (d : group) {
  require alive n ∧ online n
  require pending n d
  if ¬published d then
    rank d := clock
    clock := clock + 1
  published d := true
  known n d := true
  pending n d := false
}

action receive (n : node) (d : group) {
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

abbrev CanonicalRep (node group name snapshot : Type) (f : State.Label) :=
  Veil.CanonicalField (State.Label.toDomain node group name snapshot f)
    (State.Label.toCodomain node group name snapshot f)

abbrev CanonicalState (node group name snapshot : Type) :=
  State (CanonicalRep node group name snapshot)

noncomputable section Proofs
variable {node group name snapshot : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]
@[reducible] instance canonicalFieldRep : ∀ f, Veil.FieldRepresentation
    (State.Label.toDomain node group name snapshot f)
    (State.Label.toCodomain node group name snapshot f)
    (CanonicalRep node group name snapshot f) := by
  intro f
  cases f <;> (apply Veil.canonicalFieldRepresentation; infer_instance_for_iterated_prod)

instance canonicalFieldRepLawful : ∀ f, Veil.LawfulFieldRepresentation
    (State.Label.toDomain node group name snapshot f)
    (State.Label.toCodomain node group name snapshot f)
    (CanonicalRep node group name snapshot f) (canonicalFieldRep f) := by
  intro f
  cases f <;> apply Veil.canonicalFieldRepresentationLawful

local instance : delta% @prepare._veil_dec_type_0 node group name snapshot
    (CanonicalRep node group name snapshot) canonicalFieldRep :=
  fun _ _ _ _ => Classical.propDecidable _
local instance : delta% @prepare._veil_dec_type_1 node group name snapshot
    (CanonicalRep node group name snapshot) canonicalFieldRep :=
  fun _ _ _ _ => Classical.propDecidable _
local instance : delta% (commit._veil_dec_type_0 (node := node) (group := group)
    (name := name) (snapshot := snapshot) (χ := CanonicalRep node group name snapshot)) :=
  fun _ _ _ _ => Classical.propDecidable _
local instance : delta% (commit._veil_dec_type_1 (node := node) (group := group) (name := name) (snapshot := snapshot)) :=
  fun _ _ => Classical.propDecidable _
local instance : delta% (commit._veil_dec_type_2 (node := node) (group := group)
    (name := name) (snapshot := snapshot) (χ := CanonicalRep node group name snapshot)) :=
  fun _ _ _ _ => Classical.propDecidable _

abbrev TheoryAssumptions := Assumptions (Theory node group name snapshot) node group name snapshot
abbrev Safe := Invariants (Theory node group name snapshot) (CanonicalState node group name snapshot)
  node group name snapshot (CanonicalRep node group name snapshot)

abbrev AncestorSafe := fun (th : Theory node group name snapshot)
  (st : CanonicalState node group name snapshot) => ancestorSafety th st

abbrev AncestorPre := fun (th : Theory node group name snapshot)
  (st : CanonicalState node group name snapshot) => Safe th st ∧ AncestorSafe th st

theorem prepare_safe (n : node) (d : group) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (prepare.ext (ρ := Theory node group name snapshot)
        (σ := CanonicalState node group name snapshot) n d)
      TheoryAssumptions Safe (fun th st => registrySafety th st) := by
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem publish_safe (n : node) (d : group) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (publish.ext (ρ := Theory node group name snapshot)
        (σ := CanonicalState node group name snapshot) n d)
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

theorem receive_safe (n : node) (d : group) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (receive.ext (ρ := Theory node group name snapshot)
        (σ := CanonicalState node group name snapshot) n d)
      TheoryAssumptions Safe (fun th st => registrySafety th st) := by
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem commit_safe (n : node) (S : snapshot) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (commit.ext (ρ := Theory node group name snapshot)
        (σ := CanonicalState node group name snapshot) n S)
      TheoryAssumptions Safe (fun th st => registrySafety th st) := by
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem crash_safe (n : node) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (crash.ext (ρ := Theory node group name snapshot)
        (σ := CanonicalState node group name snapshot) n)
      TheoryAssumptions Safe (fun th st => registrySafety th st) := by
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem recover_safe (n : node) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (recover.ext (ρ := Theory node group name snapshot)
        (σ := CanonicalState node group name snapshot) n)
      TheoryAssumptions Safe (fun th st => registrySafety th st) := by
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem partition_safe (n : node) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (partition.ext (ρ := Theory node group name snapshot)
        (σ := CanonicalState node group name snapshot) n)
      TheoryAssumptions Safe (fun th st => registrySafety th st) := by
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem reconnect_safe (n : node) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (reconnect.ext (ρ := Theory node group name snapshot)
        (σ := CanonicalState node group name snapshot) n)
      TheoryAssumptions Safe (fun th st => registrySafety th st) := by
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem heal_safe  :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (heal.ext (ρ := Theory node group name snapshot)
        (σ := CanonicalState node group name snapshot) )
      TheoryAssumptions Safe (fun th st => registrySafety th st) := by
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem initializer_safe :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (initializer.ext (ρ := Theory node group name snapshot)
        (σ := CanonicalState node group name snapshot))
      TheoryAssumptions (fun _ _ => True) (fun th st => registrySafety th st) := by
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem prepare_ancestor_safe (n : node) (d : group) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (prepare.ext (ρ := Theory node group name snapshot)
        (σ := CanonicalState node group name snapshot) n d)
      TheoryAssumptions AncestorPre AncestorSafe := by
  unfold AncestorPre AncestorSafe
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem publish_ancestor_safe (n : node) (d : group) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (publish.ext (ρ := Theory node group name snapshot)
        (σ := CanonicalState node group name snapshot) n d)
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

theorem receive_ancestor_safe (n : node) (d : group) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (receive.ext (ρ := Theory node group name snapshot)
        (σ := CanonicalState node group name snapshot) n d)
      TheoryAssumptions AncestorPre AncestorSafe := by
  unfold AncestorPre AncestorSafe
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem commit_ancestor_safe (n : node) (S : snapshot) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (commit.ext (ρ := Theory node group name snapshot)
        (σ := CanonicalState node group name snapshot) n S)
      TheoryAssumptions AncestorPre AncestorSafe := by
  unfold AncestorPre AncestorSafe
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem crash_ancestor_safe (n : node) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (crash.ext (ρ := Theory node group name snapshot)
        (σ := CanonicalState node group name snapshot) n)
      TheoryAssumptions AncestorPre AncestorSafe := by
  unfold AncestorPre AncestorSafe
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem recover_ancestor_safe (n : node) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (recover.ext (ρ := Theory node group name snapshot)
        (σ := CanonicalState node group name snapshot) n)
      TheoryAssumptions AncestorPre AncestorSafe := by
  unfold AncestorPre AncestorSafe
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem partition_ancestor_safe (n : node) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (partition.ext (ρ := Theory node group name snapshot)
        (σ := CanonicalState node group name snapshot) n)
      TheoryAssumptions AncestorPre AncestorSafe := by
  unfold AncestorPre AncestorSafe
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem reconnect_ancestor_safe (n : node) :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (reconnect.ext (ρ := Theory node group name snapshot)
        (σ := CanonicalState node group name snapshot) n)
      TheoryAssumptions AncestorPre AncestorSafe := by
  unfold AncestorPre AncestorSafe
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

theorem heal_ancestor_safe  :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (heal.ext (ρ := Theory node group name snapshot)
        (σ := CanonicalState node group name snapshot) )
      TheoryAssumptions AncestorPre AncestorSafe := by
  unfold AncestorPre AncestorSafe
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  grind

abbrev GroupsNext := Next (Theory node group name snapshot) (CanonicalState node group name snapshot)
  node group name snapshot (CanonicalRep node group name snapshot)

abbrev GroupsInit := Init (Theory node group name snapshot) (CanonicalState node group name snapshot)
  node group name snapshot (CanonicalRep node group name snapshot)

private theorem vc_step_from
    (pre : Theory node group name snapshot → CanonicalState node group name snapshot → Prop)
    (act : Veil.VeilM Veil.Mode.external (Theory node group name snapshot)
      (CanonicalState node group name snapshot) Unit)
    (h : act.meetsSpecificationIfSuccessfulAssuming TheoryAssumptions pre
      (fun th st => registrySafety th st))
    (th : Theory node group name snapshot) (st st' : CanonicalState node group name snapshot)
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
    (th : Theory node group name snapshot) (st st' : CanonicalState node group name snapshot)
    (label : Label node group name snapshot)
    (ha : TheoryAssumptions th) (hi : Safe th st)
    (ht : GroupsNext th st label st') : Safe th st' := by
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
      (initializer.ext.tr (Theory node group name snapshot) (CanonicalState node group name snapshot)
        node group name snapshot (CanonicalRep node group name snapshot))
      TheoryAssumptions (fun _ _ => True) (fun th st => registrySafety th st) := by
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  rcases htr with ⟨hpub, hknown, hpending, hhead, _⟩
  simp [hpub, hknown, hpending, ← hhead, has.2.1, has.2.2]

theorem initial_safe
    (th : Theory node group name snapshot) (st : CanonicalState node group name snapshot)
    (ha : TheoryAssumptions th) (ht : GroupsInit th st) : Safe th st := by
  exact initializer_transition_safe th default st ⟨ha, trivial⟩ ht

inductive Reachable (th : Theory node group name snapshot) :
    CanonicalState node group name snapshot → Prop where
  | initial {st} : GroupsInit th st → Reachable th st
  | step {st st'} {label : Label node group name snapshot} : Reachable th st →
      GroupsNext th st label st' → Reachable th st'
  | stutter {st} : Reachable th st → Reachable th st

theorem reachable_safe
    (th : Theory node group name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node group name snapshot} (hr : Reachable th st) : Safe th st := by
  induction hr with
  | initial hi => exact initial_safe th _ ha hi
  | step hr ht ih => exact next_safe th _ _ _ ha ih ht
  | stutter hr ih => exact ih


private theorem vc_ancestor_step_from
    (act : Veil.VeilM Veil.Mode.external (Theory node group name snapshot)
      (CanonicalState node group name snapshot) Unit)
    (h : act.meetsSpecificationIfSuccessfulAssuming TheoryAssumptions AncestorPre AncestorSafe)
    (th : Theory node group name snapshot) (st st' : CanonicalState node group name snapshot)
    (ha : TheoryAssumptions th) (hs : Safe th st) (hi : AncestorSafe th st)
    (ht : act.toTransitionDerived th st st') : AncestorSafe th st' := by
  have htr : act.toTransition.meetsSpecificationIfSuccessful
      (fun th st => TheoryAssumptions th ∧ AncestorPre th st) AncestorSafe := by
    rw [Veil.Transition.meetsSpecificationIfSuccessful_eq]
    exact h
  rw [Veil.VeilM.toTransitionDerived_sound] at htr
  exact htr th st st' ⟨ha, hs, hi⟩ ht

theorem next_ancestor_safe
    (th : Theory node group name snapshot) (st st' : CanonicalState node group name snapshot)
    (label : Label node group name snapshot)
    (ha : TheoryAssumptions th) (hs : Safe th st) (hi : AncestorSafe th st)
    (ht : GroupsNext th st label st') : AncestorSafe th st' := by
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
      (initializer.ext.tr (Theory node group name snapshot) (CanonicalState node group name snapshot)
        node group name snapshot (CanonicalRep node group name snapshot))
      TheoryAssumptions (fun _ _ => True) AncestorSafe := by
  unfold AncestorSafe
  unveil
  try simp [canonicalFieldRep, Veil.FieldRepresentation.get, Veil.FieldRepresentation.setSingle,
    Veil.canonicalFieldRepresentation, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp] at *
  rcases htr with ⟨hpub, hknown, hpending, hhead, _⟩
  simp [hpub, hpending]

theorem initial_ancestor_safe
    (th : Theory node group name snapshot) (st : CanonicalState node group name snapshot)
    (ha : TheoryAssumptions th) (ht : GroupsInit th st) : AncestorSafe th st := by
  exact initializer_transition_ancestor_safe th default st ⟨ha, trivial⟩ ht

theorem reachable_ancestor_safe
    (th : Theory node group name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node group name snapshot} (hr : Reachable th st) :
    AncestorSafe th st := by
  induction hr with
  | initial hi => exact initial_ancestor_safe th _ ha hi
  | step hr ht ih => exact next_ancestor_safe th _ _ _ ha (reachable_safe th ha hr) ih ht
  | stutter hr ih => exact ih


theorem dependency_acyclic
    (th : Theory node group name snapshot) (st : CanonicalState node group name snapshot)
    (hs : Safe th st) (T : group → Prop)
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
    (th : Theory node group name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node group name snapshot} (hr : Reachable th st)
    (n : node) (d : group) (hk : st.known n d = true) : st.published d = true :=
  (reachable_safe th ha hr).2.2.1 n d hk

theorem published_valid
    (th : Theory node group name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node group name snapshot} (hr : Reachable th st)
    (d : group) (hp : st.published d = true) : th.valid d = true :=
  (reachable_safe th ha hr).1 d hp

theorem published_closed
    (th : Theory node group name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node group name snapshot} (hr : Reachable th st)
    (d e : group) (hp : st.published d = true) (hd : th.deps d e = true) :
    st.published e = true :=
  (reachable_safe th ha hr).2.1 d e hp hd

theorem snapshot_safe
    (th : Theory node group name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node group name snapshot} (hr : Reachable th st) (n : node) :
    buildable (st.head n) th st ∧
      ∀ d, th.contents (st.head n) d = true → st.published d = true := by
  have hs := reachable_safe th ha hr
  exact ⟨hs.2.2.2.2.1 n, hs.2.2.2.2.2.1 n⟩

theorem reachable_acyclic
    (th : Theory node group name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node group name snapshot} (hr : Reachable th st)
    (T : group → Prop) (hsub : ∀ d, T d → st.published d = true) (hne : ∃ d, T d) :
    ∃ d, T d ∧ ∀ e, T e → th.deps d e ≠ true :=
  dependency_acyclic th st (reachable_safe th ha hr) T hsub hne


theorem published_ancestors_closed
    (th : Theory node group name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node group name snapshot} (hr : Reachable th st)
    (d e : group) (hp : st.published d = true) (he : th.ancestors d e = true) :
    st.published e = true :=
  (reachable_ancestor_safe th ha hr).1 d e hp he

theorem pending_ancestors_closed
    (th : Theory node group name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node group name snapshot} (hr : Reachable th st)
    (n : node) (d e : group) (hp : st.pending n d = true) (he : th.ancestors d e = true) :
    st.published e = true :=
  (reachable_ancestor_safe th ha hr).2.1 n d hp e he

theorem published_ancestor_rank
    (th : Theory node group name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node group name snapshot} (hr : Reachable th st)
    (d e : group) (hp : st.published d = true) (he : th.ancestors d e = true) :
    st.rank e < st.rank d :=
  (reachable_ancestor_safe th ha hr).2.2 d e hp he

theorem published_no_self_ancestor
    (th : Theory node group name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node group name snapshot} (hr : Reachable th st)
    (d : group) (hp : st.published d = true) : th.ancestors d d ≠ true := by
  intro he
  exact Nat.lt_irrefl _ (published_ancestor_rank th ha hr d d hp he)

theorem ancestor_acyclic
    (th : Theory node group name snapshot) (st : CanonicalState node group name snapshot)
    (hs : AncestorSafe th st) (T : group → Prop)
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
    (th : Theory node group name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node group name snapshot} (hr : Reachable th st)
    (T : group → Prop) (hsub : ∀ d, T d → st.published d = true) (hne : ∃ d, T d) :
    ∃ d, T d ∧ ∀ e, T e → th.ancestors d e ≠ true :=
  ancestor_acyclic th st (reachable_ancestor_safe th ha hr) T hsub hne

/-- Two heads for any included name block a current checkpoint. -/
theorem collision_blocks_current
    (th : Theory node group name snapshot) (st : CanonicalState node group name snapshot)
    (n : node) (S : snapshot) (a b d : group) (x : name)
    (ha : isHead n a x th st) (hb : isHead n b x th st)
    (hne : a ≠ b) (hd : th.contents S d = true) (hx : th.member d x = true) :
    ¬current n S th st := by
  intro hc
  exact hne (((hc d x hd hx a).1 ha).trans ((hc d x hd hx b).1 hb).symm)

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
attribute [local instance] Classical.propDecidable

theorem publish_enabled_iff
    (th : Theory node group name snapshot) (st : CanonicalState node group name snapshot)
    (n : node) (g : group) :
    (∃ st', GroupsNext th st (.publish n g) st') ↔
      st.alive n = true ∧ st.online n = true ∧ st.pending n g = true := by
  simp only [GroupsNext, Next, NextAct, publish.ext.derived_eq]
  dsimp [publish.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
    Veil.canonicalFieldRepresentation]
  by_cases hp : st.published g = true <;> simp [hp]

/-- Published bindings are an expansion of the single group publication bit. -/
def PublishedBinding (th : Theory node group name snapshot)
    (st : CanonicalState node group name snapshot) (g : group) (x : name) : Prop :=
  st.published g = true ∧ th.member g x = true

/-- Snapshot bindings are an expansion of immutable group contents. -/
def SnapshotBinding (th : Theory node group name snapshot)
    (S : snapshot) (g : group) (x : name) : Prop :=
  th.contents S g = true ∧ th.member g x = true

theorem no_subset_publication (th : Theory node group name snapshot)
    (st : CanonicalState node group name snapshot) (g : group) (x y : name)
    (hx : th.member g x = true) (hy : th.member g y = true) :
    PublishedBinding th st g x ↔ PublishedBinding th st g y := by
  simp [PublishedBinding, hx, hy]

theorem no_subset_snapshot (th : Theory node group name snapshot)
    (S : snapshot) (g : group) (x y : name)
    (hx : th.member g x = true) (hy : th.member g y = true) :
    SnapshotBinding th S g x ↔ SnapshotBinding th S g y := by
  simp [SnapshotBinding, hx, hy]

theorem snapshot_no_duplicate_name
    (th : Theory node group name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node group name snapshot} (hr : Reachable th st)
    (n : node) (g h : group) (x : name)
    (hg : SnapshotBinding th (st.head n) g x)
    (hh : SnapshotBinding th (st.head n) h x) : g = h :=
  (snapshot_safe th ha hr n).1.2.2.1 g h x hg.1 hh.1 hg.2 hh.2

theorem snapshot_exact_dependency
    (th : Theory node group name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node group name snapshot} (hr : Reachable th st)
    (n : node) (g h : group) (hg : th.contents (st.head n) g = true)
    (hd : th.deps g h = true) : th.contents (st.head n) h = true :=
  (snapshot_safe th ha hr n).1.2.1 g h hg hd

theorem commit_enabled_iff
    (th : Theory node group name snapshot) (st : CanonicalState node group name snapshot)
    (n : node) (S : snapshot) :
    (∃ st', GroupsNext th st (.commit n S) st') ↔
      st.alive n = true ∧ st.online n = true ∧
      (∀ d, th.contents S d = true → st.known n d = true) ∧
      buildable S th st ∧ current n S th st := by
  simp only [GroupsNext, Next, NextAct, commit.ext.derived_eq]
  dsimp [commit.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
    Veil.canonicalFieldRepresentation]
  constructor
  · rintro ⟨st', ha, ho, hk, hv, hd, hu, he, hc, _⟩
    exact ⟨ha, ho, hk, ⟨hv, hd, hu, he⟩, hc⟩
  · rintro ⟨ha, ho, hk, hb, hc⟩
    rcases hb with ⟨hv, hd, hu, he⟩
    exact ⟨_, ha, ho, hk, hv, hd, hu, he, hc, rfl⟩

theorem commit_fresh
    (th : Theory node group name snapshot) (st st' : CanonicalState node group name snapshot)
    (n : node) (S : snapshot) (ht : GroupsNext th st (.commit n S) st') :
    current n S th st ∧ st'.head n = S := by
  simp only [GroupsNext, Next, NextAct, commit.ext.derived_eq] at ht
  dsimp [commit.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
    Veil.canonicalFieldRepresentation] at ht
  rcases ht with ⟨_, _, _, _, _, _, _, hc, hs⟩
  subst st'
  refine ⟨hc, ?_⟩
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

theorem commit_unique_head_for_every_name
    (th : Theory node group name snapshot) (st st' : CanonicalState node group name snapshot)
    (n : node) (S : snapshot) (ht : GroupsNext th st (.commit n S) st')
    (g h : group) (x : name) (hg : th.contents S g = true)
    (hx : th.member g x = true) : isHead n h x th st ↔ h = g :=
  (commit_fresh th st st' n S ht).1 g x hg hx h

theorem stale_name_blocks_commit
    (th : Theory node group name snapshot) (st st' : CanonicalState node group name snapshot)
    (n : node) (S : snapshot) (g h : group) (x : name)
    (hg : th.contents S g = true) (hx : th.member g x = true)
    (hk : st.known n h = true) (ha : th.revisions h g x = true) :
    ¬GroupsNext th st (.commit n S) st' := by
  intro ht
  have hh := (commit_unique_head_for_every_name th st st' n S ht g g x hg hx).2 rfl
  exact hh.2.2 ⟨h, hk, ha⟩

theorem overlapping_heads_block_commit
    (th : Theory node group name snapshot) (st st' : CanonicalState node group name snapshot)
    (n : node) (S : snapshot) (a b g : group) (x : name)
    (ha : isHead n a x th st) (hb : isHead n b x th st)
    (hne : a ≠ b) (hg : th.contents S g = true) (hx : th.member g x = true) :
    ¬GroupsNext th st (.commit n S) st' := by
  intro ht
  exact collision_blocks_current th st n S a b g x ha hb hne hg hx
    (commit_fresh th st st' n S ht).1

/-- Compatibility catches collisions pulled into the snapshot through dependencies. -/
theorem transitive_name_conflict_blocks_buildable
    (th : Theory node group name snapshot) (st : CanonicalState node group name snapshot)
    (S : snapshot) (a b u v : group) (x : name)
    (ha : th.contents S a = true) (hb : th.contents S b = true)
    (hau : th.deps a u = true) (hbv : th.deps b v = true)
    (hux : th.member u x = true) (hvx : th.member v x = true) (hne : u ≠ v) :
    ¬buildable S th st := by
  rintro ⟨_, hd, hu, _⟩
  exact hne (hu u v x (hd a u ha hau) (hd b v hb hbv) hux hvx)

/-- An old checkpoint's structural meaning is independent of changing knowledge. -/
theorem old_snapshot_preserved
    (th : Theory node group name snapshot) (st st' : CanonicalState node group name snapshot)
    (S : snapshot) (hs : buildable S th st) : buildable S th st' := hs

/-- The singleton-name specialization keeps exact Registry snapshot meaning. -/
def singletonTheory (th : ParaleanRegistry.Theory node group name snapshot) :
    Theory node group name snapshot where
  valid := th.valid
  deps := th.deps
  ancestors := th.ancestors
  member := fun g x => decide (th.declName g = x)
  revisions := fun g a x => th.ancestors g a && decide (th.declName g = x)
  contents := th.contents
  exportable := th.exportable
  emptySnapshot := th.emptySnapshot

theorem singleton_buildable_iff
    (th : ParaleanRegistry.Theory node group name snapshot)
    (st : CanonicalState node group name snapshot)
    (rst : ParaleanRegistry.CanonicalState node group name snapshot) (S : snapshot) :
    buildable S (singletonTheory th) st ↔ ParaleanRegistry.buildable S th rst := by
  dsimp [buildable, ParaleanRegistry.buildable, singletonTheory, readFrom, instIsSubReaderOfRefl]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨hv, hd, hu, he⟩
    exact ⟨hv, hd, fun g h hg hh hn => hu g h (th.declName g) hg hh rfl hn.symm, he⟩
  · rintro ⟨hv, hd, hu, he⟩
    exact ⟨hv, hd, fun g h x hg hh hx hy => hu g h hg hh (hx.trans hy.symm), he⟩

theorem singleton_assumptions
    (th : ParaleanRegistry.Theory node group name snapshot)
    (ha : ParaleanRegistry.TheoryAssumptions th) : TheoryAssumptions (singletonTheory th) := by
  dsimp [TheoryAssumptions, Assumptions, valid_ancestry, empty_contents, empty_exportable,
    singletonTheory, readFrom, instIsSubReaderOfRefl]
  refine ⟨⟨?_, ?_, ?_⟩, ha.2⟩
  · intro g a
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun hg => ⟨th.declName g, hg, rfl⟩, fun ⟨_, hg, _⟩ => hg⟩
  · intro g a x hv he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at he ⊢
    have hschema := ha.1 g hv a he.1
    refine ⟨he.2, hschema.1.trans he.2, ?_⟩
    intro b hb
    exact ⟨hschema.2 b hb.1, he.2⟩
  · intro g _
    exact ⟨th.declName g, by simp⟩

/-- A resolving group can replace every known overlapping binding independently. -/
theorem resolved_group_current
    (th : Theory node group name snapshot) (st : CanonicalState node group name snapshot)
    (n : node) (S : snapshot) (g : group)
    (selected : ∀ h, th.contents S h = true ↔ h = g)
    (known : st.known n g = true)
    (fresh : ∀ x, th.member g x = true → ¬∃ h, st.known n h = true ∧ th.revisions h g x = true)
    (resolved : ∀ h x, st.known n h = true → th.member h x = true →
      th.member g x = true → h = g ∨ th.revisions g h x = true) :
    current n S th st := by
  intro d x hd hx h
  have eq := (selected d).1 hd
  subst d
  constructor
  · rintro ⟨hk, hm, hn⟩
    rcases resolved h x hk hm hx with he | hr
    · exact he
    · exact False.elim (hn ⟨g, known, hr⟩)
  · intro he
    subst h
    exact ⟨known, hx, fresh x hx⟩

theorem resolved_group_commit_enabled
    (th : Theory node group name snapshot) (st : CanonicalState node group name snapshot)
    (n : node) (S : snapshot) (g : group)
    (ready : st.alive n = true ∧ st.online n = true)
    (selected : ∀ h, th.contents S h = true ↔ h = g)
    (known : st.known n g = true) (build : buildable S th st)
    (fresh : ∀ x, th.member g x = true → ¬∃ h, st.known n h = true ∧ th.revisions h g x = true)
    (resolved : ∀ h x, st.known n h = true → th.member h x = true →
      th.member g x = true → h = g ∨ th.revisions g h x = true) :
    ∃ st', GroupsNext th st (.commit n S) st' := by
  apply (commit_enabled_iff th st n S).2
  refine ⟨ready.1, ready.2, ?_, build, resolved_group_current th st n S g selected known fresh resolved⟩
  intro h hh
  exact (selected h).1 hh ▸ known

theorem published_revision_closed
    (th : Theory node group name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node group name snapshot} (hr : Reachable th st)
    (g a : group) (x : name) (hp : st.published g = true)
    (he : th.revisions g a x = true) : st.published a = true := by
  apply published_ancestors_closed th ha hr g a hp
  exact (ha.1.1 g a).2 ⟨x, he⟩

theorem published_revision_rank
    (th : Theory node group name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node group name snapshot} (hr : Reachable th st)
    (g a : group) (x : name) (hp : st.published g = true)
    (he : th.revisions g a x = true) : st.rank a < st.rank g := by
  apply published_ancestor_rank th ha hr g a hp
  exact (ha.1.1 g a).2 ⟨x, he⟩

end Proofs

noncomputable section OverlapExample
attribute [local instance] Classical.propDecidable

/-- Groups 0={x,y}, 1={y,z}, 2={x,y,z}. Group 2 resolves both old groups per name. -/
def overlapTheory : Theory Unit (Fin 3) (Fin 3) Bool where
  valid := fun _ => true
  deps := fun _ _ => false
  ancestors := fun g a => decide (g = 2 ∧ a ≠ 2)
  member := fun g x => decide (g = 2 ∨ (g = 0 ∧ x ≠ 2) ∨ (g = 1 ∧ x ≠ 0))
  revisions := fun g a x => decide (g = 2 ∧ a ≠ 2 ∧
    (a = 0 ∧ x ≠ 2 ∨ a = 1 ∧ x ≠ 0))
  contents := fun S g => decide (S = true ∧ g = 2)
  exportable := fun _ => true
  emptySnapshot := false

def overlapState : CanonicalState Unit (Fin 3) (Fin 3) Bool where
  published := fun _ => true
  known := fun _ _ => true
  pending := fun _ _ => false
  head := fun _ => false
  alive := fun _ => true
  online := fun _ => true
  stable := false
  clock := 3
  rank := fun g => g.val

def overlapProgress (k : Nat) (p : Option (Fin 3)) :
    CanonicalState Unit (Fin 3) (Fin 3) Bool where
  published := fun g => decide (g.val < k)
  known := fun _ g => decide (g.val < k)
  pending := fun _ g => decide (p = some g)
  head := fun _ => false
  alive := fun _ => true
  online := fun _ => true
  stable := false
  clock := k
  rank := fun g => if g.val < k then g.val else 0

theorem overlap_initial : GroupsInit overlapTheory (overlapProgress 0 none) := by
  dsimp [GroupsInit, Init, initializer.ext.tr, overlapProgress, overlapTheory, getFrom, setIn,
    readFrom, Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    canonicalFieldRep, Veil.canonicalFieldRepresentation]
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

theorem overlap_prepare_step (g : Fin 3) :
    GroupsNext overlapTheory (overlapProgress g.val none) (.prepare () g)
      (overlapProgress g.val (some g)) := by
  simp only [GroupsNext, Next, NextAct, prepare.ext.derived_eq]
  dsimp [prepare.ext.tr, overlapProgress, overlapTheory, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    canonicalFieldRep, Veil.canonicalFieldRepresentation]
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]
  repeat' constructor
  all_goals first | (intro a ha; simp_all; omega) | (ext n a; simp; omega) | omega

theorem overlap_publish_step (g : Fin 3) :
    GroupsNext overlapTheory (overlapProgress g.val (some g)) (.publish () g)
      (overlapProgress (g.val + 1) none) := by
  simp only [GroupsNext, Next, NextAct, publish.ext.derived_eq]
  dsimp [publish.ext.tr, overlapProgress, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    canonicalFieldRep, Veil.canonicalFieldRepresentation]
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]
  constructor
  · intro a
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq, Fin.ext_iff]
    omega
  · intro a
    by_cases he : g = a
    · subst a; simp
    · have hv : g.val ≠ a.val := fun hv => he (Fin.ext hv)
      simp only [if_neg he]
      split_ifs <;> first | rfl | omega

theorem overlap_reachable : Reachable overlapTheory overlapState := by
  have h0 := Reachable.initial overlap_initial
  have h1 := Reachable.step h0 (overlap_prepare_step 0)
  have h2 := Reachable.step h1 (overlap_publish_step 0)
  have h3 := Reachable.step h2 (overlap_prepare_step 1)
  have h4 := Reachable.step h3 (overlap_publish_step 1)
  have h5 := Reachable.step h4 (overlap_prepare_step 2)
  have h6 := Reachable.step h5 (overlap_publish_step 2)
  have he : overlapProgress 3 none = overlapState := by
    ext n g <;> simp [overlapProgress, overlapState] <;> omega
  exact he ▸ h6

theorem overlap_assumptions : TheoryAssumptions overlapTheory := by
  decide

theorem overlap_three_names : ∀ x : Fin 3, overlapTheory.member 2 x = true := by
  decide

theorem overlap_resolves_both :
    overlapTheory.revisions 2 0 0 = true ∧ overlapTheory.revisions 2 0 1 = true ∧
    overlapTheory.revisions 2 1 1 = true ∧ overlapTheory.revisions 2 1 2 = true := by
  decide

theorem overlap_safe : Safe overlapTheory overlapState ∧ AncestorSafe overlapTheory overlapState := by
  decide

/-- A checked overlapping resolution has an actual generated successful commit. -/
theorem overlap_commit_success :
    ∃ st', GroupsNext overlapTheory overlapState (.commit () true) st' ∧ st'.head () = true := by
  have ready : overlapState.alive () = true ∧ overlapState.online () = true := by decide
  have selected : ∀ h, overlapTheory.contents true h = true ↔ h = 2 := by decide
  have known : overlapState.known () 2 = true := by decide
  have hb : buildable true overlapTheory overlapState := by decide
  have fresh : ∀ x, overlapTheory.member 2 x = true →
      ¬∃ h, overlapState.known () h = true ∧ overlapTheory.revisions h 2 x = true := by decide
  have resolved : ∀ h x, overlapState.known () h = true → overlapTheory.member h x = true →
      overlapTheory.member 2 x = true → h = 2 ∨ overlapTheory.revisions 2 h x = true := by decide
  obtain ⟨st', ht⟩ := resolved_group_commit_enabled overlapTheory overlapState () true 2
    ready selected known hb fresh resolved
  exact ⟨st', ht, (commit_fresh overlapTheory overlapState st' () true ht).2⟩

theorem overlap_pipeline_success :
    ∃ st', Reachable overlapTheory st' ∧ st'.head () = true ∧
      ∀ x : Fin 3, SnapshotBinding overlapTheory (st'.head ()) 2 x := by
  obtain ⟨st', ht, hh⟩ := overlap_commit_success
  refine ⟨st', Reachable.step overlap_reachable ht, hh, ?_⟩
  intro x
  rw [hh]
  exact ⟨by decide, overlap_three_names x⟩

end OverlapExample

#print axioms published_revision_closed
#print axioms published_revision_rank
#print axioms overlap_initial
#print axioms overlap_prepare_step
#print axioms overlap_publish_step
#print axioms overlap_reachable
#print axioms overlap_assumptions
#print axioms overlap_three_names
#print axioms overlap_resolves_both
#print axioms overlap_safe
#print axioms overlap_commit_success
#print axioms overlap_pipeline_success

#print axioms publish_enabled_iff
#print axioms no_subset_publication
#print axioms no_subset_snapshot
#print axioms snapshot_no_duplicate_name
#print axioms snapshot_exact_dependency
#print axioms commit_enabled_iff
#print axioms commit_fresh
#print axioms commit_unique_head_for_every_name
#print axioms stale_name_blocks_commit
#print axioms overlapping_heads_block_commit
#print axioms transitive_name_conflict_blocks_buildable
#print axioms old_snapshot_preserved
#print axioms singleton_buildable_iff
#print axioms singleton_assumptions
#print axioms resolved_group_current
#print axioms resolved_group_commit_enabled
end ParaleanGroups

namespace ParaleanGroupComposition

abbrev DiskRep (replica obj writeQuorum readQuorum : Type) (f : Durability.State.Label) :=
  Veil.CanonicalField (Durability.State.Label.toDomain replica obj writeQuorum readQuorum f)
    (Durability.State.Label.toCodomain replica obj writeQuorum readQuorum f)

abbrev DiskState (replica obj writeQuorum readQuorum : Type) :=
  Durability.State (DiskRep replica obj writeQuorum readQuorum)

structure Theory (node group name snapshot replica obj writeQuorum readQuorum : Type) where
  registry : ParaleanGroups.Theory node group name snapshot
  storage : Durability.Theory replica obj writeQuorum readQuorum
  payload : group → obj
  manifest : snapshot → obj

structure State (node group name snapshot replica obj writeQuorum readQuorum : Type) where
  registry : ParaleanGroups.CanonicalState node group name snapshot
  storage : DiskState replica obj writeQuorum readQuorum

noncomputable section Proofs
variable {node group name snapshot replica obj writeQuorum readQuorum : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]
  [DecidableEq replica] [Inhabited replica] [DecidableEq obj] [Inhabited obj]
  [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum]

@[reducible] instance diskFieldRep : ∀ f, Veil.FieldRepresentation
    (Durability.State.Label.toDomain replica obj writeQuorum readQuorum f)
    (Durability.State.Label.toCodomain replica obj writeQuorum readQuorum f)
    (DiskRep replica obj writeQuorum readQuorum f) := by
  intro f
  cases f <;> (apply Veil.canonicalFieldRepresentation; infer_instance_for_iterated_prod)

instance diskFieldRepLawful : ∀ f, Veil.LawfulFieldRepresentation
    (Durability.State.Label.toDomain replica obj writeQuorum readQuorum f)
    (Durability.State.Label.toCodomain replica obj writeQuorum readQuorum f)
    (DiskRep replica obj writeQuorum readQuorum f) (diskFieldRep f) := by
  intro f
  cases f <;> apply Veil.canonicalFieldRepresentationLawful

instance diskStateInhabited : Inhabited (DiskState replica obj writeQuorum readQuorum) :=
  ⟨⟨fun _ _ => false, fun _ => true, fun _ => false, fun _ => default⟩⟩

local instance : delta% @Durability.Ack._veil_dec_type_0 obj writeQuorum replica readQuorum
    (DiskRep replica obj writeQuorum readQuorum) diskFieldRep :=
  fun _ _ _ _ => Classical.propDecidable _
local instance : delta% @Durability.Lose._veil_dec_type_0 replica obj writeQuorum readQuorum
    (DiskRep replica obj writeQuorum readQuorum) diskFieldRep :=
  fun _ _ _ => Classical.propDecidable _

abbrev StorageInit := Durability.Init (Durability.Theory replica obj writeQuorum readQuorum)
  (DiskState replica obj writeQuorum readQuorum) replica obj writeQuorum readQuorum
  (DiskRep replica obj writeQuorum readQuorum)
abbrev StorageNext := Durability.Next (Durability.Theory replica obj writeQuorum readQuorum)
  (DiskState replica obj writeQuorum readQuorum) replica obj writeQuorum readQuorum
  (DiskRep replica obj writeQuorum readQuorum)
abbrev StorageSafe := Durability.Invariants (Durability.Theory replica obj writeQuorum readQuorum)
  (DiskState replica obj writeQuorum readQuorum) replica obj writeQuorum readQuorum
  (DiskRep replica obj writeQuorum readQuorum)
abbrev StorageAssumptions := Durability.Assumptions (Durability.Theory replica obj writeQuorum readQuorum)
  replica obj writeQuorum readQuorum

def Assumptions (th : Theory node group name snapshot replica obj writeQuorum readQuorum) : Prop :=
  ParaleanGroups.TheoryAssumptions th.registry ∧ StorageAssumptions th.storage

/-- The baseline empty checkpoint has no stored manifest obligation. -/
def Coupled (th : Theory node group name snapshot replica obj writeQuorum readQuorum)
    (rg : ParaleanGroups.CanonicalState node group name snapshot)
    (disk : DiskState replica obj writeQuorum readQuorum) : Prop :=
  (∀ d, rg.published d = true → disk.acknowledged (th.payload d) = true) ∧
  (∀ n, rg.head n ≠ th.registry.emptySnapshot → disk.acknowledged (th.manifest (rg.head n)) = true)

def Guard (th : Theory node group name snapshot replica obj writeQuorum readQuorum)
    (disk : DiskState replica obj writeQuorum readQuorum) :
    ParaleanGroups.Label node group name snapshot → Prop
  | .publish _ d => disk.acknowledged (th.payload d) = true
  | .commit _ S => disk.acknowledged (th.manifest S) = true
  | _ => True

def Init (th : Theory node group name snapshot replica obj writeQuorum readQuorum)
    (s : State node group name snapshot replica obj writeQuorum readQuorum) : Prop :=
  ParaleanGroups.GroupsInit th.registry s.registry ∧ StorageInit th.storage s.storage

inductive Next (th : Theory node group name snapshot replica obj writeQuorum readQuorum) :
    State node group name snapshot replica obj writeQuorum readQuorum →
    State node group name snapshot replica obj writeQuorum readQuorum → Prop where
  | registry {rg rg' disk} (label : ParaleanGroups.Label node group name snapshot) :
      ParaleanGroups.GroupsNext th.registry rg label rg' → Guard th disk label →
      Next th ⟨rg, disk⟩ ⟨rg', disk⟩
  | storage {rg disk disk'} (label : Durability.Label replica obj writeQuorum readQuorum) :
      StorageNext th.storage disk label disk' → Next th ⟨rg, disk⟩ ⟨rg, disk'⟩
  | stutter {s} : Next th s s

def Safe (th : Theory node group name snapshot replica obj writeQuorum readQuorum)
    (s : State node group name snapshot replica obj writeQuorum readQuorum) : Prop :=
  ParaleanGroups.Safe th.registry s.registry ∧
    StorageSafe th.storage s.storage ∧ Coupled th s.registry s.storage

theorem storage_acknowledged_mono (th : Durability.Theory replica obj writeQuorum readQuorum)
    (s s' : DiskState replica obj writeQuorum readQuorum)
    (label : Durability.Label replica obj writeQuorum readQuorum)
    (ht : StorageNext th s label s') :
    ∀ o, s.acknowledged o = true → s'.acknowledged o = true := by
  cases label <;>
    simp only [StorageNext, Durability.Next, Durability.NextAct,
      Durability.Put.ext.derived_eq, Durability.Ack.ext.derived_eq,
      Durability.Lose.ext.derived_eq] at ht
  all_goals
    dsimp [Durability.Put.ext.tr, Durability.Ack.ext.tr, Durability.Lose.ext.tr,
      getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
      instIsSubStateOfRefl, instIsSubReaderOfRefl, diskFieldRep,
      Veil.canonicalFieldRepresentation] at ht
    repeat' rcases ht with ⟨ha, ht⟩
    try subst s'
    simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp]
    try grind

omit [DecidableEq replica] [Inhabited replica] [DecidableEq obj] [Inhabited obj]
  [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum] in
theorem registry_preserves_coupling
    (th : Theory node group name snapshot replica obj writeQuorum readQuorum)
    (rg rg' : ParaleanGroups.CanonicalState node group name snapshot)
    (disk : DiskState replica obj writeQuorum readQuorum)
    (label : ParaleanGroups.Label node group name snapshot)
    (hc : Coupled th rg disk) (hg : Guard th disk label)
    (ht : ParaleanGroups.GroupsNext th.registry rg label rg') : Coupled th rg' disk := by
  cases label <;>
    simp only [ParaleanGroups.GroupsNext, ParaleanGroups.Next, ParaleanGroups.NextAct,
      ParaleanGroups.prepare.ext.derived_eq, ParaleanGroups.publish.ext.derived_eq,
      ParaleanGroups.receive.ext.derived_eq, ParaleanGroups.commit.ext.derived_eq,
      ParaleanGroups.crash.ext.derived_eq, ParaleanGroups.recover.ext.derived_eq,
      ParaleanGroups.partition.ext.derived_eq, ParaleanGroups.reconnect.ext.derived_eq,
      ParaleanGroups.heal.ext.derived_eq] at ht
  all_goals
    dsimp [ParaleanGroups.prepare.ext.tr, ParaleanGroups.publish.ext.tr,
      ParaleanGroups.receive.ext.tr, ParaleanGroups.commit.ext.tr,
      ParaleanGroups.crash.ext.tr, ParaleanGroups.recover.ext.tr,
      ParaleanGroups.partition.ext.tr, ParaleanGroups.reconnect.ext.tr,
      ParaleanGroups.heal.ext.tr, getFrom, setIn, readFrom,
      Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
      ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation] at ht
    try split_ifs at ht
    all_goals
      repeat' rcases ht with ⟨ha, ht⟩
      try subst rg'
      simp only [Coupled, Guard] at *
      simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
        Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
        Veil.IteratedProd.patCmp] at *
      grind

omit [DecidableEq replica] [Inhabited replica] [DecidableEq obj] [Inhabited obj]
  [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum] in
theorem initial_coupled
    (th : Theory node group name snapshot replica obj writeQuorum readQuorum)
    (rg : ParaleanGroups.CanonicalState node group name snapshot)
    (disk : DiskState replica obj writeQuorum readQuorum)
    (ht : ParaleanGroups.GroupsInit th.registry rg) : Coupled th rg disk := by
  dsimp [ParaleanGroups.GroupsInit, ParaleanGroups.Init,
    ParaleanGroups.initializer.ext.tr, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation] at ht
  subst rg
  simp [Coupled, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

theorem initial_safe
    (th : Theory node group name snapshot replica obj writeQuorum readQuorum)
    (ha : Assumptions th)
    (s : State node group name snapshot replica obj writeQuorum readQuorum)
    (ht : Init th s) : Safe th s := by
  exact ⟨ParaleanGroups.initial_safe th.registry s.registry ha.1 ht.1,
    Durability.Init_preserves _ _ replica obj writeQuorum readQuorum
      (DiskRep replica obj writeQuorum readQuorum) th.storage s.storage ha.2 ht.2,
    initial_coupled th s.registry s.storage ht.1⟩

theorem next_safe
    (th : Theory node group name snapshot replica obj writeQuorum readQuorum)
    (ha : Assumptions th)
    (s s' : State node group name snapshot replica obj writeQuorum readQuorum)
    (hs : Safe th s) (ht : Next th s s') : Safe th s' := by
  cases ht with
  | registry label ht hg =>
    exact ⟨ParaleanGroups.next_safe th.registry _ _ label ha.1 hs.1 ht,
      hs.2.1, registry_preserves_coupling th _ _ _ label hs.2.2 hg ht⟩
  | storage label ht =>
    refine ⟨hs.1,
      Durability.Next_preserves _ _ replica obj writeQuorum readQuorum
        (DiskRep replica obj writeQuorum readQuorum) th.storage _ _ label ha.2 hs.2.1 ht,
      ?_⟩
    have hm := storage_acknowledged_mono th.storage _ _ label ht
    exact ⟨fun d hd => hm _ (hs.2.2.1 d hd), fun n hn => hm _ (hs.2.2.2 n hn)⟩
  | stutter => exact hs

inductive Reachable (th : Theory node group name snapshot replica obj writeQuorum readQuorum) :
    State node group name snapshot replica obj writeQuorum readQuorum → Prop where
  | initial {s} : Init th s → Reachable th s
  | step {s s'} : Reachable th s → Next th s s' → Reachable th s'

theorem reachable_safe
    (th : Theory node group name snapshot replica obj writeQuorum readQuorum)
    (ha : Assumptions th)
    {s : State node group name snapshot replica obj writeQuorum readQuorum}
    (hr : Reachable th s) : Safe th s := by
  induction hr with
  | initial hi => exact initial_safe th ha _ hi
  | step hr ht ih => exact next_safe th ha _ _ ih ht

omit [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot] in
theorem acknowledged_recoverable
    (th : Theory node group name snapshot replica obj writeQuorum readQuorum)
    (disk : DiskState replica obj writeQuorum readQuorum)
    (ha : StorageAssumptions th.storage) (hs : StorageSafe th.storage disk)
    (o : obj) (q : readQuorum) (hack : disk.acknowledged o = true)
    (hq : ∀ r, th.storage.memberR r q = true → disk.live r = true) :
    disk.live (th.storage.meet (disk.witness o) q) = true ∧
      disk.stored (th.storage.meet (disk.witness o) q) o = true := by
  have hrec := Durability.invariants_recoverable
    (Durability.Theory replica obj writeQuorum readQuorum)
    (DiskState replica obj writeQuorum readQuorum) replica obj writeQuorum readQuorum
    (DiskRep replica obj writeQuorum readQuorum) th.storage disk ha hs
  dsimp [Durability.Recoverable, getFrom, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, diskFieldRep,
    Veil.canonicalFieldRepresentation] at hrec
  exact hrec o q hack hq

omit [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot] in
theorem acknowledged_has_copy
    (th : Theory node group name snapshot replica obj writeQuorum readQuorum)
    (disk : DiskState replica obj writeQuorum readQuorum)
    (ha : StorageAssumptions th.storage) (hs : StorageSafe th.storage disk)
    (o : obj) (hack : disk.acknowledged o = true) :
    ∃ r, disk.live r = true ∧ disk.stored r o = true := by
  have hcopy := Durability.invariants_noDataLoss
    (Durability.Theory replica obj writeQuorum readQuorum)
    (DiskState replica obj writeQuorum readQuorum) replica obj writeQuorum readQuorum
    (DiskRep replica obj writeQuorum readQuorum) th.storage disk ha hs
  dsimp [Durability.NoDataLoss, getFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, diskFieldRep, Veil.canonicalFieldRepresentation] at hcopy
  exact hcopy o hack

theorem published_recoverable
    (th : Theory node group name snapshot replica obj writeQuorum readQuorum)
    (ha : Assumptions th)
    {s : State node group name snapshot replica obj writeQuorum readQuorum}
    (hr : Reachable th s) (d : group) (hp : s.registry.published d = true)
    (q : readQuorum) (hq : ∀ r, th.storage.memberR r q = true → s.storage.live r = true) :
    s.storage.live (th.storage.meet (s.storage.witness (th.payload d)) q) = true ∧
      s.storage.stored (th.storage.meet (s.storage.witness (th.payload d)) q) (th.payload d) = true := by
  have hs := reachable_safe th ha hr
  exact acknowledged_recoverable th s.storage ha.2 hs.2.1 _ q (hs.2.2.1 d hp) hq

theorem published_has_copy
    (th : Theory node group name snapshot replica obj writeQuorum readQuorum)
    (ha : Assumptions th)
    {s : State node group name snapshot replica obj writeQuorum readQuorum}
    (hr : Reachable th s) (d : group) (hp : s.registry.published d = true) :
    ∃ r, s.storage.live r = true ∧ s.storage.stored r (th.payload d) = true := by
  have hs := reachable_safe th ha hr
  exact acknowledged_has_copy th s.storage ha.2 hs.2.1 _ (hs.2.2.1 d hp)

theorem checkpoint_manifest_recoverable
    (th : Theory node group name snapshot replica obj writeQuorum readQuorum)
    (ha : Assumptions th)
    {s : State node group name snapshot replica obj writeQuorum readQuorum}
    (hr : Reachable th s) (n : node) (hne : s.registry.head n ≠ th.registry.emptySnapshot)
    (q : readQuorum) (hq : ∀ r, th.storage.memberR r q = true → s.storage.live r = true) :
    s.storage.live (th.storage.meet (s.storage.witness (th.manifest (s.registry.head n))) q) = true ∧
      s.storage.stored (th.storage.meet (s.storage.witness (th.manifest (s.registry.head n))) q)
        (th.manifest (s.registry.head n)) = true := by
  have hs := reachable_safe th ha hr
  exact acknowledged_recoverable th s.storage ha.2 hs.2.1 _ q (hs.2.2.2 n hne) hq

theorem checkpoint_manifest_has_copy
    (th : Theory node group name snapshot replica obj writeQuorum readQuorum)
    (ha : Assumptions th)
    {s : State node group name snapshot replica obj writeQuorum readQuorum}
    (hr : Reachable th s) (n : node) (hne : s.registry.head n ≠ th.registry.emptySnapshot) :
    ∃ r, s.storage.live r = true ∧ s.storage.stored r (th.manifest (s.registry.head n)) = true := by
  have hs := reachable_safe th ha hr
  exact acknowledged_has_copy th s.storage ha.2 hs.2.1 _ (hs.2.2.2 n hne)

theorem checkpoint_declaration_recoverable
    (th : Theory node group name snapshot replica obj writeQuorum readQuorum)
    (ha : Assumptions th)
    {s : State node group name snapshot replica obj writeQuorum readQuorum}
    (hr : Reachable th s) (n : node) (d : group)
    (hd : th.registry.contents (s.registry.head n) d = true)
    (q : readQuorum) (hq : ∀ r, th.storage.memberR r q = true → s.storage.live r = true) :
    s.storage.live (th.storage.meet (s.storage.witness (th.payload d)) q) = true ∧
      s.storage.stored (th.storage.meet (s.storage.witness (th.payload d)) q) (th.payload d) = true := by
  have hs := reachable_safe th ha hr
  exact published_recoverable th ha hr d (hs.1.2.2.2.2.2.1 n d hd) q hq

theorem checkpoint_declaration_has_copy
    (th : Theory node group name snapshot replica obj writeQuorum readQuorum)
    (ha : Assumptions th)
    {s : State node group name snapshot replica obj writeQuorum readQuorum}
    (hr : Reachable th s) (n : node) (d : group)
    (hd : th.registry.contents (s.registry.head n) d = true) :
    ∃ r, s.storage.live r = true ∧ s.storage.stored r (th.payload d) = true := by
  have hs := reachable_safe th ha hr
  exact published_has_copy th ha hr d (hs.1.2.2.2.2.2.1 n d hd)

end Proofs
#print axioms storage_acknowledged_mono
#print axioms registry_preserves_coupling
#print axioms initial_coupled
#print axioms initial_safe
#print axioms next_safe
#print axioms reachable_safe
#print axioms published_recoverable
#print axioms published_has_copy
#print axioms checkpoint_manifest_recoverable
#print axioms checkpoint_manifest_has_copy
#print axioms checkpoint_declaration_recoverable
#print axioms checkpoint_declaration_has_copy
end ParaleanGroupComposition

namespace ParaleanGroups
noncomputable section TemporalBridge

variable {node group name snapshot : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]

attribute [local instance] Classical.propDecidable

abbrev ReceiveStep (th : Theory node group name snapshot)
    (s s' : CanonicalState node group name snapshot) (n : node) (d : group) : Prop :=
  receive.ext.tr (Theory node group name snapshot) (CanonicalState node group name snapshot)
    node group name snapshot (CanonicalRep node group name snapshot) n d th s s'

theorem receive_enabled_iff (th : Theory node group name snapshot)
    (s : CanonicalState node group name snapshot) (n : node) (d : group) :
    (∃ s', ReceiveStep th s s' n d) ↔
      s.alive n = true ∧ s.online n = true ∧ s.published d = true ∧ ¬s.known n d = true := by
  dsimp [ReceiveStep, receive.ext.tr, getFrom, setIn, instIsSubStateOfRefl,
    Veil.FieldRepresentation.get, canonicalFieldRep, Veil.canonicalFieldRepresentation]
  constructor
  · rintro ⟨s', ha, ho, hp, hk, _⟩
    exact ⟨ha, ho, hp, hk⟩
  · rintro ⟨ha, ho, hp, hk⟩
    exact ⟨_, ha, ho, hp, hk, rfl⟩

theorem receive_adds_known (th : Theory node group name snapshot)
    (s s' : CanonicalState node group name snapshot) (n : node) (d : group)
    (h : ReceiveStep th s s' n d) : s'.known n d = true := by
  simp only [ReceiveStep, receive.ext.tr] at h
  dsimp [getFrom, setIn, instIsSubStateOfRefl, Veil.FieldRepresentation.get,
    canonicalFieldRep, Veil.canonicalFieldRepresentation] at h
  rcases h with ⟨_, _, _, _, hs⟩
  subst s'
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

abbrev RegistryStep (th : Theory node group name snapshot)
    (s : CanonicalState node group name snapshot) (l : Label node group name snapshot)
    (s' : CanonicalState node group name snapshot) : Prop :=
  Next (Theory node group name snapshot) (CanonicalState node group name snapshot)
    node group name snapshot (CanonicalRep node group name snapshot) th s l s'

/-- Durable publication survives every generated Registry action. Stable
    states cannot crash or partition, so their knowledge and readiness persist. -/
theorem registry_step_persistent (th : Theory node group name snapshot)
    (s s' : CanonicalState node group name snapshot) (l : Label node group name snapshot)
    (h : RegistryStep th s l s') :
    (∀ d, s.published d = true → s'.published d = true) ∧
    (s.stable = true → s'.stable = true ∧
      (∀ n d, s.known n d = true → s'.known n d = true) ∧
      (∀ n, s.alive n = true → s'.alive n = true) ∧
      (∀ n, s.online n = true → s'.online n = true)) ∧
    ((s.stable = true → ∀ n, s.alive n = true ∧ s.online n = true) →
      s'.stable = true → ∀ n, s'.alive n = true ∧ s'.online n = true) := by
  cases l <;>
    simp only [RegistryStep, Next, NextAct, prepare.ext.derived_eq, publish.ext.derived_eq,
      receive.ext.derived_eq, commit.ext.derived_eq, crash.ext.derived_eq,
      recover.ext.derived_eq, partition.ext.derived_eq, reconnect.ext.derived_eq,
      heal.ext.derived_eq] at h
  all_goals
    dsimp [prepare.ext.tr, publish.ext.tr, receive.ext.tr, commit.ext.tr, crash.ext.tr,
      recover.ext.tr, partition.ext.tr, reconnect.ext.tr, heal.ext.tr,
      getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
      instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
      Veil.canonicalFieldRepresentation] at h
    simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp] at h
    try split_ifs at h
    all_goals
      repeat' rcases h with ⟨ha, h⟩
      try subst s'
      simp_all

#print axioms receive_adds_known
#print axioms registry_step_persistent

abbrev HealStep (th : Theory node group name snapshot)
    (s s' : CanonicalState node group name snapshot) : Prop :=
  heal.ext.tr (Theory node group name snapshot) (CanonicalState node group name snapshot)
    node group name snapshot (CanonicalRep node group name snapshot) th s s'

theorem heal_enabled_iff (th : Theory node group name snapshot)
    (s : CanonicalState node group name snapshot) :
    (∃ s', HealStep th s s') ↔ ¬s.stable = true := by
  dsimp [HealStep, heal.ext.tr, getFrom, setIn, instIsSubStateOfRefl,
    Veil.FieldRepresentation.get, canonicalFieldRep, Veil.canonicalFieldRepresentation]
  constructor
  · rintro ⟨s', hs, _⟩
    exact hs
  · intro hs
    exact ⟨_, hs, rfl⟩

theorem heal_sets_stable (th : Theory node group name snapshot)
    (s s' : CanonicalState node group name snapshot) (h : HealStep th s s') :
    s'.stable = true := by
  dsimp [HealStep, heal.ext.tr, getFrom, setIn, instIsSubStateOfRefl,
    Veil.FieldRepresentation.get, canonicalFieldRep, Veil.canonicalFieldRepresentation] at h
  rcases h with ⟨_, hs⟩
  subst s'
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

theorem reachable_ready (th : Theory node group name snapshot)
    {s : CanonicalState node group name snapshot} (hr : Reachable th s) :
    s.stable = true → ∀ n, s.alive n = true ∧ s.online n = true := by
  induction hr with
  | initial hi =>
    dsimp [GroupsInit, Init, initializer.ext.tr, getFrom, setIn, instIsSubStateOfRefl] at hi
    cases hi
    simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp]
  | step hr ht ih => exact (registry_step_persistent th _ _ _ ht).2.2 ih
  | stutter hr ih => exact ih

structure Trace (th : Theory node group name snapshot) where
  state : Nat → CanonicalState node group name snapshot
  initial : Reachable th (state 0)
  next : ∀ t, state (t + 1) = state t ∨ ∃ l, RegistryStep th (state t) l (state (t + 1))

variable {th : Theory node group name snapshot}

theorem Trace.reachable (tr : Trace th) (t : Nat) : Reachable th (tr.state t) := by
  induction t with
  | zero => exact tr.initial
  | succ t ih =>
    rcases tr.next t with he | ⟨l, hn⟩
    · exact he.symm ▸ ih
    · exact Reachable.step ih hn

def Trace.ReceiveFair (tr : Trace th) : Prop :=
  ∀ n d cutoff,
    (∀ t, cutoff ≤ t → (tr.state t).alive n = true ∧ (tr.state t).online n = true ∧
      (tr.state t).published d = true ∧ ¬(tr.state t).known n d = true) →
    ∃ t, cutoff ≤ t ∧ ReceiveStep th (tr.state t) (tr.state (t + 1)) n d

def Trace.HealFair (tr : Trace th) : Prop :=
  ∀ cutoff, (∀ t, cutoff ≤ t → ¬(tr.state t).stable = true) →
    ∃ t, cutoff ≤ t ∧ HealStep th (tr.state t) (tr.state (t + 1))

theorem Trace.eventually_stable (tr : Trace th) (fair : tr.HealFair) :
    ∃ cutoff, (tr.state cutoff).stable = true := by
  classical
  by_contra absent
  obtain ⟨t, _, ht⟩ := fair 0 (fun t _ hs => absent ⟨t, hs⟩)
  exact absent ⟨t + 1, heal_sets_stable th _ _ ht⟩

theorem Trace.stable_after (tr : Trace th) {a b : Nat} (hab : a ≤ b)
    (hs : (tr.state a).stable = true) : (tr.state b).stable = true := by
  induction hab with
  | refl => exact hs
  | @step t ht ih =>
    rcases tr.next t with he | ⟨l, hn⟩
    · simpa only [he] using ih
    · exact ((registry_step_persistent th _ _ l hn).2.1 ih).1

/-- Every trace law is discharged using generated Registry transitions and
    the proved safety invariant. The only temporal premises are action fairness. -/
def Trace.deliveryTrace (tr : Trace th) (ha : TheoryAssumptions th)
    (cutoff : Nat) (stable : (tr.state cutoff).stable = true) :
    ParaleanConvergence.DeliveryTrace node group where
  published t d := (tr.state t).published d = true
  known t n d := (tr.state t).known n d = true
  ready t n := (tr.state t).alive n = true ∧ (tr.state t).online n = true
  receive t n d := ReceiveStep th (tr.state t) (tr.state (t + 1)) n d
  published_step := by
    intro t d hp
    rcases tr.next t with he | ⟨l, hn⟩
    · simpa only [he] using hp
    · exact (registry_step_persistent th _ _ l hn).1 d hp
  recovery := cutoff
  ready_after := by
    intro t ht n
    exact reachable_ready th (tr.reachable t) (tr.stable_after ht stable) n
  known_step := by
    intro t ht n d hk
    rcases tr.next t with he | ⟨l, hn⟩
    · simpa only [he] using hk
    · exact ((registry_step_persistent th _ _ l hn).2.1 (tr.stable_after ht stable)).2.1 n d hk
  receive_adds := by
    intro t n d hr
    exact receive_adds_known th _ _ n d hr
  known_published := by
    intro t n d hk
    exact (reachable_safe th ha (tr.reachable t)).2.2.1 n d hk

theorem Trace.deliveryTrace_fair (tr : Trace th) (ha : TheoryAssumptions th)
    (cutoff : Nat) (stable : (tr.state cutoff).stable = true) (fair : tr.ReceiveFair) :
    (tr.deliveryTrace ha cutoff stable).WeakFair := by
  intro n d t₀ enabled
  exact fair n d t₀ (fun t ht => ⟨(enabled t ht).1.1, (enabled t ht).1.2,
    (enabled t ht).2.1, (enabled t ht).2.2⟩)

theorem Trace.eventual_delivery (tr : Trace th) (ha : TheoryAssumptions th)
    (hf : tr.HealFair) (rf : tr.ReceiveFair) (n : node) (d : group)
    (t₀ : Nat) (hp : (tr.state t₀).published d = true) :
    ParaleanConvergence.EventuallyAlways (fun t => (tr.state t).known n d = true) := by
  obtain ⟨cutoff, hs⟩ := tr.eventually_stable hf
  exact ParaleanConvergence.eventual_delivery (tr.deliveryTrace ha cutoff hs)
    (tr.deliveryTrace_fair ha cutoff hs rf) n d t₀ hp

theorem Trace.convergence (tr : Trace th) (ha : TheoryAssumptions th)
    (hf : tr.HealFair) (rf : tr.ReceiveFair)
    (nodes : List node) (decls : List group)
    (allNodes : ∀ n, n ∈ nodes) (allDecls : ∀ d, d ∈ decls) :
    ParaleanConvergence.EventuallyAlways (fun t => ∀ n d,
      (tr.state t).known n d = true ↔ (tr.state t).published d = true) := by
  obtain ⟨cutoff, hs⟩ := tr.eventually_stable hf
  exact ParaleanConvergence.convergence (tr.deliveryTrace ha cutoff hs)
    (tr.deliveryTrace_fair ha cutoff hs rf) nodes decls allNodes allDecls

theorem Trace.index_convergence (tr : Trace th) (ha : TheoryAssumptions th)
    (hf : tr.HealFair) (rf : tr.ReceiveFair)
    (nodes : List node) (decls : List group)
    (allNodes : ∀ n, n ∈ nodes) (allDecls : ∀ d, d ∈ decls) :
    ParaleanConvergence.EventuallyAlways (fun t => ∀ n,
      (tr.state t).known n = (tr.state t).published) := by
  obtain ⟨cutoff, hc⟩ := tr.convergence ha hf rf nodes decls allNodes allDecls
  refine ⟨cutoff, ?_⟩
  intro t ht n
  funext d
  have h := hc t ht n d
  cases hk : (tr.state t).known n d <;>
    cases hp : (tr.state t).published d <;> simp_all

end TemporalBridge
#print axioms registry_step_persistent
#print axioms reachable_ready
#print axioms Trace.eventual_delivery
#print axioms Trace.convergence
#print axioms Trace.index_convergence
end ParaleanGroups

namespace ParaleanGroupComposition
noncomputable section EndToEnd

variable {node group name snapshot replica obj writeQuorum readQuorum : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]
  [DecidableEq replica] [Inhabited replica] [DecidableEq obj] [Inhabited obj]
  [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum]

variable {th : Theory node group name snapshot replica obj writeQuorum readQuorum}

theorem next_registry_projection
    {s s' : State node group name snapshot replica obj writeQuorum readQuorum}
    (hn : Next th s s') :
    s'.registry = s.registry ∨ ∃ label,
      ParaleanGroups.RegistryStep th.registry s.registry label s'.registry := by
  cases hn with
  | registry label ht hg => exact Or.inr ⟨label, ht⟩
  | storage label ht => exact Or.inl rfl
  | stutter => exact Or.inl rfl

theorem reachable_registry_projection
    {s : State node group name snapshot replica obj writeQuorum readQuorum}
    (hr : Reachable th s) : ParaleanGroups.Reachable th.registry s.registry := by
  induction hr with
  | initial hi => exact ParaleanGroups.Reachable.initial hi.1
  | step hr hn ih =>
    rcases next_registry_projection hn with he | ⟨label, ht⟩
    · exact he.symm ▸ ih
    · exact ParaleanGroups.Reachable.step ih ht

theorem reachable_ancestor_safe
    (ha : Assumptions th)
    {s : State node group name snapshot replica obj writeQuorum readQuorum}
    (hr : Reachable th s) : ParaleanGroups.AncestorSafe th.registry s.registry :=
  ParaleanGroups.reachable_ancestor_safe th.registry ha.1 (reachable_registry_projection hr)

theorem published_ancestors_closed
    (ha : Assumptions th)
    {s : State node group name snapshot replica obj writeQuorum readQuorum}
    (hr : Reachable th s) (d e : group)
    (hp : s.registry.published d = true) (he : th.registry.ancestors d e = true) :
    s.registry.published e = true :=
  (reachable_ancestor_safe ha hr).1 d e hp he

theorem pending_ancestors_closed
    (ha : Assumptions th)
    {s : State node group name snapshot replica obj writeQuorum readQuorum}
    (hr : Reachable th s) (n : node) (d e : group)
    (hp : s.registry.pending n d = true) (he : th.registry.ancestors d e = true) :
    s.registry.published e = true :=
  (reachable_ancestor_safe ha hr).2.1 n d hp e he

theorem reachable_ancestor_acyclic
    (ha : Assumptions th)
    {s : State node group name snapshot replica obj writeQuorum readQuorum}
    (hr : Reachable th s) (T : group → Prop)
    (hsub : ∀ d, T d → s.registry.published d = true) (hne : ∃ d, T d) :
    ∃ d, T d ∧ ∀ e, T e → th.registry.ancestors d e ≠ true :=
  ParaleanGroups.ancestor_acyclic th.registry s.registry (reachable_ancestor_safe ha hr) T hsub hne

theorem published_ancestor_has_copy
    (ha : Assumptions th)
    {s : State node group name snapshot replica obj writeQuorum readQuorum}
    (hr : Reachable th s) (d e : group)
    (hp : s.registry.published d = true) (he : th.registry.ancestors d e = true) :
    ∃ r, s.storage.live r = true ∧ s.storage.stored r (th.payload e) = true :=
  published_has_copy th ha hr e (published_ancestors_closed ha hr d e hp he)

/-- Storage transitions and guarded Registry transitions share one timeline.
    Composition.Next already includes stuttering. -/
structure Trace (th : Theory node group name snapshot replica obj writeQuorum readQuorum) where
  state : Nat → State node group name snapshot replica obj writeQuorum readQuorum
  initial : Reachable th (state 0)
  next : ∀ t, Next th (state t) (state (t + 1))

theorem Trace.reachable (tr : Trace th) (t : Nat) : Reachable th (tr.state t) := by
  induction t with
  | zero => exact tr.initial
  | succ t ih => exact Reachable.step ih (tr.next t)

def Trace.toRegistryTrace (tr : Trace th) : ParaleanGroups.Trace th.registry where
  state t := (tr.state t).registry
  initial := reachable_registry_projection tr.initial
  next t := next_registry_projection (tr.next t)

/-- Fairness of Registry Heal along the composed timeline. -/
abbrev Trace.HealFair (tr : Trace th) : Prop := tr.toRegistryTrace.HealFair

/-- Fairness of generated Registry Receive along the composed timeline.
    Storage work may interleave, but cannot starve an enabled receive forever. -/
abbrev Trace.ReceiveFair (tr : Trace th) : Prop := tr.toRegistryTrace.ReceiveFair

theorem Trace.eventual_delivery (tr : Trace th) (ha : Assumptions th)
    (hf : tr.HealFair) (rf : tr.ReceiveFair) (n : node) (d : group)
    (t₀ : Nat) (hp : (tr.state t₀).registry.published d = true) :
    ParaleanConvergence.EventuallyAlways (fun t => (tr.state t).registry.known n d = true) := by
  exact tr.toRegistryTrace.eventual_delivery ha.1 hf rf n d t₀ hp

theorem Trace.index_convergence (tr : Trace th) (ha : Assumptions th)
    (hf : tr.HealFair) (rf : tr.ReceiveFair)
    (nodes : List node) (decls : List group)
    (allNodes : ∀ n, n ∈ nodes) (allDecls : ∀ d, d ∈ decls) :
    ParaleanConvergence.EventuallyAlways (fun t => ∀ n,
      (tr.state t).registry.known n = (tr.state t).registry.published) := by
  exact tr.toRegistryTrace.index_convergence ha.1 hf rf nodes decls allNodes allDecls

end EndToEnd
#print axioms reachable_registry_projection
#print axioms published_ancestor_has_copy
#print axioms Trace.eventual_delivery
#print axioms Trace.index_convergence
end ParaleanGroupComposition

namespace ParaleanGroupComposition

noncomputable section CommitProofs
variable {node group name snapshot replica obj writeQuorum readQuorum : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]
  [DecidableEq replica] [Inhabited replica] [DecidableEq obj] [Inhabited obj]
  [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum]

/-- A successful guarded commit carries its generated action label.
`Next` erases labels, so a state pair alone cannot distinguish a same-head
commit from a stutter. No head-change test is imposed here. -/
inductive CommitStep (th : Theory node group name snapshot replica obj writeQuorum readQuorum)
    (n : node) (S : snapshot) :
    State node group name snapshot replica obj writeQuorum readQuorum →
    State node group name snapshot replica obj writeQuorum readQuorum → Prop where
  | registry {rg rg' disk} :
      ParaleanGroups.GroupsNext th.registry rg (.commit n S) rg' →
      Guard th disk (.commit n S) → CommitStep th n S ⟨rg, disk⟩ ⟨rg', disk⟩

theorem CommitStep.to_next
    (th : Theory node group name snapshot replica obj writeQuorum readQuorum)
    (n : node) (S : snapshot)
    (s s' : State node group name snapshot replica obj writeQuorum readQuorum)
    (ht : CommitStep th n S s s') : Next th s s' := by
  cases ht with
  | registry hr hg => exact Next.registry (.commit n S) hr hg

theorem commit_fresh
    (th : Theory node group name snapshot replica obj writeQuorum readQuorum)
    (n : node) (S : snapshot)
    (s s' : State node group name snapshot replica obj writeQuorum readQuorum)
    (ht : CommitStep th n S s s') :
    ParaleanGroups.current n S th.registry s.registry ∧
      s'.registry.head n = S ∧ s.storage.acknowledged (th.manifest S) = true := by
  cases ht with
  | registry hr hg =>
    have hf := ParaleanGroups.commit_fresh th.registry _ _ n S hr
    exact ⟨hf.1, hf.2, hg⟩

end CommitProofs
#print axioms CommitStep.to_next
#print axioms commit_fresh
end ParaleanGroupComposition

namespace ParaleanGroups
noncomputable section Paths
variable {node group name snapshot : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]

inductive DependencyPath (th : Theory node group name snapshot) : group → group → Prop where
  | edge {g h} : th.deps g h = true → DependencyPath th g h
  | trans {g h k} : DependencyPath th g h → DependencyPath th h k → DependencyPath th g k

theorem dependency_path_snapshot_closed
    (th : Theory node group name snapshot) (st : CanonicalState node group name snapshot)
    (S : snapshot) (hb : buildable S th st) {g h : group}
    (hg : th.contents S g = true) (hp : DependencyPath th g h) : th.contents S h = true := by
  induction hp with
  | edge he => exact hb.2.1 _ _ hg he
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ hg)

theorem dependency_path_conflict_blocks_commit
    (th : Theory node group name snapshot) (st st' : CanonicalState node group name snapshot)
    (n : node) (S : snapshot) (g h a b : group) (x : name)
    (hg : th.contents S g = true) (hh : th.contents S h = true)
    (hga : DependencyPath th g a) (hhb : DependencyPath th h b)
    (hax : th.member a x = true) (hbx : th.member b x = true) (hne : a ≠ b) :
    ¬GroupsNext th st (.commit n S) st' := by
  intro ht
  have hb := ((commit_enabled_iff th st n S).1 ⟨st', ht⟩).2.2.2.1
  exact hne (hb.2.2.1 a b x
    (dependency_path_snapshot_closed th st S hb hg hga)
    (dependency_path_snapshot_closed th st S hb hh hhb) hax hbx)

theorem next_preserves_historical_snapshot
    (th : Theory node group name snapshot) (ha : TheoryAssumptions th)
    {st : CanonicalState node group name snapshot} (hr : Reachable th st)
    (st' : CanonicalState node group name snapshot) (label : Label node group name snapshot)
    (ht : GroupsNext th st label st') (n : node) :
    buildable (st.head n) th st' ∧
      ∀ g, th.contents (st.head n) g = true → st'.published g = true := by
  have hs := snapshot_safe th ha hr n
  exact ⟨hs.1, fun g hg => (registry_step_persistent th st st' label ht).1 g (hs.2 g hg)⟩

end Paths
#print axioms dependency_path_snapshot_closed
#print axioms dependency_path_conflict_blocks_commit
#print axioms next_preserves_historical_snapshot
end ParaleanGroups

namespace ParaleanGroups
noncomputable section NameConvergence
variable {node group name snapshot : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]
variable {th : Theory node group name snapshot}

theorem Trace.eventual_two_heads (tr : Trace th) (ha : TheoryAssumptions th)
    (hf : tr.HealFair) (rf : tr.ReceiveFair)
    (nodes : List node) (allNodes : ∀ n, n ∈ nodes)
    (a b : group) (x : name) (hax : th.member a x = true) (hbx : th.member b x = true)
    (t₀ : Nat) (pa : (tr.state t₀).published a = true) (pb : (tr.state t₀).published b = true)
    (unsuperseded : ∀ t e, (tr.state t).published e = true →
      th.revisions e a x ≠ true ∧ th.revisions e b x ≠ true) :
    ParaleanConvergence.EventuallyAlways (fun t => ∀ n,
      isHead n a x th (tr.state t) ∧ isHead n b x th (tr.state t)) := by
  have each : ∀ n ∈ nodes, ParaleanConvergence.EventuallyAlways
      (fun t => (tr.state t).known n a = true ∧ (tr.state t).known n b = true) := by
    intro n _
    obtain ⟨u, hu⟩ := tr.eventual_delivery ha hf rf n a t₀ pa
    obtain ⟨v, hv⟩ := tr.eventual_delivery ha hf rf n b t₀ pb
    exact ⟨max u v, fun t ht => ⟨hu t (Nat.le_trans (Nat.le_max_left _ _) ht),
      hv t (Nat.le_trans (Nat.le_max_right _ _) ht)⟩⟩
  obtain ⟨cutoff, hc⟩ := ParaleanConvergence.finite_eventuallyAlways nodes _ each
  refine ⟨cutoff, ?_⟩
  intro t ht n
  obtain ⟨hka, hkb⟩ := hc t ht n (allNodes n)
  refine ⟨⟨hka, hax, ?_⟩, ⟨hkb, hbx, ?_⟩⟩
  · rintro ⟨e, he, hea⟩
    exact (unsuperseded t e (known_published th ha (tr.reachable t) n e he)).1 hea
  · rintro ⟨e, he, heb⟩
    exact (unsuperseded t e (known_published th ha (tr.reachable t) n e he)).2 heb

end NameConvergence
#print axioms Trace.eventual_two_heads
end ParaleanGroups

namespace ParaleanGroupComposition
noncomputable section AdditionalCaps
variable {node group name snapshot replica obj writeQuorum readQuorum : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]
  [DecidableEq replica] [Inhabited replica] [DecidableEq obj] [Inhabited obj]
  [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum]
variable {th : Theory node group name snapshot replica obj writeQuorum readQuorum}

theorem guarded_commit_enabled_iff
    (s : State node group name snapshot replica obj writeQuorum readQuorum) (n : node) (S : snapshot) :
    (∃ s', CommitStep th n S s s') ↔
      s.registry.alive n = true ∧ s.registry.online n = true ∧
      (∀ g, th.registry.contents S g = true → s.registry.known n g = true) ∧
      ParaleanGroups.buildable S th.registry s.registry ∧
      ParaleanGroups.current n S th.registry s.registry ∧ s.storage.acknowledged (th.manifest S) = true := by
  constructor
  · rintro ⟨s', ht⟩
    cases ht with
    | registry hr hg =>
      have h := (ParaleanGroups.commit_enabled_iff th.registry _ n S).1 ⟨_, hr⟩
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, hg⟩
  · rintro ⟨hal, hon, hk, hb, hc, hack⟩
    obtain ⟨rg', ht⟩ := (ParaleanGroups.commit_enabled_iff th.registry s.registry n S).2
      ⟨hal, hon, hk, hb, hc⟩
    exact ⟨⟨rg', s.storage⟩, CommitStep.registry ht hack⟩

theorem Trace.eventual_two_heads (tr : Trace th) (ha : Assumptions th)
    (hf : tr.HealFair) (rf : tr.ReceiveFair)
    (nodes : List node) (allNodes : ∀ n, n ∈ nodes)
    (a b : group) (x : name) (hax : th.registry.member a x = true) (hbx : th.registry.member b x = true)
    (t₀ : Nat) (pa : (tr.state t₀).registry.published a = true) (pb : (tr.state t₀).registry.published b = true)
    (unsuperseded : ∀ t e, (tr.state t).registry.published e = true →
      th.registry.revisions e a x ≠ true ∧ th.registry.revisions e b x ≠ true) :
    ParaleanConvergence.EventuallyAlways (fun t => ∀ n,
      ParaleanGroups.isHead n a x th.registry (tr.state t).registry ∧
      ParaleanGroups.isHead n b x th.registry (tr.state t).registry) :=
  tr.toRegistryTrace.eventual_two_heads ha.1 hf rf nodes allNodes a b x hax hbx t₀ pa pb unsuperseded

theorem snapshot_no_duplicate_name (ha : Assumptions th)
    {s : State node group name snapshot replica obj writeQuorum readQuorum} (hr : Reachable th s)
    (n : node) (g h : group) (x : name)
    (hg : ParaleanGroups.SnapshotBinding th.registry (s.registry.head n) g x)
    (hh : ParaleanGroups.SnapshotBinding th.registry (s.registry.head n) h x) : g = h :=
  ParaleanGroups.snapshot_no_duplicate_name th.registry ha.1 (reachable_registry_projection hr) n g h x hg hh

end AdditionalCaps
#print axioms guarded_commit_enabled_iff
#print axioms Trace.eventual_two_heads
#print axioms snapshot_no_duplicate_name
end ParaleanGroupComposition

namespace ParaleanGroups
noncomputable section Conflict
variable {node group name snapshot : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]
variable {th : Theory node group name snapshot}

theorem Trace.eventual_name_collision (tr : Trace th) (ha : TheoryAssumptions th)
    (hf : tr.HealFair) (rf : tr.ReceiveFair)
    (nodes : List node) (allNodes : ∀ n, n ∈ nodes)
    (a b : group) (x : name) (hne : a ≠ b)
    (hax : th.member a x = true) (hbx : th.member b x = true)
    (t₀ : Nat) (pa : (tr.state t₀).published a = true) (pb : (tr.state t₀).published b = true)
    (unsuperseded : ∀ t e, (tr.state t).published e = true →
      th.revisions e a x ≠ true ∧ th.revisions e b x ≠ true) :
    ParaleanConvergence.EventuallyAlways (fun t => ∀ n S g,
      th.contents S g = true → th.member g x = true →
      ¬∃ st', GroupsNext th (tr.state t) (.commit n S) st') := by
  obtain ⟨c, hc⟩ := tr.eventual_two_heads ha hf rf nodes allNodes a b x hax hbx t₀ pa pb unsuperseded
  refine ⟨c, ?_⟩
  intro t ht n S g hg hx hex
  obtain ⟨st', hstep⟩ := hex
  exact overlapping_heads_block_commit th (tr.state t) st' n S a b g x
    (hc t ht n).1 (hc t ht n).2 hne hg hx hstep

end Conflict
#print axioms Trace.eventual_name_collision
end ParaleanGroups

namespace ParaleanGroupComposition
noncomputable section Conflict
variable {node group name snapshot replica obj writeQuorum readQuorum : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]
  [DecidableEq replica] [Inhabited replica] [DecidableEq obj] [Inhabited obj]
  [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum]
variable {th : Theory node group name snapshot replica obj writeQuorum readQuorum}

theorem CommitStep.registry_transition
    (s s' : State node group name snapshot replica obj writeQuorum readQuorum)
    (n : node) (S : snapshot) (ht : CommitStep th n S s s') :
    ParaleanGroups.GroupsNext th.registry s.registry (.commit n S) s'.registry := by
  cases ht with
  | registry hr _ => exact hr

theorem Trace.eventual_name_collision (tr : Trace th) (ha : Assumptions th)
    (hf : tr.HealFair) (rf : tr.ReceiveFair)
    (nodes : List node) (allNodes : ∀ n, n ∈ nodes)
    (a b : group) (x : name) (hne : a ≠ b)
    (hax : th.registry.member a x = true) (hbx : th.registry.member b x = true)
    (t₀ : Nat) (pa : (tr.state t₀).registry.published a = true) (pb : (tr.state t₀).registry.published b = true)
    (unsuperseded : ∀ t e, (tr.state t).registry.published e = true →
      th.registry.revisions e a x ≠ true ∧ th.registry.revisions e b x ≠ true) :
    ParaleanConvergence.EventuallyAlways (fun t => ∀ n S g,
      th.registry.contents S g = true → th.registry.member g x = true →
      ¬∃ s', CommitStep th n S (tr.state t) s') := by
  obtain ⟨c, hc⟩ := tr.toRegistryTrace.eventual_name_collision ha.1 hf rf nodes allNodes
    a b x hne hax hbx t₀ pa pb unsuperseded
  refine ⟨c, ?_⟩
  intro t ht n S g hg hx hex
  obtain ⟨s', hstep⟩ := hex
  exact hc t ht n S g hg hx ⟨s'.registry,
    CommitStep.registry_transition (tr.state t) s' n S hstep⟩

end Conflict
#print axioms Trace.eventual_name_collision
end ParaleanGroupComposition
