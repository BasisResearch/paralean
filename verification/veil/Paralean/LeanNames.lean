import Paralean.Groups

/-! Lean-level naming layer under `ParaleanGroups.member`.

A command (not an `addDecl` call) is the capture unit. A trusted classifier
sorts every Lean output of a command into one of three classes.

* Public: every name a user can write in source. This covers explicitly
  declared names, auto-named instances (`instFooNat`, named canonically from the
  instance type, without environment-dependent `_n` deduplication) and the eager
  auxiliaries of inductive and structure commands (`T.below`, `T.brecOn`,
  `T.casesOn`, `T.recOn`, `T.noConfusion`, `T.c.injEq`, `T.ctorIdx`, projections,
  constructors, `SizeOf` instances). Only public names reach the model's `name`
  type and enter collision checks.
* Scoped: `_private.*` names and compiler auxiliaries (`proof_n`, `match_n`,
  `_aux*`, `_unsafe_rec`). Their identity is keyed by the producing group; the
  workspace renderer and the exporter both emit the group-keyed `Rendered` form.
* Reserved: lazily realised names (`eq_n`, `eq_def`, `unfold`, `induct`,
  `fun_cases`, match and congruence equations). Never published; each consumer
  and the validator realise them from the pinned base group. -/

set_option linter.unusedSectionVars false

namespace ParaleanLeanNames

/-- Lean names as seen by capture, after classification. `mod` = module paths,
`atom` = name strings, `sfx` = reserved suffixes (`eq_1`, `eq_def`, `induct`, ...). -/
inductive LeanName (mod atom sfx : Type) where
  /-- Public name: explicit declarations, canonical instance names
  (`instFooNat`) and eager auxiliaries (`T.casesOn`, `T.mk`, ...). -/
  | pub (b : atom)
  /-- Compiler auxiliary (`foo.proof_1`, `foo.match_1`, `_aux_...`, `_unsafe_rec`). -/
  | gen (b : atom)
  /-- Private name `_private.<m>.0.b`. -/
  | priv (m : mod) (b : atom)
  /-- Reserved name `base.s`, created by a consumer's `realizeConst`. -/
  | res (base : LeanName mod atom sfx) (s : sfx)
  deriving DecidableEq

/-- Classification of a Lean name. -/
inductive Kind (leanName : Type) where
  | pub
  | reserved (base : leanName)
  | scoped
  deriving DecidableEq

def Kind.map {α β : Type} (f : α → β) : Kind α → Kind β
  | .pub => .pub
  | .reserved b => .reserved (f b)
  | .scoped => .scoped

/-- The Lean name the workspace renderer and the exporter emit for a name
produced by a group. Scoped names carry the producing group; the module path of
a private name is dropped. The implementation spells these as Lean names (for
example `_private.<groupId>.0.b`); that spelling must be injective and must not
coincide with any public spelling. -/
inductive Rendered (group atom sfx : Type) where
  | pub (b : atom)
  | gen (g : group) (b : atom)
  | priv (g : group) (b : atom)
  | res (base : Rendered group atom sfx) (s : sfx)
  deriving DecidableEq

section Naming
variable {mod atom sfx group name command : Type}

def kind : LeanName mod atom sfx → Kind (LeanName mod atom sfx)
  | .pub _ => .pub
  | .gen _ => .scoped
  | .priv _ _ => .scoped
  | .res y _ => .reserved y

/-- Rendering of `y` when produced by group `g`. -/
def render (g : group) : LeanName mod atom sfx → Rendered group atom sfx
  | .pub b => .pub b
  | .gen b => .gen g b
  | .priv _ b => .priv g b
  | .res y s => .res (render g y) s

/-- Exporter relocation of declarations between module paths. -/
def relocate (f : mod → mod) : LeanName mod atom sfx → LeanName mod atom sfx
  | .pub b => .pub b
  | .gen b => .gen b
  | .priv m b => .priv (f m) b
  | .res y s => .res (relocate f y) s

/-- Canonical model name. Only public names are collision-checked. -/
def canon (enc : atom → name) : LeanName mod atom sfx → Option name
  | .pub b => some (enc b)
  | _ => none

theorem canon_some_iff (enc : atom → name) (y : LeanName mod atom sfx) (x : name) :
    canon enc y = some x ↔ ∃ b, y = .pub b ∧ enc b = x := by
  cases y <;> simp [canon]

theorem canon_none_of_scoped (enc : atom → name) {y : LeanName mod atom sfx}
    (hy : kind y = .scoped) : canon enc y = none := by
  cases y <;> simp_all [kind, canon]

theorem canon_none_of_reserved (enc : atom → name) {y b : LeanName mod atom sfx}
    (hy : kind y = .reserved b) : canon enc y = none := by
  cases y <;> simp_all [kind, canon]

/-- Public names map injectively. -/
theorem canon_injective_public (enc : atom → name) (hinj : Function.Injective enc)
    {y y' : LeanName mod atom sfx} {x : name}
    (hy : canon enc y = some x) (hy' : canon enc y' = some x) : y = y' := by
  rcases (canon_some_iff enc y x).1 hy with ⟨b, rfl, hb⟩
  rcases (canon_some_iff enc y' x).1 hy' with ⟨b', rfl, hb'⟩
  rw [hinj (hb.trans hb'.symm)]

/-- Scoped names render to group-unique names that never equal a public name.
Structural: it holds because `Rendered` keeps the group and the class in
separate constructors; the implementation's spelling must preserve this. -/
theorem scoped_render_distinct {g h : group} (hne : g ≠ h)
    {y y' : LeanName mod atom sfx} (hy : kind y = .scoped) :
    (kind y' = .scoped → render g y ≠ render h y') ∧
    (∀ (k : group) b, render g y ≠ render k (.pub b : LeanName mod atom sfx)) := by
  refine ⟨fun hy' => ?_, fun k b => ?_⟩
  · cases y <;> cases y' <;> simp_all [kind, render]
  · cases y <;> simp_all [kind, render]

/-- Working-copy clash: in one rendered file, unreserved outputs of two distinct
groups get the same Lean name (Lean's "already declared" error) exactly when
they are the same public name. -/
theorem render_clash_iff {g h : group} (hne : g ≠ h) {y y' : LeanName mod atom sfx}
    (hy : ∀ b s, y ≠ .res b s) (hy' : ∀ b s, y' ≠ .res b s) :
    render g y = render h y' ↔ ∃ b, y = .pub b ∧ y' = .pub b := by
  cases y with
  | res b s => exact absurd rfl (hy b s)
  | pub b =>
    cases y' with
    | res b' s' => exact absurd rfl (hy' b' s')
    | _ => simp [render, eq_comm]
  | gen b =>
    cases y' with
    | res b' s' => exact absurd rfl (hy' b' s')
    | _ => simp [render, hne]
  | priv m b =>
    cases y' with
    | res b' s' => exact absurd rfl (hy' b' s')
    | _ => simp [render, hne]

theorem kind_relocate (f : mod → mod) (y : LeanName mod atom sfx) :
    kind (relocate f y) = (kind y).map (relocate f) := by
  cases y <;> rfl

theorem render_relocate (f : mod → mod) (g : group) (y : LeanName mod atom sfx) :
    render g (relocate f y) = render g y := by
  induction y with
  | pub b => rfl
  | gen b => rfl
  | priv m b => rfl
  | res y s ih => simp [relocate, render, ih]

theorem canon_relocate (f : mod → mod) (enc : atom → name) (y : LeanName mod atom sfx) :
    canon enc (relocate f y) = canon enc y := by
  cases y <;> rfl

/-- Command-granularity capture: every `addDecl` output of a command `c` is in
`produces c`, and the whole command is one group `capture c`. -/
structure Capture (command group mod atom sfx : Type) where
  capture : command → group
  produces : command → LeanName mod atom sfx → Prop

variable (C : Capture command group mod atom sfx) (enc : atom → name)

/-- Raw Lean-level ownership. -/
def binds (g : group) (y : LeanName mod atom sfx) : Prop :=
  ∃ c, C.capture c = g ∧ C.produces c y

/-- The model's membership, refined through `canon`. -/
def member (g : group) (x : name) : Prop :=
  ∃ c y, C.capture c = g ∧ C.produces c y ∧ canon enc y = some x

/-- Two distinct groups claim one canonical name. -/
def Conflict (g h : group) (x : name) : Prop :=
  g ≠ h ∧ member C enc g x ∧ member C enc h x

theorem member_iff_public (g : group) (x : name) :
    member C enc g x ↔ ∃ b, enc b = x ∧ binds C g (.pub b) := by
  constructor
  · rintro ⟨c, y, hc, hp, hy⟩
    rcases (canon_some_iff enc y x).1 hy with ⟨b, rfl, hb⟩
    exact ⟨b, hb, c, hc, hp⟩
  · rintro ⟨b, hb, c, hc, hp⟩
    exact ⟨c, .pub b, hc, hp, by simp [canon, hb]⟩

/-- No split auxiliaries: all outputs of one command are bound by the single
group `capture c`, and every public output is a member of that group. -/
theorem aux_same_group (c : command) (y y' : LeanName mod atom sfx)
    (hy : C.produces c y) (hy' : C.produces c y') :
    binds C (C.capture c) y ∧ binds C (C.capture c) y' ∧
      (∀ x, canon enc y = some x → member C enc (C.capture c) x) ∧
      (∀ x, canon enc y' = some x → member C enc (C.capture c) x) :=
  ⟨⟨c, rfl, hy⟩, ⟨c, rfl, hy'⟩, fun _ hx => ⟨c, y, rfl, hy, hx⟩,
    fun _ hx => ⟨c, y', rfl, hy', hx⟩⟩

/-- Relocated capture: the exporter moves declarations between modules. -/
def Capture.relocated (f : mod → mod) : Capture command group mod atom sfx where
  capture := C.capture
  produces c y := ∃ y₀, C.produces c y₀ ∧ y = relocate f y₀

/-- Relocation changes neither renderings, canonical names, nor membership. -/
theorem relocation_invariant (f : mod → mod) :
    (∀ (g : group) (y : LeanName mod atom sfx), render g (relocate f y) = render g y) ∧
    (∀ y : LeanName mod atom sfx, canon enc (relocate f y) = canon enc y) ∧
    (∀ g x, member (C.relocated f) enc g x ↔ member C enc g x) := by
  refine ⟨render_relocate f, canon_relocate f enc, ?_⟩
  intro g x
  constructor
  · rintro ⟨c, y, hc, ⟨y₀, hp, rfl⟩, hx⟩
    exact ⟨c, y₀, hc, hp, (canon_relocate f enc y₀) ▸ hx⟩
  · rintro ⟨c, y, hc, hp, hx⟩
    exact ⟨c, relocate f y, hc, ⟨y, hp, rfl⟩, (canon_relocate f enc y).symm ▸ hx⟩

/-- Two groups conflict exactly when they produce the same public Lean name. -/
theorem public_collision_iff (hinj : Function.Injective enc) (g h : group) (x : name) :
    Conflict C enc g h x ↔
      g ≠ h ∧ ∃ b, enc b = x ∧ binds C g (.pub b) ∧ binds C h (.pub b) := by
  constructor
  · rintro ⟨hne, hg, hh⟩
    rcases (member_iff_public C enc g x).1 hg with ⟨b, hb, hgb⟩
    rcases (member_iff_public C enc h x).1 hh with ⟨b', hb', hhb⟩
    have : b' = b := hinj (hb'.trans hb.symm)
    subst this
    exact ⟨hne, b', hb, hgb, hhb⟩
  · rintro ⟨hne, b, hb, hgb, hhb⟩
    exact ⟨hne, (member_iff_public C enc g x).2 ⟨b, hb, hgb⟩,
      (member_iff_public C enc h x).2 ⟨b, hb, hhb⟩⟩

/-- Every working-copy clash between two groups is a canonical conflict, so the
collision check sees every "already declared" error the renderer could cause. -/
theorem render_clash_conflict {g h : group} (hne : g ≠ h) {y y' : LeanName mod atom sfx}
    (hg : binds C g y) (hh : binds C h y')
    (hy : ∀ b s, y ≠ .res b s) (hy' : ∀ b s, y' ≠ .res b s)
    (he : render g y = render h y') :
    ∃ b, y = .pub b ∧ y' = .pub b ∧ Conflict C enc g h (enc b) := by
  rcases (render_clash_iff hne hy hy').1 he with ⟨b, rfl, rfl⟩
  exact ⟨b, rfl, rfl, hne, (member_iff_public C enc g _).2 ⟨b, rfl, hg⟩,
    (member_iff_public C enc h _).2 ⟨b, rfl, hh⟩⟩

/-! ### Eager auxiliaries

An eager auxiliary is the public name `der b e` for base `b` and fixed suffix `e`
(`casesOn`, `recOn`, `below`, `mk`, a projection, ...), produced by the same
command as `b`. -/

/-- Capture well-formedness: a command producing `der b e` also produces `b`.
Holds for inductive and structure commands; fails for a hand-written
`def T.casesOn` without `T`, which is then an ordinary public name. -/
def DerivedClosed {eager : Type} (der : atom → eager → atom) : Prop :=
  ∀ c b e, C.produces c (.pub (der b e)) → C.produces c (.pub b)

/-- Two groups collide on a derived eager name iff they collide on its base and
both produce the derived name. Derived names add no collision beyond their
base's. -/
theorem derived_collision_iff {eager : Type} (hinj : Function.Injective enc)
    (der : atom → eager → atom) (hcl : DerivedClosed C der) (g h : group) (b : atom) (e : eager) :
    Conflict C enc g h (enc (der b e)) ↔
      Conflict C enc g h (enc b) ∧ binds C g (.pub (der b e)) ∧ binds C h (.pub (der b e)) := by
  constructor
  · intro hc
    rcases (public_collision_iff C enc hinj g h _).1 hc with ⟨hne, b', hb', hg, hh⟩
    have hb : b' = der b e := hinj hb'
    subst hb
    rcases hg with ⟨c, hcg, hpc⟩
    rcases hh with ⟨c', hch, hpc'⟩
    exact ⟨(public_collision_iff C enc hinj g h _).2
        ⟨hne, b, rfl, ⟨c, hcg, hcl c b e hpc⟩, ⟨c', hch, hcl c' b e hpc'⟩⟩,
      ⟨c, hcg, hpc⟩, ⟨c', hch, hpc'⟩⟩
  · rintro ⟨hc, hg, hh⟩
    exact (public_collision_iff C enc hinj g h _).2 ⟨hc.1, der b e, rfl, hg, hh⟩

/-- With `der` injective on `(base, suffix)`, a derived canonical name
determines its base and suffix, so each derived collision has one base. -/
theorem derived_name_determines_base {eager : Type} (hinj : Function.Injective enc)
    (der : atom → eager → atom) (hder : Function.Injective (fun p : atom × eager => der p.1 p.2))
    {b b' : atom} {e e' : eager} (he : enc (der b e) = enc (der b' e')) : b = b' ∧ e = e' := by
  have := hder (a₁ := (b, e)) (a₂ := (b', e')) (hinj he)
  simp only [Prod.mk.injEq] at this
  exact this

/-! ### Canonical instance names

`instName τ` is the fork's deterministic name for an anonymous instance of type
`τ` (no `_n` deduplication). Both results are definitional consequences of
classifying `instName τ` as public. -/

/-- An instance-only command has a public anchor: its group is a member of the
canonical instance name. -/
theorem instance_anchor {ty : Type} (instName : ty → atom) (c : command) (τ : ty)
    (hp : C.produces c (.pub (instName τ))) :
    member C enc (C.capture c) (enc (instName τ)) :=
  ⟨c, _, rfl, hp, rfl⟩

/-- Two groups declaring an anonymous instance of the same type conflict on the
canonical instance name (a duplicate instance). -/
theorem instance_collision {ty : Type} (instName : ty → atom) {c c' : command}
    (hne : C.capture c ≠ C.capture c') (τ : ty)
    (hp : C.produces c (.pub (instName τ))) (hp' : C.produces c' (.pub (instName τ))) :
    Conflict C enc (C.capture c) (C.capture c') (enc (instName τ)) :=
  ⟨hne, instance_anchor C enc instName c τ hp, instance_anchor C enc instName c' τ hp'⟩

/-- Consumer-side realization: a consumer's environment may gain reserved
constants (Lean's `realizeConst` calls `addDecl` in the consumer). Even if a
naive capture attributes them to the consumer command `c`, membership is
unchanged. -/
def Capture.withRealized (c : command) (ys : LeanName mod atom sfx → Prop) :
    Capture command group mod atom sfx where
  capture := C.capture
  produces c' y := C.produces c' y ∨ (c' = c ∧ ys y)

theorem realization_member_eq (c : command) (ys : LeanName mod atom sfx → Prop)
    (hres : ∀ y, ys y → ∃ b s, y = .res b s) :
    member (C.withRealized c ys) enc = member C enc := by
  funext g x
  apply propext
  constructor
  · rintro ⟨c', y, hc, hp | ⟨_, hy⟩, hx⟩
    · exact ⟨c', y, hc, hp, hx⟩
    · rcases hres y hy with ⟨b, s, rfl⟩
      simp [canon] at hx
  · rintro ⟨c', y, hc, hp, hx⟩
    exact ⟨c', y, hc, Or.inl hp, hx⟩

end Naming

/-! ## Instantiating the group registry -/

noncomputable section Registry
attribute [local instance] Classical.propDecidable
open ParaleanGroups

variable {node group name snapshot command mod atom sfx : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]

/-- The registry theory whose `member` is the refined membership. Revisions are
given on canonical names and restricted to names both groups bind. -/
def namingTheory (base : Theory node group name snapshot)
    (C : Capture command group mod atom sfx) (enc : atom → name)
    (rev : group → group → name → Prop) : Theory node group name snapshot :=
  { base with
    member := fun g x => decide (member C enc g x)
    revisions := fun g a x => decide (rev g a x ∧ member C enc g x ∧ member C enc a x)
    ancestors := fun g a => decide (∃ x, rev g a x ∧ member C enc g x ∧ member C enc a x) }

/-- `valid_ancestry` and the snapshot assumptions hold for the refined theory
whenever revisions are per-name transitive and every valid group has a public output. -/
theorem naming_assumptions (base : Theory node group name snapshot)
    (C : Capture command group mod atom sfx) (enc : atom → name)
    (rev : group → group → name → Prop)
    (htrans : ∀ g a b x, rev g a x → rev a b x → rev g b x)
    (hpub : ∀ g, base.valid g = true → ∃ c b, C.capture c = g ∧ C.produces c (.pub b))
    (hempty : ∀ d, base.contents base.emptySnapshot d ≠ true)
    (hexp : base.exportable base.emptySnapshot = true) :
    TheoryAssumptions (namingTheory base C enc rev) := by
  dsimp [TheoryAssumptions, Assumptions, valid_ancestry, empty_contents, empty_exportable,
    namingTheory, readFrom, instIsSubReaderOfRefl]
  simp only [decide_eq_true_eq]
  refine ⟨⟨fun _ _ => trivial, ?_, ?_⟩, ?_, hexp⟩
  · intro g a x _ he
    refine ⟨he.2.1, he.2.2, ?_⟩
    intro b hb
    exact ⟨htrans g a b x he.1 hb.1, he.2.1, hb.2.2⟩
  · intro g hv
    rcases hpub g hv with ⟨c, b, hc, hp⟩
    exact ⟨enc b, c, .pub b, hc, hp, rfl⟩
  · intro d hd
    exact hempty d hd

/-- A canonical conflict inside one snapshot makes it unbuildable. -/
theorem conflict_not_buildable (base : Theory node group name snapshot)
    (C : Capture command group mod atom sfx) (enc : atom → name)
    (rev : group → group → name → Prop) (st : CanonicalState node group name snapshot)
    (S : snapshot) (g h : group) (x : name) (hc : Conflict C enc g h x)
    (hg : base.contents S g = true) (hh : base.contents S h = true) :
    ¬buildable S (namingTheory base C enc rev) st := by
  rintro ⟨_, _, hu, _⟩
  apply hc.1
  exact hu g h x hg hh (by simpa [namingTheory] using hc.2.1)
    (by simpa [namingTheory] using hc.2.2)

/-- Consumer realization leaves the registry theory, hence every Groups
predicate and transition, unchanged. -/
theorem realization_theory_eq (base : Theory node group name snapshot)
    (C : Capture command group mod atom sfx) (enc : atom → name)
    (rev : group → group → name → Prop) (c : command) (ys : LeanName mod atom sfx → Prop)
    (hres : ∀ y, ys y → ∃ b s, y = .res b s) :
    namingTheory base (C.withRealized c ys) enc rev = namingTheory base C enc rev := by
  simp only [namingTheory, realization_member_eq C enc c ys hres]

/-- Deterministic realization: the constant for `b.s` is computed from the
group binding the base `b` (Lean's `realizeConst` is keyed by base constant and
evaluated in the base's environment). -/
def Realized (C : Capture command group mod atom sfx) {const : Type}
    (R : group → LeanName mod atom sfx → sfx → const)
    (inS : group → Prop) (y : LeanName mod atom sfx) (k : const) : Prop :=
  ∃ b s g, y = .res b s ∧ inS g ∧ binds C g b ∧ k = R g b s

/-- Two consumers holding the same buildable snapshot realize identical
constants for a reserved name over a public base; realization adds no
membership, so heads, currency and buildability are unchanged. -/
theorem reserved_consumer_deterministic (base : Theory node group name snapshot)
    (C : Capture command group mod atom sfx) (enc : atom → name)
    (rev : group → group → name → Prop) {const : Type}
    (R : group → LeanName mod atom sfx → sfx → const)
    (st₁ st₂ : CanonicalState node group name snapshot) (S : snapshot)
    (hb : buildable S (namingTheory base C enc rev) st₁)
    (b₀ : atom) (s₀ : sfx) (k₁ k₂ : const)
    (h₁ : Realized C R (fun g => base.contents S g = true) (.res (.pub b₀) s₀) k₁)
    (h₂ : Realized C R (fun g => base.contents S g = true) (.res (.pub b₀) s₀) k₂)
    (c : command) (ys : LeanName mod atom sfx → Prop)
    (hres : ∀ y, ys y → ∃ b s, y = .res b s) :
    k₁ = k₂ ∧
      (∀ n d x, isHead n d x (namingTheory base (C.withRealized c ys) enc rev) st₂ ↔
        isHead n d x (namingTheory base C enc rev) st₂) ∧
      (∀ n T, current n T (namingTheory base (C.withRealized c ys) enc rev) st₂ ↔
        current n T (namingTheory base C enc rev) st₂) ∧
      (∀ T, buildable T (namingTheory base (C.withRealized c ys) enc rev) st₂ ↔
        buildable T (namingTheory base C enc rev) st₂) ∧
      (∀ g h x, Conflict (C.withRealized c ys) enc g h x ↔ Conflict C enc g h x) := by
  have heq := realization_theory_eq base C enc rev c ys hres
  have hm := realization_member_eq C enc c ys hres
  refine ⟨?_, by rw [heq]; simp, by rw [heq]; simp, by rw [heq]; simp,
    by intro g h x; simp [Conflict, hm]⟩
  rcases h₁ with ⟨b, s, g, he, hg, hgb, rfl⟩
  rcases h₂ with ⟨b', s', g', he', hg', hgb', rfl⟩
  cases he; cases he'
  have hu := hb.2.2.1 g g' (enc b₀) hg hg'
    (by simpa [namingTheory] using (member_iff_public C enc g (enc b₀)).2 ⟨b₀, rfl, hgb⟩)
    (by simpa [namingTheory] using (member_iff_public C enc g' (enc b₀)).2 ⟨b₀, rfl, hgb'⟩)
  rw [hu]

end Registry

/-! ## Concrete instance

Atoms: `0 = instFooNat`, `1 = foo`, `2 = bar`, `3 = aux`, `4 = T`,
`5 = T.casesOn`, `6 = proof_1`; module `0 = A`; suffix `0 = eq_1`.

* Command/group 0 (agent 0) defines `foo`, `instance : Foo Nat` (canonical
  public name `instFooNat`), `private def aux` (`_private.A.0.aux`) and a
  compiler auxiliary `proof_1`; its proof realises `foo.eq_1`.
* Command/group 1 (agent 1, depending on group 0) defines `bar` and an
  inductive `T` with eager `T.casesOn`, and also its own `private def aux` and
  `proof_1` in the same module `A`; it realises `foo.eq_1`.
* Command/group 2 (agent 2) independently defines `foo` and
  `instance : Foo Nat`: genuine collisions on `foo` and on `instFooNat`.

Reserved names are listed as outputs to model the worst case where a naive
capture records the consumer's `realizeConst` `addDecl`. -/

noncomputable section Instance
open ParaleanGroups

abbrev LN := LeanName (Fin 2) (Fin 7) (Fin 1)

instance : Inhabited LN := ⟨.pub 0⟩

def outputs (c : Fin 3) : List LN :=
  if c = 0 then [.pub 0, .pub 1, .priv 0 3, .gen 6, .res (.pub 1) 0]
  else if c = 1 then [.pub 2, .pub 4, .pub 5, .priv 0 3, .gen 6, .res (.pub 1) 0]
  else [.pub 0, .pub 1]

def instC : Capture (Fin 3) (Fin 3) (Fin 2) (Fin 7) (Fin 1) where
  capture := id
  produces c y := y ∈ outputs c

def table (g : Fin 3) (x : Fin 7) : Bool :=
  decide ((g = 0 ∨ g = 2) ∧ (x = 0 ∨ x = 1) ∨ g = 1 ∧ (x = 2 ∨ x = 4 ∨ x = 5))

theorem inst_member_iff (g : Fin 3) (x : Fin 7) :
    member instC id g x ↔ table g x = true := by
  rw [member_iff_public]
  simp only [binds, instC, id]
  revert g x
  decide

/-- Under `canon`, the only conflicts are groups 0 and 2 on `instFooNat` and `foo`. -/
theorem inst_conflicts_exact (g h : Fin 3) (x : Fin 7) :
    Conflict instC id g h x ↔ ((g = 0 ∧ h = 2 ∨ g = 2 ∧ h = 0) ∧ (x = 0 ∨ x = 1)) := by
  simp only [Conflict, inst_member_iff]
  revert g h x
  decide

/-- Non-vacuity of the three classes and of rendering: groups 0 and 1 each
produce `private def aux` and `proof_1` in module `A`; these are scoped, render
to distinct Lean names and do not conflict. The duplicate `instance : Foo Nat`
of groups 0 and 2 renders to the same name and is a canonical conflict, found
through `instance_collision`. `T.casesOn` is public and conflict-free. -/
theorem inst_classes :
    (∀ g : Fin 3, g ≠ 2 → binds instC g (.priv 0 3) ∧ binds instC g (.gen 6) ∧
      binds instC g (.res (.pub 1) 0)) ∧
    kind (LeanName.gen 6 : LN) = .scoped ∧ kind (LeanName.priv 0 3 : LN) = .scoped ∧
    kind (LeanName.res (.pub 1) 0 : LN) = .reserved (.pub 1) ∧
    kind (LeanName.pub 0 : LN) = .pub ∧ kind (LeanName.pub 5 : LN) = .pub ∧
    render (0 : Fin 3) (LeanName.priv 0 3 : LN) ≠ render (1 : Fin 3) (LeanName.priv 0 3 : LN) ∧
    render (0 : Fin 3) (LeanName.gen 6 : LN) ≠ render (1 : Fin 3) (LeanName.gen 6 : LN) ∧
    (∀ x, ¬Conflict instC id 0 1 x) ∧
    render (0 : Fin 3) (LeanName.pub 0 : LN) = render (2 : Fin 3) (LeanName.pub 0 : LN) ∧
    Conflict instC id 0 2 0 ∧
    member instC id 1 5 ∧ (∀ g h, ¬Conflict instC id g h 5) := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, by decide, by decide, ?_, rfl, ?_, ?_, ?_⟩
  · intro g hg
    refine ⟨⟨g, rfl, ?_⟩, ⟨g, rfl, ?_⟩, ⟨g, rfl, ?_⟩⟩ <;>
      (simp only [instC]; revert g; decide)
  · intro x hc
    rcases (inst_conflicts_exact 0 1 x).1 hc with ⟨h, _⟩
    revert h; decide
  · exact instance_collision instC id (fun _ : Unit => (0 : Fin 7)) (c := 0) (c' := 2)
      (by decide) () (by simp [instC]; decide) (by simp [instC]; decide)
  · exact (inst_member_iff 1 5).2 (by decide)
  · intro g h hc
    rcases (inst_conflicts_exact g h 5).1 hc with ⟨_, hx⟩
    revert hx; decide

/-- Registry theory: group 1 pins group 0; snapshot `true` selects groups 0 and 1. -/
def instTheory : Theory Unit (Fin 3) (Fin 7) Bool where
  valid := fun _ => true
  deps := fun g e => decide (g = 1 ∧ e = 0)
  ancestors := fun _ _ => false
  member := table
  revisions := fun _ _ _ => false
  contents := fun S g => decide (S = true ∧ g ≠ 2)
  exportable := fun _ => true
  emptySnapshot := false

theorem inst_public_output (g : Fin 3) :
    ∃ c b, instC.capture c = g ∧ instC.produces c (.pub b) := by
  refine ⟨g, if g = 1 then 2 else 1, rfl, ?_⟩
  simp only [instC]
  revert g; decide

section
attribute [local instance] Classical.propDecidable

/-- The concrete theory is exactly the refined theory built from `instC`. -/
theorem inst_theory_eq :
    namingTheory instTheory instC id (fun _ _ _ => False) = instTheory := by
  have hm : (fun g x => decide (member instC id g x)) = table := by
    funext g x
    exact Bool.eq_iff_iff.2 (by simpa using inst_member_iff g x)
  simp only [namingTheory, hm]
  simp [instTheory]

theorem inst_assumptions : TheoryAssumptions instTheory := by
  have h := naming_assumptions instTheory instC id (fun _ _ _ => False)
    (fun _ _ _ _ h _ => h)
    (fun g _ => inst_public_output g)
    (by decide) rfl
  rwa [inst_theory_eq] at h
end

def prog (k : Nat) (p : Option (Fin 3)) (hd : Bool) :
    CanonicalState Unit (Fin 3) (Fin 7) Bool where
  published := fun g => decide (g.val < k)
  known := fun _ g => decide (g.val < k)
  pending := fun _ g => decide (p = some g)
  head := fun _ => hd
  alive := fun _ => true
  online := fun _ => true
  stable := false
  clock := k
  rank := fun g => if g.val < k then g.val else 0

theorem inst_initial : GroupsInit instTheory (prog 0 none false) := by
  dsimp [GroupsInit, Init, initializer.ext.tr, prog, instTheory, getFrom, setIn,
    readFrom, Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    canonicalFieldRep, Veil.canonicalFieldRepresentation]
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

theorem inst_prepare_step (g : Fin 3) (hd : Bool) :
    GroupsNext instTheory (prog g.val none hd) (.prepare () g) (prog g.val (some g) hd) := by
  simp only [GroupsNext, Next, NextAct, prepare.ext.derived_eq]
  dsimp [prepare.ext.tr, prog, instTheory, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    canonicalFieldRep, Veil.canonicalFieldRepresentation]
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]
  repeat' constructor
  all_goals first | (intro a ha; simp_all; omega) | omega

theorem inst_publish_step (g : Fin 3) (hd : Bool) :
    GroupsNext instTheory (prog g.val (some g) hd) (.publish () g)
      (prog (g.val + 1) none hd) := by
  simp only [GroupsNext, Next, NextAct, publish.ext.derived_eq]
  dsimp [publish.ext.tr, prog, getFrom, setIn, readFrom,
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

theorem inst_commit_step :
    GroupsNext instTheory (prog 2 none false) (.commit () true) (prog 2 none true) := by
  simp only [GroupsNext, Next, NextAct, commit.ext.derived_eq]
  dsimp [commit.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
    Veil.canonicalFieldRepresentation]
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, rfl, by decide, ?_⟩
  simp [prog, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

/-- Publish groups 0 and 1, commit the snapshot selecting both, then publish
the colliding group 2. -/
theorem inst_reachable : Reachable instTheory (prog 3 none true) := by
  have h0 := Reachable.initial inst_initial
  have h1 := Reachable.step h0 (inst_prepare_step 0 false)
  have h2 := Reachable.step h1 (inst_publish_step 0 false)
  have h3 := Reachable.step h2 (inst_prepare_step 1 false)
  have h4 := Reachable.step h3 (inst_publish_step 1 false)
  have h5 := Reachable.step h4 inst_commit_step
  have h6 := Reachable.step h5 (inst_prepare_step 2 true)
  exact Reachable.step h6 (inst_publish_step 2 true)

/-- Non-vacuity: both agents' groups, each with its own `private def aux`,
`proof_1` and realised `foo.eq_1`, are committed together in a reachable
checkpoint; the only canonical conflicts are the genuine `foo` and `instFooNat`
collisions with group 2, which then block any commit of a snapshot containing
group 0. -/
theorem inst_nonvacuous :
    Reachable instTheory (prog 2 none true) ∧
    Reachable instTheory (prog 3 none true) ∧
    (prog 3 none true).head () = true ∧
    SnapshotBinding instTheory ((prog 3 none true).head ()) 0 1 ∧
    SnapshotBinding instTheory ((prog 3 none true).head ()) 1 2 ∧
    (∀ g h x, Conflict instC id g h x ↔ ((g = 0 ∧ h = 2 ∨ g = 2 ∧ h = 0) ∧ (x = 0 ∨ x = 1))) ∧
    ¬∃ st', GroupsNext instTheory (prog 3 none true) (.commit () true) st' := by
  have h5 : Reachable instTheory (prog 2 none true) := by
    have h0 := Reachable.initial inst_initial
    have h1 := Reachable.step h0 (inst_prepare_step 0 false)
    have h2 := Reachable.step h1 (inst_publish_step 0 false)
    have h3 := Reachable.step h2 (inst_prepare_step 1 false)
    have h4 := Reachable.step h3 (inst_publish_step 1 false)
    exact Reachable.step h4 inst_commit_step
  refine ⟨h5, inst_reachable, rfl, by unfold SnapshotBinding; decide,
    by unfold SnapshotBinding; decide, inst_conflicts_exact, ?_⟩
  rintro ⟨st', ht⟩
  exact overlapping_heads_block_commit instTheory _ st' () true 0 2 0 1
    (by decide) (by decide) (by decide) (by decide) (by decide) ht

/-- Naive capture: every produced Lean name, raw, is a member. -/
def rawTheory : Theory Unit (Fin 3) LN Bool :=
  { instTheory with
    member := fun g y => decide (y ∈ outputs g)
    revisions := fun _ _ _ => false }

/-- Guard necessity: raw membership reports a false collision between groups 0
and 1 on the compiler auxiliary `proof_1` (and on the private and realised
names), so the snapshot that the canonical layer commits is unbuildable; under
`canon` groups 0 and 1 never conflict. -/
theorem naive_false_collision :
    rawTheory.member 0 (.gen 6) = true ∧ rawTheory.member 1 (.gen 6) = true ∧
    rawTheory.member 0 (.priv 0 3) = true ∧ rawTheory.member 1 (.priv 0 3) = true ∧
    rawTheory.member 0 (.res (.pub 1) 0) = true ∧ rawTheory.member 1 (.res (.pub 1) 0) = true ∧
    kind (LeanName.gen 6 : LN) = .scoped ∧
    (∀ st : CanonicalState Unit (Fin 3) LN Bool, ¬buildable true rawTheory st) ∧
    (∀ x, ¬Conflict instC id 0 1 x) ∧
    buildable true instTheory (prog 2 none false) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, rfl, ?_, ?_, by decide⟩
  · rintro st ⟨_, _, hu, _⟩
    exact absurd (hu 0 1 (.gen 6) (by decide) (by decide) (by decide) (by decide)) (by decide)
  · intro x hc
    rcases (inst_conflicts_exact 0 1 x).1 hc with ⟨h, _⟩
    revert h; decide

/-- Capture at `addDecl` granularity splits one command's outputs across groups. -/
def perDecl : Capture LN LN (Fin 2) (Fin 7) (Fin 1) where
  capture := id
  produces c y := y = c

theorem addDecl_capture_splits :
    (∃ y y', y ∈ outputs 0 ∧ y' ∈ outputs 0 ∧
      perDecl.capture y ≠ perDecl.capture y' ∧ perDecl.produces y y ∧ perDecl.produces y' y') ∧
    (∀ y, y ∈ outputs 0 → binds instC 0 y) :=
  ⟨⟨.gen 6, .pub 1, by decide, by decide, by simp [perDecl], rfl, rfl⟩,
    fun y hy => ⟨0, rfl, hy⟩⟩

end Instance

#print axioms canon_injective_public
#print axioms aux_same_group
#print axioms scoped_render_distinct
#print axioms render_clash_iff
#print axioms render_clash_conflict
#print axioms derived_collision_iff
#print axioms derived_name_determines_base
#print axioms instance_anchor
#print axioms instance_collision
#print axioms relocation_invariant
#print axioms public_collision_iff
#print axioms realization_member_eq
#print axioms naming_assumptions
#print axioms conflict_not_buildable
#print axioms realization_theory_eq
#print axioms reserved_consumer_deterministic
#print axioms inst_member_iff
#print axioms inst_conflicts_exact
#print axioms inst_classes
#print axioms inst_theory_eq
#print axioms inst_assumptions
#print axioms inst_reachable
#print axioms inst_nonvacuous
#print axioms naive_false_collision
#print axioms addDecl_capture_splits

end ParaleanLeanNames
