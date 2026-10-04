import Paralean.Groups
import Paralean.Delivery
import Paralean.Admission

/-! Catalog recovery with atomic group snapshots and generated storage coupling.
Scan tokens contain schema-validated physical enumeration and readiness results.
The computed admissible set excludes staged records that fail validation/readiness.
Desktop loss clears all volatile IDs and writer authorization. -/
set_option veil.smt.trust false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

veil module ParaleanRecovery

type record
type workspace
type snapshot
type decl
type name
type token
type scan
immutable function tokenRank : token → Nat
immutable individual identity : workspace
immutable function recordWorkspace : record → workspace
immutable function image : record → snapshot
immutable function causalRank : record → Nat
immutable relation parent : record → record → Bool
immutable relation ancestor : record → record → Bool
immutable relation valid : decl → Bool
immutable relation deps : decl → decl → Bool
immutable relation member : decl → name → Bool
immutable relation contents : snapshot → decl → Bool
immutable relation exportable : snapshot → Bool
immutable relation decoded : scan → record → Bool
immutable relation ready : scan → record → Bool
relation committed : record → Bool
relation durableAck : record → Bool
relation known : record → Bool
relation heads : record → Bool
individual scanned : Bool
individual reconstructed : Bool
individual conflict : Bool
individual selected : Bool
individual selectedRecord : record
individual writer : Bool
individual fence : Nat
#gen_state
assumption [ancestry] ∀ c p, ancestor c p → causalRank p < causalRank c
assumption [parents_are_ancestors] ∀ c p, parent c p → ancestor c p
assumption [transitive_ancestry] ∀ c p a, ancestor c p → ancestor p a → ancestor c a
-- Every ancestry edge must be justified by a parent edge. Rank descent makes
-- this recursive decomposition exactly nonempty parent-path reachability.
assumption [ancestry_has_parent] ∀ c a, ancestor c a →
  ∃ p, parent c p ∧ (p = a ∨ ancestor p a)

ghost relation buildable (S : snapshot) :=
  (∀ d, contents S d → valid d) ∧
  (∀ d e, contents S d → deps d e → contents S e) ∧
  (∀ d e x, contents S d → contents S e → member d x → member e x → d = e) ∧ exportable S

ghost relation admissible (v : scan) (c : record) :=
  decoded v c ∧ ready v c ∧ recordWorkspace c = identity ∧ buildable (image c) ∧
  (∀ p, ancestor c p → decoded v p ∧ ready v p ∧ recordWorkspace p = identity ∧ buildable (image p))

after_init {
  committed C := false
  durableAck C := false
  known C := false
  heads C := false
  scanned := false
  reconstructed := false
  conflict := false
  selected := false
  selectedRecord := (default : record)
  writer := true
  fence := 0
}

action commit (c : record) (epoch : token) {
  require writer ∧ tokenRank epoch = fence
  require ¬committed c
  require recordWorkspace c = identity
  require buildable (image c)
  require ∀ p, ancestor c p → committed p
  committed c := true
  durableAck c := true
  known C := false
  heads C := false
  scanned := false
  reconstructed := false
  conflict := false
  selected := false
}

action loseDesktop {
  known C := false
  heads C := false
  scanned := false
  reconstructed := false
  conflict := false
  selected := false
  selectedRecord := (default : record)
  writer := false
}

-- Atomic exclusive lease rotation. An old writer token cannot commit.
action rotateFence (epoch : token) {
  require tokenRank epoch > fence
  fence := tokenRank epoch
  writer := true
}

action enumerate (v : scan) {
  require ∀ c, committed c → decoded v c ∧ ready v c
  known C := decide (admissible v C)
  committed C := committed C || decide (admissible v C)
  durableAck C := durableAck C || decide (admissible v C)
  heads C := false
  scanned := true
  reconstructed := false
  conflict := false
  selected := false
}

action reconstruct {
  require scanned
  heads C := decide (known C ∧ ¬∃ d, known d ∧ ancestor d C)
  conflict := decide (∃ c d, known c ∧ ¬(∃ e, known e ∧ ancestor e c) ∧
    known d ∧ ¬(∃ e, known e ∧ ancestor e d) ∧ c ≠ d)
  reconstructed := true
  selected := false
}

-- Automatic recovery is only permitted for a unique causal head.
action automatic (c : record) {
  require reconstructed ∧ heads c
  require ∀ d, heads d → d = c
  selectedRecord := c
  selected := true
}

-- Explicit historical choice never overwrites the reconstructed conflict.
action historical (c : record) {
  require reconstructed ∧ known c
  selectedRecord := c
  selected := true
}

invariant [Records] ∀ c, committed c → recordWorkspace c = identity ∧
  durableAck c ∧ buildable (image c) ∧
  (∀ p, ancestor c p → committed p)
invariant [KnownSound] ∀ c, known c → committed c
invariant [CatalogComplete] scanned → ∀ c, known c ↔ committed c
invariant [HeadsExact] reconstructed → scanned ∧
  (∀ c, heads c ↔ committed c ∧ ¬∃ d, committed d ∧ ancestor d c)
invariant [ConflictExact] reconstructed →
  (conflict ↔ ∃ c d, heads c ∧ heads d ∧ c ≠ d)
invariant [SelectedBacked] selected → reconstructed ∧ known selectedRecord
#gen_spec

section Proofs
variable (ρ σ record workspace snapshot decl name token scan : Type)
variable [DecidableEq record] [Inhabited record]
variable [DecidableEq workspace] [Inhabited workspace]
variable [DecidableEq snapshot] [Inhabited snapshot]
variable [DecidableEq decl] [Inhabited decl]
variable [DecidableEq name] [Inhabited name]
variable [DecidableEq token] [Inhabited token]
variable [DecidableEq scan] [Inhabited scan]
variable (χ : State.Label → Type)
variable [χ_rep : ∀ f, Veil.FieldRepresentation
  (State.Label.toDomain record workspace snapshot decl name token scan f)
  (State.Label.toCodomain record workspace snapshot decl name token scan f) (χ f)]
variable [∀ f, Veil.LawfulFieldRepresentation
  (State.Label.toDomain record workspace snapshot decl name token scan f)
  (State.Label.toCodomain record workspace snapshot decl name token scan f) (χ f) (χ_rep f)]
variable [IsSubStateOf (State χ) σ]
variable [IsSubReaderOf (Theory record workspace snapshot decl name token scan) ρ]


variable [commit_dec_0 : delta% (commit._veil_dec_type_0
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan))]
variable [commit_dec_1 : delta% (commit._veil_dec_type_1
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan) (χ := χ))]
variable [reconstruct_dec_0 : delta% (reconstruct._veil_dec_type_0
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan) (χ := χ))]
variable [reconstruct_dec_1 : delta% (reconstruct._veil_dec_type_1
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan) (χ := χ))]
variable [enumerate_dec_1 : delta% (enumerate._veil_dec_type_1
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan))]
variable [enumerate_dec_0 : delta% (enumerate._veil_dec_type_0
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan) (χ := χ))]
variable [automatic_dec_0 : delta% (automatic._veil_dec_type_0
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan) (χ := χ))]

theorem commit_preserves (c : record) (epoch : token) :
  Veil.Transition.meetsSpecificationIfSuccessfulAssuming
    (commit.ext.tr ρ σ record workspace snapshot decl name token scan χ c epoch)
    (Assumptions ρ record workspace snapshot decl name token scan)
    (Invariants ρ σ record workspace snapshot decl name token scan χ)
    (Invariants ρ σ record workspace snapshot decl name token scan χ) := by
  unveil
  grind (splits := 30)

theorem loseDesktop_preserves :
  Veil.Transition.meetsSpecificationIfSuccessfulAssuming
    (loseDesktop.ext.tr ρ σ record workspace snapshot decl name token scan χ)
    (Assumptions ρ record workspace snapshot decl name token scan)
    (Invariants ρ σ record workspace snapshot decl name token scan χ)
    (Invariants ρ σ record workspace snapshot decl name token scan χ) := by
  unveil
  grind (splits := 30)

theorem rotateFence_preserves (epoch : token) :
  Veil.Transition.meetsSpecificationIfSuccessfulAssuming
    (rotateFence.ext.tr ρ σ record workspace snapshot decl name token scan χ epoch)
    (Assumptions ρ record workspace snapshot decl name token scan)
    (Invariants ρ σ record workspace snapshot decl name token scan χ)
    (Invariants ρ σ record workspace snapshot decl name token scan χ) := by
  unveil
  grind (splits := 30)

theorem enumerate_preserves (v : scan) :
  Veil.Transition.meetsSpecificationIfSuccessfulAssuming
    (enumerate.ext.tr ρ σ record workspace snapshot decl name token scan χ v)
    (Assumptions ρ record workspace snapshot decl name token scan)
    (Invariants ρ σ record workspace snapshot decl name token scan χ)
    (Invariants ρ σ record workspace snapshot decl name token scan χ) := by
  veil_apply_local_tr
  grind (splits := 30)

theorem reconstruct_preserves :
  Veil.Transition.meetsSpecificationIfSuccessfulAssuming
    (reconstruct.ext.tr ρ σ record workspace snapshot decl name token scan χ)
    (Assumptions ρ record workspace snapshot decl name token scan)
    (Invariants ρ σ record workspace snapshot decl name token scan χ)
    (Invariants ρ σ record workspace snapshot decl name token scan χ) := by
  unveil
  grind (splits := 30)

theorem automatic_preserves (c : record) :
  Veil.Transition.meetsSpecificationIfSuccessfulAssuming
    (automatic.ext.tr ρ σ record workspace snapshot decl name token scan χ c)
    (Assumptions ρ record workspace snapshot decl name token scan)
    (Invariants ρ σ record workspace snapshot decl name token scan χ)
    (Invariants ρ σ record workspace snapshot decl name token scan χ) := by
  unveil
  grind (splits := 30)

theorem historical_preserves (c : record) :
  Veil.Transition.meetsSpecificationIfSuccessfulAssuming
    (historical.ext.tr ρ σ record workspace snapshot decl name token scan χ c)
    (Assumptions ρ record workspace snapshot decl name token scan)
    (Invariants ρ σ record workspace snapshot decl name token scan χ)
    (Invariants ρ σ record workspace snapshot decl name token scan χ) := by
  unveil
  grind (splits := 30)

theorem initializer_preserves :
  Veil.Transition.meetsSpecificationIfSuccessfulAssuming
    (initializer.ext.tr ρ σ record workspace snapshot decl name token scan χ)
    (Assumptions ρ record workspace snapshot decl name token scan)
    (fun _ _ => True)
    (Invariants ρ σ record workspace snapshot decl name token scan χ) := by
  unveil
  grind (splits := 30)

variable [Inhabited σ]

theorem Init_preserves (th : ρ) (s : σ)
    (ha : Assumptions ρ record workspace snapshot decl name token scan th)
    (hi : Init ρ σ record workspace snapshot decl name token scan χ th s) :
    Invariants ρ σ record workspace snapshot decl name token scan χ th s :=
  initializer_preserves ρ σ record workspace snapshot decl name token scan χ th default s
    ⟨ha, trivial⟩ hi

omit [Inhabited σ] in
theorem Next_preserves (th : ρ) (s s' : σ)
    (label : Label record workspace snapshot decl name token scan)
    (ha : Assumptions ρ record workspace snapshot decl name token scan th)
    (hs : Invariants ρ σ record workspace snapshot decl name token scan χ th s)
    (ht : Next ρ σ record workspace snapshot decl name token scan χ th s label s') :
    Invariants ρ σ record workspace snapshot decl name token scan χ th s' := by
  cases label <;> simp only [Next, NextAct, commit.ext.derived_eq,
    loseDesktop.ext.derived_eq, rotateFence.ext.derived_eq, enumerate.ext.derived_eq,
    reconstruct.ext.derived_eq, automatic.ext.derived_eq, historical.ext.derived_eq] at ht
  all_goals first
    | exact commit_preserves ρ σ record workspace snapshot decl name token scan χ _ _ th s s' ⟨ha, hs⟩ ht
    | exact loseDesktop_preserves ρ σ record workspace snapshot decl name token scan χ th s s' ⟨ha, hs⟩ ht
    | exact rotateFence_preserves ρ σ record workspace snapshot decl name token scan χ _ th s s' ⟨ha, hs⟩ ht
    | exact enumerate_preserves ρ σ record workspace snapshot decl name token scan χ _ th s s' ⟨ha, hs⟩ ht
    | exact reconstruct_preserves ρ σ record workspace snapshot decl name token scan χ th s s' ⟨ha, hs⟩ ht
    | exact automatic_preserves ρ σ record workspace snapshot decl name token scan χ _ th s s' ⟨ha, hs⟩ ht
    | exact historical_preserves ρ σ record workspace snapshot decl name token scan χ _ th s s' ⟨ha, hs⟩ ht

inductive Reachable (th : ρ) : σ → Prop where
  | initial {s} : Init ρ σ record workspace snapshot decl name token scan χ th s → Reachable th s
  | step {s s'} : Reachable th s → (label : Label record workspace snapshot decl name token scan) →
      Next ρ σ record workspace snapshot decl name token scan χ th s label s' → Reachable th s'

theorem reachable_invariants (th : ρ)
    (ha : Assumptions ρ record workspace snapshot decl name token scan th) {s : σ}
    (hr : Reachable ρ σ record workspace snapshot decl name token scan χ th s) :
    Invariants ρ σ record workspace snapshot decl name token scan χ th s := by
  induction hr with
  | initial hi => exact Init_preserves ρ σ record workspace snapshot decl name token scan χ th _ ha hi
  | step hr label ht ih =>
    exact Next_preserves ρ σ record workspace snapshot decl name token scan χ th _ _ label ha ih ht

end Proofs
end ParaleanRecovery

namespace ParaleanRecovery

abbrev CanonicalRep (record workspace snapshot decl name token scan : Type) (f : State.Label) :=
  Veil.CanonicalField (State.Label.toDomain record workspace snapshot decl name token scan f)
    (State.Label.toCodomain record workspace snapshot decl name token scan f)
abbrev CanonicalState (record workspace snapshot decl name token scan : Type) :=
  State (CanonicalRep record workspace snapshot decl name token scan)

noncomputable section Canonical
variable {record workspace snapshot decl name token scan : Type}
  [DecidableEq record] [Inhabited record]
  [DecidableEq workspace] [Inhabited workspace]
  [DecidableEq snapshot] [Inhabited snapshot]
  [DecidableEq decl] [Inhabited decl]
  [DecidableEq name] [Inhabited name]
  [DecidableEq token] [Inhabited token]
  [DecidableEq scan] [Inhabited scan]

@[reducible] instance canonicalFieldRep : ∀ f, Veil.FieldRepresentation
  (State.Label.toDomain record workspace snapshot decl name token scan f)
  (State.Label.toCodomain record workspace snapshot decl name token scan f)
  (CanonicalRep record workspace snapshot decl name token scan f) := by
  intro f
  cases f <;> (apply Veil.canonicalFieldRepresentation; infer_instance_for_iterated_prod)
instance canonicalFieldRepLawful : ∀ f, Veil.LawfulFieldRepresentation
  (State.Label.toDomain record workspace snapshot decl name token scan f)
  (State.Label.toCodomain record workspace snapshot decl name token scan f)
  (CanonicalRep record workspace snapshot decl name token scan f) (canonicalFieldRep f) := by
  intro f
  cases f <;> apply Veil.canonicalFieldRepresentationLawful

local instance : delta% (commit._veil_dec_type_0
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan)) :=
  fun _ _ => Classical.propDecidable _
local instance : delta% (commit._veil_dec_type_1
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan)
  (χ := CanonicalRep record workspace snapshot decl name token scan)) :=
  fun _ _ _ => Classical.propDecidable _
local instance : delta% (reconstruct._veil_dec_type_0
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan)
  (χ := CanonicalRep record workspace snapshot decl name token scan)) :=
  fun _ _ _ => Classical.propDecidable _
local instance : delta% (reconstruct._veil_dec_type_1
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan)
  (χ := CanonicalRep record workspace snapshot decl name token scan)) :=
  fun _ _ => Classical.propDecidable _
local instance : delta% (automatic._veil_dec_type_0
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan)
  (χ := CanonicalRep record workspace snapshot decl name token scan)) :=
  fun _ _ => Classical.propDecidable _

local instance : delta% (enumerate._veil_dec_type_1
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan)) :=
  fun _ _ _ => Classical.propDecidable _
local instance : delta% (enumerate._veil_dec_type_0
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan)
  (χ := CanonicalRep record workspace snapshot decl name token scan)) :=
  fun _ _ _ => Classical.propDecidable _

instance canonicalStateInhabited : Inhabited (CanonicalState record workspace snapshot decl name token scan) :=
  ⟨⟨fun _ => false, fun _ => false, fun _ => false, fun _ => false,
    false, false, false, false, default, false, 0⟩⟩

abbrev TheoryAssumptions := Assumptions (Theory record workspace snapshot decl name token scan)
  record workspace snapshot decl name token scan
abbrev RecoveryInit := Init (Theory record workspace snapshot decl name token scan)
  (CanonicalState record workspace snapshot decl name token scan) record workspace snapshot decl name token scan
  (CanonicalRep record workspace snapshot decl name token scan)
abbrev RecoveryNext := Next (Theory record workspace snapshot decl name token scan)
  (CanonicalState record workspace snapshot decl name token scan) record workspace snapshot decl name token scan
  (CanonicalRep record workspace snapshot decl name token scan)
abbrev RecoveryReachable := Reachable (Theory record workspace snapshot decl name token scan)
  (CanonicalState record workspace snapshot decl name token scan) record workspace snapshot decl name token scan
  (CanonicalRep record workspace snapshot decl name token scan)

abbrev Safe := Invariants (Theory record workspace snapshot decl name token scan)
  (CanonicalState record workspace snapshot decl name token scan) record workspace snapshot decl name token scan
  (CanonicalRep record workspace snapshot decl name token scan)

/-- Reconstruction characterizes every causal head, including competing heads. -/
theorem reconstruction_iff
    (th : Theory record workspace snapshot decl name token scan)
    (s : CanonicalState record workspace snapshot decl name token scan)
    (hs : Safe th s) (hr : s.reconstructed = true) (c : record) :
    s.heads c = true ↔ s.committed c = true ∧
      ¬∃ d, s.committed d = true ∧ th.ancestor d c = true := by
  simp only [Safe, Invariants, HeadsExact] at hs
  exact hs.2.2.2.1 hr |>.2 c

/-- Conflict reports exactly the existence of distinct maximal records. -/
theorem conflict_iff
    (th : Theory record workspace snapshot decl name token scan)
    (s : CanonicalState record workspace snapshot decl name token scan)
    (hs : Safe th s) (hr : s.reconstructed = true) :
    s.conflict = true ↔ ∃ c d, s.heads c = true ∧ s.heads d = true ∧ c ≠ d := by
  simp only [Safe, Invariants, ConflictExact] at hs
  exact hs.2.2.2.2.1 hr

/-- The selected image is an exact, committed, buildable immutable record. -/
theorem selected_record_backed
    (th : Theory record workspace snapshot decl name token scan)
    (s : CanonicalState record workspace snapshot decl name token scan)
    (hs : Safe th s) (hsel : s.selected = true) :
    s.committed s.selectedRecord = true ∧
      th.recordWorkspace s.selectedRecord = th.identity ∧
      s.durableAck s.selectedRecord = true ∧
      buildable (th.image s.selectedRecord) th s := by
  have h := hs
  simp only [Safe, Invariants, Records, KnownSound, SelectedBacked] at h
  have hk := (h.2.2.2.2.2 hsel).2
  have hc := h.2.1 _ hk
  have hb := h.1 _ hc
  exact ⟨hc, hb.1, hb.2.1, hb.2.2.1⟩

theorem catalog_complete
    (th : Theory record workspace snapshot decl name token scan)
    (s : CanonicalState record workspace snapshot decl name token scan)
    (hs : Safe th s) (hscan : s.scanned = true) (c : record) :
    s.known c = true ↔ s.committed c = true := by
  simp only [Safe, Invariants, CatalogComplete] at hs
  exact hs.2.2.1 hscan c


theorem reachable_safe
    (th : Theory record workspace snapshot decl name token scan)
    (ha : TheoryAssumptions th)
    {s : CanonicalState record workspace snapshot decl name token scan}
    (hr : RecoveryReachable th s) : Safe th s :=
  reachable_invariants _ _ record workspace snapshot decl name token scan
    (CanonicalRep record workspace snapshot decl name token scan) th ha hr

theorem automatic_no_silent_winner
    (th : Theory record workspace snapshot decl name token scan)
    (s s' : CanonicalState record workspace snapshot decl name token scan)
    (hs : Safe th s) (c : record)
    (ht : RecoveryNext th s (.automatic c) s') : s'.conflict = false := by
  simp only [RecoveryNext, Next, NextAct, automatic.ext.derived_eq] at ht
  dsimp [automatic.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
    Veil.canonicalFieldRepresentation] at ht
  rcases ht with ⟨hrec, hhead, hunique, hstate⟩
  subst s'
  have hc := conflict_iff th s hs hrec
  change s.conflict = false
  grind

theorem stale_writer_rejected
    (th : Theory record workspace snapshot decl name token scan)
    (s s' : CanonicalState record workspace snapshot decl name token scan)
    (c : record) (epoch : token) (hstale : th.tokenRank epoch ≠ s.fence) :
    ¬ RecoveryNext th s (.commit c epoch) s' := by
  intro ht
  simp only [RecoveryNext, Next, NextAct, commit.ext.derived_eq] at ht
  dsimp [commit.ext.tr, getFrom, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
    Veil.canonicalFieldRepresentation] at ht
  grind

end Canonical
end ParaleanRecovery

namespace ParaleanRecovery
noncomputable section StorageAdapter
open ParaleanGroupComposition
variable {node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq decl] [Inhabited decl]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]
  [DecidableEq replica] [Inhabited replica] [DecidableEq obj] [Inhabited obj]
  [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum]

/-- Admission requires the catalog record, exact manifest, and every snapshot package. -/
def StorageReady
    (th : ParaleanGroupComposition.Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (disk : DiskState replica obj writeQuorum readQuorum) (recordObject : obj) (S : snapshot) : Prop :=
  disk.acknowledged recordObject = true ∧ disk.acknowledged (th.manifest S) = true ∧
    ∀ d, th.registry.contents S d = true → disk.acknowledged (th.payload d) = true

/-- The catalog scan is the union of validated objects at the surviving read quorum. -/
def QuorumCatalog
    (th : ParaleanGroupComposition.Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (disk : DiskState replica obj writeQuorum readQuorum) (q : readQuorum) (recordObject : obj) : Prop :=
  ∃ r, th.storage.memberR r q = true ∧ disk.live r = true ∧ disk.stored r recordObject = true

theorem composition_checkpoint_ready
    (th : ParaleanGroupComposition.Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (ha : ParaleanGroupComposition.Assumptions th)
    {s : ParaleanGroupComposition.State node decl name snapshot replica obj writeQuorum readQuorum}
    (hr : ParaleanGroupComposition.Reachable th s) (n : node)
    (recordObject : obj) (hack : s.storage.acknowledged recordObject = true)
    (hne : s.registry.head n ≠ th.registry.emptySnapshot) :
    StorageReady th s.storage recordObject (s.registry.head n) ∧
      ParaleanGroups.buildable (s.registry.head n) th.registry s.registry := by
  have hs := ParaleanGroupComposition.reachable_safe th ha hr
  refine ⟨⟨hack, hs.2.2.2 n hne, ?_⟩, hs.1.2.2.2.2.1 n⟩
  intro d hd
  exact hs.2.2.1 d (hs.1.2.2.2.2.2.1 n d hd)

theorem ready_in_quorum_catalog
    (th : ParaleanGroupComposition.Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (disk : DiskState replica obj writeQuorum readQuorum)
    (ha : StorageAssumptions th.storage) (hs : StorageSafe th.storage disk)
    (q : readQuorum) (hq : ∀ r, th.storage.memberR r q = true → disk.live r = true)
    (recordObject : obj) (S : snapshot) (hready : StorageReady th disk recordObject S) : QuorumCatalog th disk q recordObject := by
  have hc := ParaleanGroupComposition.acknowledged_recoverable th disk ha hs
    recordObject q hready.1 hq
  have hm := ha (disk.witness recordObject) q
  exact ⟨_, hm.2, hc⟩

end StorageAdapter
end ParaleanRecovery

namespace ParaleanRecovery
noncomputable section Execution

private def executionTheory : Theory Bool Unit Bool Unit Unit Bool Unit where
  tokenRank := fun t => if t then 1 else 0
  identity := ()
  recordWorkspace := fun _ => ()
  image := id
  causalRank := fun _ => 0
  parent := fun _ _ => false
  ancestor := fun _ _ => false
  valid := fun _ => true
  deps := fun _ _ => false
  member := fun _ _ => true
  contents := fun S _ => S
  exportable := fun _ => true
  decoded := fun _ _ => true
  ready := fun _ => id

private def executionInitial : CanonicalState Bool Unit Bool Unit Unit Bool Unit :=
  ⟨fun _ => false, fun _ => false, fun _ => false, fun _ => false,
    false, false, false, false, false, true, 0⟩
private def executionCommitted : CanonicalState Bool Unit Bool Unit Unit Bool Unit :=
  { executionInitial with committed := id, durableAck := id }
private def executionScanned : CanonicalState Bool Unit Bool Unit Unit Bool Unit :=
  { executionCommitted with known := id, scanned := true }
private def executionReconstructed : CanonicalState Bool Unit Bool Unit Unit Bool Unit :=
  { executionScanned with heads := id, reconstructed := true }
private def executionSelected : CanonicalState Bool Unit Bool Unit Unit Bool Unit :=
  { executionReconstructed with selected := true, selectedRecord := true }
private def executionLost : CanonicalState Bool Unit Bool Unit Unit Bool Unit :=
  { executionCommitted with writer := false }
private def executionRescanned : CanonicalState Bool Unit Bool Unit Unit Bool Unit :=
  { executionScanned with writer := false }
private def executionRebuilt : CanonicalState Bool Unit Bool Unit Unit Bool Unit :=
  { executionReconstructed with writer := false }
private def executionRecovered : CanonicalState Bool Unit Bool Unit Unit Bool Unit :=
  { executionSelected with writer := false }

/-- The actual generated actions recover a nonempty image after erasing its ID. -/
theorem nonempty_lose_id_execution :
    TheoryAssumptions executionTheory ∧
    RecoveryInit executionTheory executionInitial ∧
    RecoveryNext executionTheory executionInitial (.commit true false) executionCommitted ∧
    RecoveryNext executionTheory executionCommitted (.enumerate ()) executionScanned ∧
    RecoveryNext executionTheory executionScanned .reconstruct executionReconstructed ∧
    RecoveryNext executionTheory executionReconstructed (.automatic true) executionSelected ∧
    RecoveryNext executionTheory executionSelected .loseDesktop executionLost ∧
    executionSelected.selectedRecord = true ∧ executionLost.selectedRecord = false ∧
    (∀ c, executionLost.known c = false) ∧
    RecoveryNext executionTheory executionLost (.enumerate ()) executionRescanned ∧
    RecoveryNext executionTheory executionRescanned .reconstruct executionRebuilt ∧
    RecoveryNext executionTheory executionRebuilt (.automatic true) executionRecovered ∧
    executionRecovered.selected = true ∧
    executionTheory.contents (executionTheory.image executionRecovered.selectedRecord) () = true := by
  repeat' apply And.intro
  all_goals try simp only [RecoveryNext, Next, NextAct, commit.ext.derived_eq,
    enumerate.ext.derived_eq, reconstruct.ext.derived_eq, automatic.ext.derived_eq,
    loseDesktop.ext.derived_eq]
  all_goals try dsimp [commit.ext.tr, enumerate.ext.tr, reconstruct.ext.tr, automatic.ext.tr, loseDesktop.ext.tr]
  all_goals simp [TheoryAssumptions, Assumptions, ancestry,
    parents_are_ancestors, transitive_ancestry, ancestry_has_parent, RecoveryInit, Init,
    RecoveryNext, Next, NextAct, initializer.ext.tr, commit.ext.derived_eq,
    enumerate.ext.derived_eq, reconstruct.ext.derived_eq, automatic.ext.derived_eq,
    loseDesktop.ext.derived_eq, commit.ext.tr, enumerate.ext.tr, reconstruct.ext.tr,
    automatic.ext.tr, loseDesktop.ext.tr, buildable,
    executionTheory, executionInitial, executionCommitted, executionScanned,
    executionReconstructed, executionSelected, executionLost, executionRescanned,
    executionRebuilt, executionRecovered, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    canonicalFieldRep, Veil.canonicalFieldRepresentation,
    Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool]

end Execution
#print axioms commit_preserves
#print axioms loseDesktop_preserves
#print axioms rotateFence_preserves
#print axioms enumerate_preserves
#print axioms reconstruct_preserves
#print axioms automatic_preserves
#print axioms historical_preserves
#print axioms Init_preserves
#print axioms Next_preserves
#print axioms reachable_safe
#print axioms reconstruction_iff
#print axioms conflict_iff
#print axioms selected_record_backed
#print axioms catalog_complete
#print axioms automatic_no_silent_winner
#print axioms stale_writer_rejected
#print axioms composition_checkpoint_ready
#print axioms ready_in_quorum_catalog
#print axioms nonempty_lose_id_execution
end ParaleanRecovery

namespace ParaleanRecovery

structure CoupledTheory (node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum : Type) where
  base : ParaleanGroupComposition.Theory node decl name snapshot replica obj writeQuorum readQuorum
  recovery : Theory record workspace snapshot decl name token scan
  recordObject : record → obj

structure CoupledState (record workspace snapshot decl name token scan replica obj writeQuorum readQuorum : Type) where
  recovery : CanonicalState record workspace snapshot decl name token scan
  storage : ParaleanGroupComposition.DiskState replica obj writeQuorum readQuorum

noncomputable section Coupling
variable {node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum : Type}
  [DecidableEq node] [Inhabited node]
  [DecidableEq record] [Inhabited record]
  [DecidableEq workspace] [Inhabited workspace]
  [DecidableEq snapshot] [Inhabited snapshot]
  [DecidableEq decl] [Inhabited decl]
  [DecidableEq name] [Inhabited name]
  [DecidableEq token] [Inhabited token]
  [DecidableEq scan] [Inhabited scan]
  [DecidableEq replica] [Inhabited replica]
  [DecidableEq obj] [Inhabited obj]
  [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum]

local instance : delta% (commit._veil_dec_type_0
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan)) :=
  fun _ _ => Classical.propDecidable _
local instance : delta% (commit._veil_dec_type_1
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan)
  (χ := CanonicalRep record workspace snapshot decl name token scan)) :=
  fun _ _ _ => Classical.propDecidable _
local instance : delta% (reconstruct._veil_dec_type_0
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan)
  (χ := CanonicalRep record workspace snapshot decl name token scan)) :=
  fun _ _ _ => Classical.propDecidable _
local instance : delta% (reconstruct._veil_dec_type_1
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan)
  (χ := CanonicalRep record workspace snapshot decl name token scan)) :=
  fun _ _ => Classical.propDecidable _
local instance : delta% (automatic._veil_dec_type_0
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan)
  (χ := CanonicalRep record workspace snapshot decl name token scan)) :=
  fun _ _ => Classical.propDecidable _
local instance : delta% (enumerate._veil_dec_type_1
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan)) :=
  fun _ _ _ => Classical.propDecidable _
local instance : delta% (enumerate._veil_dec_type_0
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan)
  (χ := CanonicalRep record workspace snapshot decl name token scan)) :=
  fun _ _ _ => Classical.propDecidable _
local instance : delta% @Durability.Ack._veil_dec_type_0 obj writeQuorum replica readQuorum
    (ParaleanGroupComposition.DiskRep replica obj writeQuorum readQuorum) ParaleanGroupComposition.diskFieldRep :=
  fun _ _ _ _ => Classical.propDecidable _
local instance : delta% @Durability.Lose._veil_dec_type_0 replica obj writeQuorum readQuorum
    (ParaleanGroupComposition.DiskRep replica obj writeQuorum readQuorum) ParaleanGroupComposition.diskFieldRep :=
  fun _ _ _ => Classical.propDecidable _

def Compatible
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum) : Prop :=
  th.recovery.valid = th.base.registry.valid ∧
  th.recovery.deps = th.base.registry.deps ∧
  th.recovery.member = th.base.registry.member ∧
  th.recovery.contents = th.base.registry.contents ∧
  th.recovery.exportable = th.base.registry.exportable

def ObjectsSeparate
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum) : Prop :=
  Function.Injective th.recordObject ∧
  (∀ c S, th.recordObject c ≠ th.base.manifest S) ∧
  (∀ c d, th.recordObject c ≠ th.base.payload d) ∧
  (∀ S d, th.base.manifest S ≠ th.base.payload d)

abbrev CoupledAssumptions
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum) :=
  ParaleanGroupComposition.StorageAssumptions th.base.storage ∧ TheoryAssumptions th.recovery ∧
    Compatible th ∧ ObjectsSeparate th

def Coupled
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (s : CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum) : Prop :=
  (∀ c, s.recovery.committed c = true → s.storage.acknowledged (th.recordObject c) = true) ∧
  (∀ c, s.recovery.committed c = true →
    s.storage.acknowledged (th.base.manifest (th.recovery.image c)) = true ∧
    ∀ d, th.base.registry.contents (th.recovery.image c) d = true →
      s.storage.acknowledged (th.base.payload d) = true)

def CoupledSafe
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (s : CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum) : Prop :=
  Safe th.recovery s.recovery ∧
    ParaleanGroupComposition.StorageSafe th.base.storage s.storage ∧ Coupled th s

def StorageGuard
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (s : CanonicalState record workspace snapshot decl name token scan)
    (label : Durability.Label replica obj writeQuorum readQuorum) : Prop :=
  match label with
  | .Ack _ _ => True
  | _ => True

inductive CoupledNext
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum) :
    CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum →
    CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum → Prop where
  | storage {rec disk disk'} (label : Durability.Label replica obj writeQuorum readQuorum) :
      ParaleanGroupComposition.StorageNext th.base.storage disk label disk' → StorageGuard th rec label →
      CoupledNext th ⟨rec, disk⟩ ⟨rec, disk'⟩
  | commit {rec rec' disk disk'} (c : record) (epoch : token) (w : writeQuorum) :
      RecoveryNext th.recovery rec (.commit c epoch) rec' →
      ParaleanGroupComposition.StorageNext th.base.storage disk (.Ack (th.recordObject c) w) disk' →
      disk.acknowledged (th.base.manifest (th.recovery.image c)) = true →
      (∀ d, th.base.registry.contents (th.recovery.image c) d = true → disk.acknowledged (th.base.payload d) = true) →
      CoupledNext th ⟨rec, disk⟩ ⟨rec', disk'⟩
  | recovery {rec rec' disk} (label : Label record workspace snapshot decl name token scan) :
      (∀ c epoch, label ≠ .commit c epoch) →
      (∀ v, label = .enumerate v → ∀ c, th.recovery.ready v c = true →
        StorageReady th.base disk (th.recordObject c) (th.recovery.image c)) → RecoveryNext th.recovery rec label rec' →
      CoupledNext th ⟨rec, disk⟩ ⟨rec', disk⟩

/-- Complete physical scan. Candidate objects may be unacknowledged. No global
acknowledgment bit is read from their bytes. Adoption must re-acknowledge them. -/
def PhysicalScan
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (disk : ParaleanGroupComposition.DiskState replica obj writeQuorum readQuorum)
    (q : readQuorum) (v : scan) : Prop :=
  ∀ c, th.recovery.decoded v c = true ↔ QuorumCatalog th.base disk q (th.recordObject c)

theorem physical_scan_covers_committed
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (s : CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (ha : CoupledAssumptions th) (hs : CoupledSafe th s)
    (q : readQuorum) (hq : ∀ r, th.base.storage.memberR r q = true → s.storage.live r = true)
    (v : scan) (hscan : PhysicalScan th s.storage q v) :
    ∀ c, s.recovery.committed c = true → th.recovery.decoded v c = true := by
  intro c hc
  apply (hscan c).2
  have hk := hs.2.2.1 c hc
  have hw := ParaleanGroupComposition.acknowledged_recoverable th.base s.storage ha.1 hs.2.1
    (th.recordObject c) q hk hq
  have hm := ha.1 (s.storage.witness (th.recordObject c)) q
  exact ⟨_, hm.2, hw⟩

def ReadyScan
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (disk : ParaleanGroupComposition.DiskState replica obj writeQuorum readQuorum) (v : scan) : Prop :=
  ∀ c, th.recovery.ready v c = true ↔ StorageReady th.base disk (th.recordObject c) (th.recovery.image c)

theorem physical_scan_ready_for_committed
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (s : CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (ha : CoupledAssumptions th) (hs : CoupledSafe th s)
    (q : readQuorum) (hq : ∀ r, th.base.storage.memberR r q = true → s.storage.live r = true)
    (v : scan) (hscan : PhysicalScan th s.storage q v) (hready : ReadyScan th s.storage v) :
    ∀ c, s.recovery.committed c = true →
      th.recovery.decoded v c = true ∧ th.recovery.ready v c = true := by
  intro c hc
  refine ⟨physical_scan_covers_committed th s ha hs q hq v hscan c hc, (hready c).2 ?_⟩
  exact ⟨hs.2.2.1 c hc, hs.2.2.2 c hc⟩

theorem coupled_next_safe
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (ha : CoupledAssumptions th)
    (s s' : CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (hs : CoupledSafe th s) (ht : CoupledNext th s s') : CoupledSafe th s' := by
  cases ht with
  | @storage rec disk disk' label ht hg =>
    refine ⟨hs.1, Durability.Next_preserves _ _ replica obj writeQuorum readQuorum
      (ParaleanGroupComposition.DiskRep replica obj writeQuorum readQuorum)
      th.base.storage _ _ label ha.1 hs.2.1 ht, ?_⟩
    have hcouple := hs.2.2
    cases label <;> simp only [ParaleanGroupComposition.StorageNext, Durability.Next, Durability.NextAct,
      Durability.Put.ext.derived_eq, Durability.Ack.ext.derived_eq, Durability.Lose.ext.derived_eq] at ht
    all_goals
      dsimp [Durability.Put.ext.tr, Durability.Ack.ext.tr, Durability.Lose.ext.tr,
        getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
        instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanGroupComposition.diskFieldRep,
        Veil.canonicalFieldRepresentation] at ht
      repeat' rcases ht with ⟨hh, ht⟩
      simp [Coupled, StorageGuard, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
        Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
        Veil.IteratedProd.patCmp] at *
      grind (splits := 30)
  | @commit rec rec' disk disk' c epoch w ht hd hm hp =>
    refine ⟨Next_preserves _ _ record workspace snapshot decl name token scan
      (CanonicalRep record workspace snapshot decl name token scan)
      th.recovery _ _ (.commit c epoch) ha.2.1 hs.1 ht,
      Durability.Next_preserves _ _ replica obj writeQuorum readQuorum
      (ParaleanGroupComposition.DiskRep replica obj writeQuorum readQuorum)
      th.base.storage _ _ (.Ack (th.recordObject c) w) ha.1 hs.2.1 hd, ?_⟩
    have hcouple := hs.2.2
    simp only [RecoveryNext, Next, NextAct, commit.ext.derived_eq] at ht
    simp only [ParaleanGroupComposition.StorageNext, Durability.Next, Durability.NextAct,
      Durability.Ack.ext.derived_eq] at hd
    dsimp [commit.ext.tr, Durability.Ack.ext.tr, getFrom, setIn, readFrom,
      Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
      canonicalFieldRep, ParaleanGroupComposition.diskFieldRep, Veil.canonicalFieldRepresentation] at ht hd
    repeat' rcases ht with ⟨hh, ht⟩
    repeat' rcases hd with ⟨hh, hd⟩
    simp [Coupled, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp] at *
    grind (splits := 30)
  | @recovery rec rec' disk label hnot hready ht =>
    refine ⟨Next_preserves _ _ record workspace snapshot decl name token scan
      (CanonicalRep record workspace snapshot decl name token scan)
      th.recovery _ _ label ha.2.1 hs.1 ht, hs.2.1, ?_⟩
    have hcouple := hs.2.2
    cases label <;> simp only [RecoveryNext, Next, NextAct, commit.ext.derived_eq,
      loseDesktop.ext.derived_eq, rotateFence.ext.derived_eq, enumerate.ext.derived_eq,
      reconstruct.ext.derived_eq, automatic.ext.derived_eq, historical.ext.derived_eq] at ht
    case commit c epoch => exact False.elim (hnot c epoch rfl)
    all_goals
      dsimp [loseDesktop.ext.tr, rotateFence.ext.tr, enumerate.ext.tr, reconstruct.ext.tr,
        automatic.ext.tr, historical.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
        instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
        Veil.canonicalFieldRepresentation] at ht
      repeat' rcases ht with ⟨hh, ht⟩
      simp [Coupled, admissible, StorageReady, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
        Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
        Veil.IteratedProd.patCmp] at *
      grind (splits := 30)


def CoupledInit
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (s : CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum) : Prop :=
  RecoveryInit th.recovery s.recovery ∧ ParaleanGroupComposition.StorageInit th.base.storage s.storage

theorem coupled_initial_safe
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (ha : CoupledAssumptions th)
    (s : CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (hi : CoupledInit th s) : CoupledSafe th s := by
  refine ⟨Init_preserves _ _ record workspace snapshot decl name token scan
      (CanonicalRep record workspace snapshot decl name token scan) th.recovery _ ha.2.1 hi.1,
    Durability.Init_preserves _ _ replica obj writeQuorum readQuorum
      (ParaleanGroupComposition.DiskRep replica obj writeQuorum readQuorum)
      th.base.storage s.storage ha.1 hi.2, ?_⟩
  obtain ⟨rec, disk⟩ := s
  obtain ⟨hr, hd⟩ := hi
  dsimp [RecoveryInit, Init, initializer.ext.tr, ParaleanGroupComposition.StorageInit,
    Durability.Init, Durability.initializer.ext.tr, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    canonicalFieldRep, ParaleanGroupComposition.diskFieldRep, Veil.canonicalFieldRepresentation] at hr hd
  subst rec
  subst disk
  simp [Coupled, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

inductive CoupledReachable
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum) :
    CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum → Prop where
  | initial {s} : CoupledInit th s → CoupledReachable th s
  | step {s s'} : CoupledReachable th s → CoupledNext th s s' → CoupledReachable th s'

theorem coupled_reachable_safe
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (ha : CoupledAssumptions th)
    {s : CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum}
    (hr : CoupledReachable th s) : CoupledSafe th s := by
  induction hr with
  | initial hi => exact coupled_initial_safe th ha _ hi
  | step hr ht ih => exact coupled_next_safe th ha _ _ ih ht

/-- Every selected admitted record has actual acknowledged bytes. Unready staged
candidates are excluded by admissibility and do not block reconstruction. -/
theorem coupled_selected_has_copies
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (ha : CoupledAssumptions th)
    {s : CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum}
    (hr : CoupledReachable th s) (hsel : s.recovery.selected = true) :
    (∃ r, s.storage.live r = true ∧ s.storage.stored r (th.recordObject s.recovery.selectedRecord) = true) ∧
    (∃ r, s.storage.live r = true ∧
      s.storage.stored r (th.base.manifest (th.recovery.image s.recovery.selectedRecord)) = true) ∧
    ∀ d, th.base.registry.contents (th.recovery.image s.recovery.selectedRecord) d = true →
      ∃ r, s.storage.live r = true ∧ s.storage.stored r (th.base.payload d) = true := by
  have hs := coupled_reachable_safe th ha hr
  have hb := selected_record_backed th.recovery s.recovery hs.1 hsel
  have hc := hs.2.2.1 _ hb.1
  have hd := hs.2.2.2 _ hb.1
  refine ⟨ParaleanGroupComposition.acknowledged_has_copy th.base s.storage ha.1 hs.2.1 _ hc,
    ParaleanGroupComposition.acknowledged_has_copy th.base s.storage ha.1 hs.2.1 _ hd.1, ?_⟩
  intro d hd'
  exact ParaleanGroupComposition.acknowledged_has_copy th.base s.storage ha.1 hs.2.1 _ (hd.2 d hd')

theorem coupled_selected_buildable
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (ha : CoupledAssumptions th)
    {s : CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum}
    (hr : CoupledReachable th s) (hsel : s.recovery.selected = true)
    (rg : ParaleanGroups.CanonicalState node decl name snapshot) :
    ParaleanGroups.buildable (th.recovery.image s.recovery.selectedRecord) th.base.registry rg := by
  have hs := coupled_reachable_safe th ha hr
  have hb := (selected_record_backed th.recovery s.recovery hs.1 hsel).2.2.2
  obtain ⟨hv, hd, hn, hc, he⟩ := ha.2.2.1
  simpa [buildable, ParaleanGroups.buildable, hv, hd, hn, hc, he,
    readFrom, instIsSubReaderOfRefl] using hb

/-- Recovery adopts only physically decoded, ready, valid records and their valid
causal closure. It does not change the workspace's writer or fence authorization. -/
theorem physical_enumeration_enabled
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (s : CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (ha : CoupledAssumptions th) (hs : CoupledSafe th s)
    (q : readQuorum) (hq : ∀ r, th.base.storage.memberR r q = true → s.storage.live r = true)
    (v : scan) (hscan : PhysicalScan th s.storage q v) (hready : ReadyScan th s.storage v) :
    ∃ rec', CoupledNext th s ⟨rec', s.storage⟩ ∧ rec'.scanned = true ∧
      rec'.writer = s.recovery.writer ∧ rec'.fence = s.recovery.fence ∧
      (∀ c, rec'.known c = true ↔ admissible v c th.recovery s.recovery) := by
  classical
  let accepted := fun c => decide (admissible v c th.recovery s.recovery)
  let rec' : CanonicalState record workspace snapshot decl name token scan :=
    { (s.recovery) with
      known := accepted
      committed := fun c => s.recovery.committed c || accepted c
      durableAck := fun c => s.recovery.durableAck c || accepted c
      heads := fun _ => false
      scanned := true
      reconstructed := false
      conflict := false
      selected := false }
  refine ⟨rec', ?_, rfl, rfl, rfl, ?_⟩
  · apply CoupledNext.recovery (.enumerate v)
    · intro c epoch h
      cases h
    · intro v' hv c hc
      cases hv
      exact (hready c).1 hc
    · have hc := physical_scan_ready_for_committed th s ha hs q hq v hscan hready
      simp only [RecoveryNext, Next, NextAct, enumerate.ext.derived_eq]
      dsimp [enumerate.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
        instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
        Veil.canonicalFieldRepresentation]
      refine ⟨hc, ?_⟩
      simp [rec', accepted, admissible, buildable, readFrom, instIsSubReaderOfRefl,
        Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
        Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
        Veil.IteratedProd.patCmp]
  · intro c
    simp [rec', accepted]

end Coupling
#print axioms physical_enumeration_enabled
#print axioms coupled_selected_buildable
#print axioms physical_scan_ready_for_committed
#print axioms physical_scan_covers_committed
#print axioms coupled_next_safe
#print axioms coupled_initial_safe
#print axioms coupled_reachable_safe
#print axioms coupled_selected_has_copies
end ParaleanRecovery

namespace ParaleanRecovery
noncomputable section CoupledExecution
open ParaleanArtifacts
private abbrev ExecutionObject := Object Unit Bool
private abbrev ExecutionDisk := ParaleanGroupComposition.DiskState Bool ExecutionObject Unit Unit
private abbrev ExecutionState := CoupledState Bool Unit Bool Unit Unit Bool Unit Bool ExecutionObject Unit Unit

private def executionStorageTheory : Durability.Theory Bool ExecutionObject Unit Unit where
  memberW := fun _ _ => true
  memberR := fun r _ => r
  meet := fun _ _ => true
private def executionGroupTheory : ParaleanGroups.Theory Unit Unit Unit Bool where
  valid := fun _ => true
  deps := fun _ _ => false
  ancestors := fun _ _ => false
  member := fun _ _ => true
  revisions := fun _ _ _ => false
  contents := fun S _ => S
  exportable := fun _ => true
  emptySnapshot := false
private def executionBase : ParaleanGroupComposition.Theory Unit Unit Unit Bool Bool ExecutionObject Unit Unit where
  registry := executionGroupTheory
  storage := executionStorageTheory
  payload := Object.payload
  manifest := Object.manifest
private def executionCoupledTheory : CoupledTheory Unit Bool Unit Bool Unit Unit Bool Unit Bool ExecutionObject Unit Unit where
  base := executionBase
  recovery := executionTheory
  recordObject := fun c => Object.catalog (if c then 1 else 0)

private def executionDiskInitial : ExecutionDisk :=
  ⟨fun _ _ => false, fun _ => true, fun _ => false, fun _ => ()⟩
private def executionPut (disk : ExecutionDisk) (r : Bool) (o : ExecutionObject) : ExecutionDisk :=
  { disk with stored := fun n p => if r = n ∧ o = p then true else disk.stored n p }
private def executionAck (disk : ExecutionDisk) (o : ExecutionObject) : ExecutionDisk :=
  { disk with
    acknowledged := fun p => if o = p then true else disk.acknowledged p
    witness := fun _ => () }
private def executionDisk1 := executionPut executionDiskInitial false (.payload ())
private def executionDisk2 := executionPut executionDisk1 true (.payload ())
private def executionDisk3 := executionAck executionDisk2 (.payload ())
private def executionDisk4 := executionPut executionDisk3 false (.manifest true)
private def executionDisk5 := executionPut executionDisk4 true (.manifest true)
private def executionDisk6 := executionAck executionDisk5 (.manifest true)
private def executionDisk7 := executionPut executionDisk6 false (.catalog 1)
private def executionDisk8 := executionPut executionDisk7 true (.catalog 1)
private def executionDisk9 := executionAck executionDisk8 (.catalog 1)
private def executionDisk10 := executionPut executionDisk9 true (.catalog 0)
private def executionDiskLost : ExecutionDisk :=
  { executionDisk10 with
    live := fun r => r
    stored := fun r o => if r then executionDisk10.stored r o else false }

private theorem execution_put_step (disk : ExecutionDisk) (r : Bool) (o : ExecutionObject)
    (hl : disk.live r = true) :
    ParaleanGroupComposition.StorageNext executionStorageTheory disk (.Put r o) (executionPut disk r o) := by
  simp only [ParaleanGroupComposition.StorageNext, Durability.Next, Durability.NextAct,
    Durability.Put.ext.derived_eq]
  dsimp [Durability.Put.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanGroupComposition.diskFieldRep,
    Veil.canonicalFieldRepresentation]
  refine ⟨hl, ?_⟩
  simp [executionPut, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp, funext_iff]

private theorem execution_ack_step (disk : ExecutionDisk) (o : ExecutionObject)
    (hq : ∀ r, disk.live r = true ∧ disk.stored r o = true) :
    ParaleanGroupComposition.StorageNext executionStorageTheory disk (.Ack o ()) (executionAck disk o) := by
  classical
  simp only [ParaleanGroupComposition.StorageNext, Durability.Next, Durability.NextAct,
    Durability.Ack.ext.derived_eq]
  dsimp [Durability.Ack.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanGroupComposition.diskFieldRep,
    Veil.canonicalFieldRepresentation]
  refine ⟨fun r _ => hq r, ?_⟩
  simp [executionAck, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp, funext_iff]

private theorem execution_lose_step :
    ParaleanGroupComposition.StorageNext executionStorageTheory executionDisk10 (.Lose false) executionDiskLost := by
  classical
  simp only [ParaleanGroupComposition.StorageNext, Durability.Next, Durability.NextAct,
    Durability.Lose.ext.derived_eq]
  dsimp [Durability.Lose.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanGroupComposition.diskFieldRep,
    Veil.canonicalFieldRepresentation]
  simp [executionStorageTheory, executionDiskLost, executionDisk10, executionDisk9,
    executionDisk8, executionDisk7, executionDisk6, executionDisk5, executionDisk4,
    executionDisk3, executionDisk2, executionDisk1, executionDiskInitial,
    executionPut, executionAck, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]

private theorem execution_coupled_assumptions : CoupledAssumptions executionCoupledTheory := by
  constructor
  · simp [ParaleanGroupComposition.StorageAssumptions, Durability.Assumptions,
      Durability.assumption_0, executionCoupledTheory, executionBase, executionStorageTheory,
      readFrom, instIsSubReaderOfRefl]
  constructor
  · exact nonempty_lose_id_execution.1
  constructor
  · simp [Compatible, executionCoupledTheory, executionBase, executionGroupTheory, executionTheory]
  · simp only [ObjectsSeparate, executionCoupledTheory, executionBase]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b h
      cases a <;> cases b <;> simp_all
    · intro c S h
      cases c <;> cases h
    · intro c d h
      cases c <;> cases h
    · intro S d h
      cases h

private theorem execution_physical_scan :
    PhysicalScan executionCoupledTheory executionDiskLost () () ∧
      ReadyScan executionCoupledTheory executionDiskLost () := by
  constructor <;> intro c <;> cases c <;>
    simp [PhysicalScan, ReadyScan, QuorumCatalog, StorageReady, executionCoupledTheory,
      executionBase, executionStorageTheory, executionTheory, executionGroupTheory,
      executionDiskLost, executionDisk10, executionDisk9, executionDisk8, executionDisk7,
      executionDisk6, executionDisk5, executionDisk4, executionDisk3, executionDisk2,
      executionDisk1, executionDiskInitial, executionPut, executionAck,
      Bool.exists_bool, Bool.forall_bool]

/-- A complete generated storage/protocol execution. It writes and acknowledges
real typed payload/manifest/catalog objects, commits, stages an unready candidate,
loses a replica and the desktop's ID, scans the surviving quorum, and recovers a
nonempty exact snapshot. The staged candidate does not poison recovery. -/
theorem coupled_nonempty_lose_id_execution :
    CoupledAssumptions executionCoupledTheory ∧
    CoupledReachable executionCoupledTheory ⟨executionRecovered, executionDiskLost⟩ ∧
    PhysicalScan executionCoupledTheory executionDiskLost () () ∧
    ReadyScan executionCoupledTheory executionDiskLost () ∧
    executionLost.selectedRecord = false ∧ (∀ c, executionLost.known c = false) ∧
    executionRecovered.selected = true ∧ executionRecovered.selectedRecord = true ∧
    executionRecovered.writer = false ∧ executionRecovered.fence = 0 ∧
    executionTheory.decoded () false = true ∧ executionTheory.ready () false = false ∧
    executionRecovered.known false = false ∧
    executionTheory.contents (executionTheory.image executionRecovered.selectedRecord) () = true := by
  rcases nonempty_lose_id_execution with
    ⟨ha, hi, hc, he, hr, hs, hl, hbefore, hafter, hclear, he', hr', hs', hselected, hcontents⟩
  have h0 : CoupledReachable executionCoupledTheory ⟨executionInitial, executionDiskInitial⟩ := by
    apply CoupledReachable.initial
    refine ⟨hi, ?_⟩
    simp [ParaleanGroupComposition.StorageInit, Durability.Init, Durability.initializer.ext.tr,
      executionDiskInitial, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
      instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanGroupComposition.diskFieldRep,
      Veil.canonicalFieldRepresentation, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp]
  have h1 := CoupledReachable.step h0 (CoupledNext.storage (.Put false (.payload ()))
    (execution_put_step _ _ _ rfl) trivial)
  have h2 := CoupledReachable.step h1 (CoupledNext.storage (.Put true (.payload ()))
    (execution_put_step _ _ _ rfl) trivial)
  have h3 := CoupledReachable.step h2 (CoupledNext.storage (.Ack (.payload ()) ())
    (execution_ack_step _ _ (by
      intro r
      cases r <;> simp [executionDisk2, executionDisk1, executionDiskInitial, executionPut])) trivial)
  have h4 := CoupledReachable.step h3 (CoupledNext.storage (.Put false (.manifest true))
    (execution_put_step _ _ _ rfl) trivial)
  have h5 := CoupledReachable.step h4 (CoupledNext.storage (.Put true (.manifest true))
    (execution_put_step _ _ _ rfl) trivial)
  have h6 := CoupledReachable.step h5 (CoupledNext.storage (.Ack (.manifest true) ())
    (execution_ack_step _ _ (by
      intro r
      cases r <;> simp [executionDisk5, executionDisk4, executionDisk3, executionDisk2,
        executionDisk1, executionDiskInitial, executionPut, executionAck])) trivial)
  have h7 := CoupledReachable.step h6 (CoupledNext.storage (.Put false (.catalog 1))
    (execution_put_step _ _ _ rfl) trivial)
  have h8 := CoupledReachable.step h7 (CoupledNext.storage (.Put true (.catalog 1))
    (execution_put_step _ _ _ rfl) trivial)
  have h9 := CoupledReachable.step h8 (CoupledNext.commit true false () hc
    (execution_ack_step _ _ (by
      intro r
      cases r <;> simp [executionCoupledTheory, executionDisk8, executionDisk7, executionDisk6, executionDisk5,
        executionDisk4, executionDisk3, executionDisk2, executionDisk1, executionDiskInitial,
        executionPut, executionAck]))
    (by simp [executionCoupledTheory, executionBase, executionDisk8, executionDisk7,
      executionDisk6, executionDisk5, executionDisk4, executionDisk3, executionDisk2,
      executionDisk1, executionDiskInitial, executionPut, executionAck, executionTheory])
    (by intro d hd
        simp [executionCoupledTheory, executionBase, executionDisk8, executionDisk7,
          executionDisk6, executionDisk5, executionDisk4, executionDisk3, executionDisk2,
          executionDisk1, executionDiskInitial, executionPut, executionAck]))
  have h10 := CoupledReachable.step h9 (CoupledNext.storage (.Put true (.catalog 0))
    (execution_put_step _ _ _ rfl) trivial)
  have h11 := CoupledReachable.step h10 (CoupledNext.storage (.Lose false) execution_lose_step trivial)
  have h12 := CoupledReachable.step h11 (CoupledNext.recovery (.enumerate ())
    (by intro c epoch h; cases h)
    (by intro v hv c hready
        cases hv
        exact (execution_physical_scan.2 c).1 hready) he)
  have h13 := CoupledReachable.step h12 (CoupledNext.recovery .reconstruct
    (by intro c epoch h; cases h) (by intro v h; cases h) hr)
  have h14 := CoupledReachable.step h13 (CoupledNext.recovery (.automatic true)
    (by intro c epoch h; cases h) (by intro v h; cases h) hs)
  have h15 := CoupledReachable.step h14 (CoupledNext.recovery .loseDesktop
    (by intro c epoch h; cases h) (by intro v h; cases h) hl)
  have h16 := CoupledReachable.step h15 (CoupledNext.recovery (.enumerate ())
    (by intro c epoch h; cases h)
    (by intro v hv c hready
        cases hv
        exact (execution_physical_scan.2 c).1 hready) he')
  have h17 := CoupledReachable.step h16 (CoupledNext.recovery .reconstruct
    (by intro c epoch h; cases h) (by intro v h; cases h) hr')
  have h18 := CoupledReachable.step h17 (CoupledNext.recovery (.automatic true)
    (by intro c epoch h; cases h) (by intro v h; cases h) hs')
  refine ⟨execution_coupled_assumptions, h18, execution_physical_scan.1,
    execution_physical_scan.2, hafter, hclear, hselected, rfl, rfl, rfl, rfl, rfl, rfl, hcontents⟩

end CoupledExecution
#print axioms coupled_nonempty_lose_id_execution
end ParaleanRecovery

namespace ParaleanRecovery

/-- The recovery store uses the actual typed maps of the receipt/admission protocol. -/
def ofAdmission
    (th : ParaleanAdmission.Theory node decl name snapshot request packet replica writeQuorum readQuorum)
    (rc : Theory record workspace snapshot decl name token scan) (recordId : record → Nat) :
    CoupledTheory node record workspace snapshot decl name token scan replica
      (ParaleanArtifacts.Object decl snapshot) writeQuorum readQuorum where
  base := ParaleanAdmission.protocolTheory th
  recovery := rc
  recordObject := fun c => ParaleanArtifacts.Object.catalog (recordId c)

noncomputable section AdmissionAdapter
variable {node record workspace snapshot decl name token scan request packet replica writeQuorum readQuorum : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq record] [Inhabited record]
  [DecidableEq workspace] [Inhabited workspace] [DecidableEq snapshot] [Inhabited snapshot]
  [DecidableEq decl] [Inhabited decl] [DecidableEq name] [Inhabited name]
  [DecidableEq token] [Inhabited token] [DecidableEq scan] [Inhabited scan]
  [DecidableEq replica] [Inhabited replica]
  [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum]

/-- Injective encoded catalog IDs provide role separation by construction. -/
theorem ofAdmission_objects_separate
    (th : ParaleanAdmission.Theory node decl name snapshot request packet replica writeQuorum readQuorum)
    (rc : Theory record workspace snapshot decl name token scan)
    (recordId : record → Nat) (hinj : Function.Injective recordId) :
    ObjectsSeparate (ofAdmission th rc recordId) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h
    exact hinj (ParaleanArtifacts.catalog_injective h)
  · intro c S
    exact ParaleanArtifacts.catalog_manifest_disjoint _ _
  · intro c d
    exact ParaleanArtifacts.catalog_payload_disjoint _ _
  · intro S d h
    cases h

end AdmissionAdapter
#print axioms ofAdmission_objects_separate
end ParaleanRecovery
