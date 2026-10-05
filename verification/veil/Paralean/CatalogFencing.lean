import Paralean.Protocol
import Paralean.CompletionRecoveryExecution

/-! Store-side fencing of catalogue writes. A step that newly stores or
acknowledges a record's catalogue object must either pass the store's
conditional check (the record's embedded token rank equals the fence held in
the store) or be a copy of bytes the writer read from a named live replica (a
repair, or the acknowledgement of bytes already on a write quorum). The guard
reads only the fence register, the record's token, the store delta and one
positive read of a live replica; it never asks whether *no* replica holds the
bytes. Every first write (no replica held the bytes) is therefore fenced
(`firstWrite_fenced`). Commit keeps only its base epoch check. A ghost map
remembers the fence at each record's first write, so every stored, acknowledged
or committed record was first written while its token was the current fence. -/
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ParaleanCatalogFencing
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

/-- Ghost history: the fence value at the first physical write of each record's
catalogue object. -/
abbrev Extra (record : Type) := record → Option Nat

/-- Catalogue bytes of `c` are on some replica or acknowledged. -/
def Present (encode : record → Nat) (s : ModelState) (c : record) : Prop :=
  (∃ x, s.admission.protocol.storage.stored x (.catalog (encode c)) = true) ∨
    s.admission.protocol.storage.acknowledged (.catalog (encode c)) = true

/-- The step newly stores `c`'s catalogue object on a replica, or newly acknowledges it. -/
def NewWrite (encode : record → Nat) (s t : ModelState) (c : record) : Prop :=
  (∃ x, t.admission.protocol.storage.stored x (.catalog (encode c)) = true ∧
      s.admission.protocol.storage.stored x (.catalog (encode c)) = false) ∨
    (t.admission.protocol.storage.acknowledged (.catalog (encode c)) = true ∧
      s.admission.protocol.storage.acknowledged (.catalog (encode c)) = false)

/-- Some replica holds `c`'s catalogue bytes. Used only to state results; no
guard evaluates it. -/
def StoredSomewhere (encode : record → Nat) (s : ModelState) (c : record) : Prop :=
  ∃ x, s.admission.protocol.storage.stored x (.catalog (encode c)) = true

/-- First write of `c`: the step newly stores or acknowledges `c`'s object while no
replica held its bytes before the step. A new copy of bytes some replica already
holds is a repair, not a first write. A specification notion only: the guard
below never decides it. -/
def FirstWrite (encode : record → Nat) (s t : ModelState) (c : record) : Prop :=
  NewWrite encode s t c ∧ ¬ StoredSomewhere encode s c

/-- Observable repair source: the writer read `c`'s catalogue bytes from replica
`x`, which answered, so `x` is live and holds them. A positive read; it does not
quantify over replicas that did not answer. -/
def CopySource (encode : record → Nat) (s : ModelState) (c : record) : Prop :=
  ∃ x, s.admission.protocol.storage.live x = true ∧
    s.admission.protocol.storage.stored x (.catalog (encode c)) = true

/-- Conditional-write check: the record's embedded token has the rank of the fence
held in the store before the step. Ranks are compared; distinct tokens of equal
rank are excluded by the ownership-service contract, not by this check. -/
def Fenced (r : RTheory) (recordToken : record → token) (s : ModelState) (c : record) : Prop :=
  r.tokenRank (recordToken c) = s.recovery.fence

/-- Record the pre-step fence at a record's first physical write. -/
def update (encode : record → Nat) (s t : ModelState) (e : Extra record) : Extra record :=
  fun c => if e c = none ∧ NewWrite encode s t c then some s.recovery.fence else e c

/-- Every new store or acknowledgement of a record's catalogue object either passes
the conditional fence check or copies bytes read from a live replica (repair; an
Ack of bytes already on a write quorum). Commit keeps its base
`tokenRank epoch = fence` check. -/
def Guard (a : ATheory) (r : RTheory) (encode : record → Nat) (recordToken : record → token)
    (s : ModelState) (e : Extra record) (t : ModelState) (e' : Extra record) : Prop :=
  (∀ c, NewWrite encode s t c → Fenced r recordToken s c ∨ CopySource encode s c) ∧
  e' = update encode s t e

def Next (a : ATheory) (r : RTheory) (encode : record → Nat) (recordToken : record → token)
    (p q : ModelState × Extra record) : Prop :=
  ParaleanProtocol.Next a r encode p.1 q.1 ∧ Guard a r encode recordToken p.1 p.2 q.1 q.2

def Initial (a : ATheory) (r : RTheory) (p : ModelState × Extra record) : Prop :=
  ParaleanCompletionRecovery.Initial a r p.1 ∧ p.2 = fun _ => none

inductive Reachable (a : ATheory) (r : RTheory) (encode : record → Nat) (recordToken : record → token) :
    ModelState × Extra record → Prop where
  | initial {p} : Initial a r p → Reachable a r encode recordToken p
  | step {p q} : Reachable a r encode recordToken p → Next a r encode recordToken p q →
      Reachable a r encode recordToken q

theorem guard_stutter (a : ATheory) (r : RTheory) (encode : record → Nat) (recordToken : record → token)
    (s : ModelState) (e : Extra record) : Guard a r encode recordToken s e s e := by
  refine ⟨?_, ?_⟩
  · rintro c (⟨x, h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
  · funext c; simp [update, NewWrite]

theorem copySource_stored (encode : record → Nat) {s : ModelState} {c : record}
    (h : CopySource encode s c) : StoredSomewhere encode s c := by
  obtain ⟨x, _, hx⟩ := h
  exact ⟨x, hx⟩

/-- The guard fences every first write: a first write has no source replica to
copy from, so it must pass the fence check. -/
theorem firstWrite_fenced (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : record → token) {s t : ModelState} {e e' : Extra record}
    (hg : Guard a r encode recordToken s e t e') (c : record) (hf : FirstWrite encode s t c) :
    Fenced r recordToken s c :=
  (hg.1 c hf.1).resolve_right (fun h => hf.2 (copySource_stored encode h))

theorem reachable_protocol (a : ATheory) (r : RTheory) (encode : record → Nat) (recordToken : record → token)
    {p} (h : Reachable a r encode recordToken p) : ParaleanProtocol.Reachable a r encode p.1 := by
  induction h with
  | initial hi => exact .initial hi.1
  | step _ ht ih => exact .step ih ht.1

/-! Fence monotonicity of every base transition. -/

theorem recovery_fence_mono (r : RTheory)
    {rec rec' : ParaleanRecovery.CanonicalState record workspace snapshot group name token scan}
    (label : ParaleanRecovery.Label record workspace snapshot group name token scan)
    (ht : ParaleanRecovery.RecoveryNext r rec label rec') : rec.fence ≤ rec'.fence := by
  cases label <;> simp only [ParaleanRecovery.RecoveryNext, ParaleanRecovery.Next, ParaleanRecovery.NextAct,
    ParaleanRecovery.commit.ext.derived_eq, ParaleanRecovery.loseDesktop.ext.derived_eq,
    ParaleanRecovery.rotateFence.ext.derived_eq, ParaleanRecovery.enumerate.ext.derived_eq,
    ParaleanRecovery.reconstruct.ext.derived_eq, ParaleanRecovery.automatic.ext.derived_eq,
    ParaleanRecovery.historical.ext.derived_eq] at ht
  all_goals
    dsimp [ParaleanRecovery.commit.ext.tr, ParaleanRecovery.loseDesktop.ext.tr,
      ParaleanRecovery.rotateFence.ext.tr, ParaleanRecovery.enumerate.ext.tr,
      ParaleanRecovery.reconstruct.ext.tr, ParaleanRecovery.automatic.ext.tr,
      ParaleanRecovery.historical.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
      instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanRecovery.canonicalFieldRep,
      Veil.canonicalFieldRepresentation] at ht
    repeat' rcases ht with ⟨hh, ht⟩
    subst_vars
    simp_all [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp]
  all_goals exact Nat.le_of_lt hh

theorem coupled_fence_mono {node : Type} [DecidableEq node] [Inhabited node] {obj : Type}
    [DecidableEq obj] [Inhabited obj]
    (th : ParaleanRecovery.CoupledTheory node record workspace snapshot group name token scan replica obj writeQuorum readQuorum)
    {v v'} (ht : ParaleanRecovery.CoupledNext th v v') : v.recovery.fence ≤ v'.recovery.fence := by
  cases ht with
  | storage _ _ _ => exact Nat.le_refl _
  | commit c epoch w hr _ _ _ => exact recovery_fence_mono _ _ hr
  | recovery l _ _ hr => exact recovery_fence_mono _ _ hr

theorem fence_mono (a : ATheory) (r : RTheory) (encode : record → Nat)
    {s t : ModelState} (ht : ParaleanProtocol.Next a r encode s t) :
    s.recovery.fence ≤ t.recovery.fence := by
  cases ht with
  | paired hc _ =>
    cases hc with
    | admission _ _ => exact Nat.le_refl _
    | coupled _ _ _ hcn => exact coupled_fence_mono _ hcn
    | finish n S c hf => cases hf; exact Nat.le_refl _
  | publish => exact Nat.le_refl _

theorem initial_storage_empty (a : ATheory) (r : RTheory) {s : ModelState}
    (hi : ParaleanCompletionRecovery.Initial a r s) :
    (∀ x o, s.admission.protocol.storage.stored x o = false) ∧
      ∀ o, s.admission.protocol.storage.acknowledged o = false := by
  have hd := hi.1.2.2
  obtain ⟨ad, rec⟩ := s
  obtain ⟨dl, rg, disk⟩ := ad
  dsimp [ParaleanGroupComposition.StorageInit, Durability.Init, Durability.initializer.ext.tr,
    getFrom, setIn, readFrom, Veil.FieldRepresentation.get, instIsSubStateOfRefl,
    instIsSubReaderOfRefl, ParaleanGroupComposition.diskFieldRep,
    Veil.canonicalFieldRepresentation] at hd
  subst disk
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]


/-! Inductive ghost invariant and the safety properties. -/

def Inv (r : RTheory) (encode : record → Nat) (recordToken : record → token)
    (p : ModelState × Extra record) : Prop :=
  (∀ c k, p.2 c = some k → k = r.tokenRank (recordToken c) ∧ k ≤ p.1.recovery.fence) ∧
  (∀ c, Present encode p.1 c → p.2 c ≠ none)

theorem initial_inv (a : ATheory) (r : RTheory) (encode : record → Nat) (recordToken : record → token)
    {p : ModelState × Extra record} (hi : Initial a r p) : Inv r encode recordToken p := by
  obtain ⟨hst, hack⟩ := initial_storage_empty a r hi.1
  refine ⟨?_, ?_⟩
  · intro c k h
    rw [hi.2] at h
    cases h
  · rintro c (⟨x, hx⟩ | hx) <;> simp_all

theorem next_inv (a : ATheory) (r : RTheory) (encode : record → Nat) (recordToken : record → token)
    {p q : ModelState × Extra record} (hp : Inv r encode recordToken p)
    (ht : Next a r encode recordToken p q) : Inv r encode recordToken q := by
  obtain ⟨s, e⟩ := p
  obtain ⟨t, e'⟩ := q
  obtain ⟨hb, hw, he⟩ := ht
  dsimp only at hb hw he hp ⊢
  have hmono := fence_mono a r encode hb
  subst he
  refine ⟨?_, ?_⟩
  · intro c k hk
    simp only [update] at hk
    by_cases hc : e c = none ∧ NewWrite encode s t c
    · rw [if_pos hc] at hk
      cases hk
      have hns : ¬ StoredSomewhere encode s c := fun hs => hp.2 c (Or.inl hs) hc.1
      have hf := (hw c hc.2).resolve_right (fun h => hns (copySource_stored encode h))
      exact ⟨hf.symm, hmono⟩
    · rw [if_neg hc] at hk
      obtain ⟨h1, h2⟩ := hp.1 c k hk
      exact ⟨h1, Nat.le_trans h2 hmono⟩
  · intro c hpres
    simp only [update]
    by_cases hs : Present encode s c
    · have hn := hp.2 c hs
      rw [if_neg (fun h => hn h.1)]
      exact hn
    · have hnew : NewWrite encode s t c := by
        simp only [Present, not_or, not_exists, Bool.not_eq_true] at hs
        rcases hpres with ⟨x, hx⟩ | hx
        · exact Or.inl ⟨x, hx, hs.1 x⟩
        · exact Or.inr ⟨hx, hs.2⟩
      by_cases hnone : e c = none
      · rw [if_pos ⟨hnone, hnew⟩]
        simp
      · rw [if_neg (fun h => hnone h.1)]
        exact hnone

theorem reachable_inv (a : ATheory) (r : RTheory) (encode : record → Nat) (recordToken : record → token)
    {p} (h : Reachable a r encode recordToken p) : Inv r encode recordToken p := by
  induction h with
  | initial hi => exact initial_inv a r encode recordToken hi
  | step _ ht ih => exact next_inv a r encode recordToken ih ht

/-- Every record whose catalogue bytes are on some replica, or that is
acknowledged, was first written while its token was the store's fence, and that
token does not exceed the current fence. Later copies or acknowledgements may
happen under any fence. No storage assumptions needed. -/
theorem present_fenced (a : ATheory) (r : RTheory) (encode : record → Nat) (recordToken : record → token)
    {p} (h : Reachable a r encode recordToken p) (c : record) (hc : Present encode p.1 c) :
    p.2 c = some (r.tokenRank (recordToken c)) ∧ r.tokenRank (recordToken c) ≤ p.1.recovery.fence := by
  have hi := reachable_inv a r encode recordToken h
  have hn := hi.2 c hc
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 hn
  obtain ⟨h1, h2⟩ := hi.1 c k hk
  subst h1
  exact ⟨hk, h2⟩

/-- Guard restatement (definitional): a step that first-writes a record whose
token rank differs from the pre-step fence is not a hardened step. -/
theorem stale_first_write_rejected (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : record → token) (s : ModelState) (e : Extra record) (c : record)
    (hstale : r.tokenRank (recordToken c) ≠ s.recovery.fence) :
    ¬ ∃ t e', Next a r encode recordToken (s, e) (t, e') ∧ FirstWrite encode s t c := by
  rintro ⟨t, e', ⟨_, hg⟩, hn⟩
  exact hstale (firstWrite_fenced a r encode recordToken hg c hn)

/-- Every catalogue object on a replica or acknowledged, and every committed
record (including records adopted by `enumerate`), was first written while its
token was the current fence, and that token does not exceed the current fence. -/
theorem catalog_objects_fenced (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : record → token)
    (ha : ParaleanAdmission.Assumptions a)
    (hra : ParaleanRecovery.CoupledAssumptions (ParaleanRecovery.ofAdmission a r encode))
    {p} (h : Reachable a r encode recordToken p) :
    (∀ c, Present encode p.1 c →
      p.2 c = some (r.tokenRank (recordToken c)) ∧ r.tokenRank (recordToken c) ≤ p.1.recovery.fence) ∧
    (∀ c, p.1.recovery.committed c = true →
      p.2 c = some (r.tokenRank (recordToken c)) ∧ r.tokenRank (recordToken c) ≤ p.1.recovery.fence) := by
  refine ⟨present_fenced a r encode recordToken h, ?_⟩
  intro c hc
  have hs := (ParaleanProtocol.reachable_safe a r encode ha hra (reachable_protocol a r encode recordToken h)).1
  have hack : p.1.admission.protocol.storage.acknowledged (.catalog (encode c)) = true := hs.2.2.2.1 c hc
  exact present_fenced a r encode recordToken h c (Or.inr hack)

/-- The selected record (automatic or historical) was first written while its
token was the current fence. It may have been copied or acknowledged later. -/
theorem selected_not_stale (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : record → token)
    (ha : ParaleanAdmission.Assumptions a)
    (hra : ParaleanRecovery.CoupledAssumptions (ParaleanRecovery.ofAdmission a r encode))
    {p} (h : Reachable a r encode recordToken p) (hsel : p.1.recovery.selected = true) :
    p.2 p.1.recovery.selectedRecord = some (r.tokenRank (recordToken p.1.recovery.selectedRecord)) ∧
      r.tokenRank (recordToken p.1.recovery.selectedRecord) ≤ p.1.recovery.fence := by
  have hs := (ParaleanProtocol.reachable_safe a r encode ha hra (reachable_protocol a r encode recordToken h)).1
  have hb := ParaleanRecovery.selected_record_backed r p.1.recovery hs.2.1 hsel
  exact (catalog_objects_fenced a r encode recordToken ha hra h).2 _ hb.1

/-- The catalogue record certifying a completion was first written under a then-current token. -/
theorem completion_not_stale (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : record → token)
    (ha : ParaleanAdmission.Assumptions a)
    (hra : ParaleanRecovery.CoupledAssumptions (ParaleanRecovery.ofAdmission a r encode))
    {s t : ModelState} {e : Extra record} (h : Reachable a r encode recordToken (s, e))
    (n : node) (S : snapshot) (c : record)
    (hf : ParaleanCompletionRecovery.FinishStep a r n S c s t) :
    e c = some (r.tokenRank (recordToken c)) ∧ r.tokenRank (recordToken c) ≤ s.recovery.fence ∧
      r.image c = S := by
  cases hf with
  | guarded _ hc hi _ =>
    exact ⟨((catalog_objects_fenced a r encode recordToken ha hra h).2 c hc).1,
      ((catalog_objects_fenced a r encode recordToken ha hra h).2 c hc).2, hi⟩

/-! Implementability: the guard reads only the pre-step fence (modelled as the
store's fence register `recovery.fence`), the token embedded in the written
record, the store delta of the step, and, for an unfenced copy, one live replica
from which the writer read the bytes. It never decides that no replica holds the
bytes. It does not read the recovery component's `writer` flag. The ghost map is
only written. -/

theorem guard_enabled_iff (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : record → token) (s t : ModelState) (e : Extra record) :
    (∃ e', Guard a r encode recordToken s e t e') ↔
      ∀ c, NewWrite encode s t c → Fenced r recordToken s c ∨ CopySource encode s c := by
  constructor
  · rintro ⟨e', hw, _⟩
    exact hw
  · intro hw
    exact ⟨_, hw, rfl⟩

theorem hardened_step (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : record → token) {s t : ModelState} (e : Extra record)
    (hb : ParaleanProtocol.Next a r encode s t)
    (hw : ∀ c, NewWrite encode s t c → Fenced r recordToken s c ∨ CopySource encode s c) :
    Next a r encode recordToken (s, e) (t, update encode s t e) :=
  ⟨hb, hw, rfl⟩

/-- Convenience: a step whose every new write is fenced satisfies the guard. -/
theorem guard_of_fenced_writes (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : record → token) {s t : ModelState} (e : Extra record)
    (hw : ∀ c, NewWrite encode s t c → Fenced r recordToken s c) :
    Guard a r encode recordToken s e t (update encode s t e) :=
  ⟨fun c hn => Or.inl (hw c hn), rfl⟩

/-- A base step that only copies or acknowledges bytes read from a live replica
is a hardened step at any fence. -/
theorem no_first_write_step (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : record → token) {s t : ModelState} (e : Extra record)
    (hb : ParaleanProtocol.Next a r encode s t)
    (hold : ∀ c, NewWrite encode s t c → CopySource encode s c) :
    Next a r encode recordToken (s, e) (t, update encode s t e) :=
  hardened_step a r encode recordToken e hb (fun c hn => Or.inr (hold c hn))

theorem put_effect {obj : Type} [DecidableEq obj] [Inhabited obj]
    (th : Durability.Theory replica obj writeQuorum readQuorum)
    {disk disk' : ParaleanGroupComposition.DiskState replica obj writeQuorum readQuorum}
    (x : replica) (o : obj) (hd : ParaleanGroupComposition.StorageNext th disk (.Put x o) disk') :
    (∀ y o', disk'.stored y o' = true → disk.stored y o' = false → y = x ∧ o' = o) ∧
      disk'.acknowledged = disk.acknowledged := by
  simp only [ParaleanGroupComposition.StorageNext, Durability.Next, Durability.NextAct,
    Durability.Put.ext.derived_eq] at hd
  dsimp [Durability.Put.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanGroupComposition.diskFieldRep,
    Veil.canonicalFieldRepresentation] at hd
  obtain ⟨_, hd⟩ := hd
  subst hd
  refine ⟨?_, rfl⟩
  intro y o' h1 h2
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp] at h1
  by_contra hne
  simp_all

theorem ack_effect {obj : Type} [DecidableEq obj] [Inhabited obj]
    (th : Durability.Theory replica obj writeQuorum readQuorum)
    {disk disk' : ParaleanGroupComposition.DiskState replica obj writeQuorum readQuorum}
    (o : obj) (w : writeQuorum) (hd : ParaleanGroupComposition.StorageNext th disk (.Ack o w) disk') :
    disk'.stored = disk.stored ∧
      ∀ o', disk'.acknowledged o' = true → disk.acknowledged o' = false → o' = o := by
  simp only [ParaleanGroupComposition.StorageNext, Durability.Next, Durability.NextAct,
    Durability.Ack.ext.derived_eq] at hd
  dsimp [Durability.Ack.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanGroupComposition.diskFieldRep,
    Veil.canonicalFieldRepresentation] at hd
  obtain ⟨_, hd⟩ := hd
  subst hd
  refine ⟨rfl, ?_⟩
  intro o' h1 h2
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp] at h1
  by_contra hne
  simp_all

/-- The conditional first write is enabled when the record's token has the fence's
rank: a physical write of the record's catalogue object is a hardened step. -/
theorem fenced_put_enabled (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : record → token) (hinj : Function.Injective encode)
    (dl : ParaleanDelivery.CanonicalState node group request packet snapshot name)
    (rg : ParaleanGroups.CanonicalState node group name snapshot)
    (rec : ParaleanRecovery.CanonicalState record workspace snapshot group name token scan)
    (disk disk' : ParaleanGroupComposition.DiskState replica (ParaleanAdmission.StoredObject group snapshot) writeQuorum readQuorum)
    (x : replica) (c : record) (e : Extra record)
    (hd : ParaleanGroupComposition.StorageNext a.storage disk (.Put x (.catalog (encode c))) disk')
    (current : r.tokenRank (recordToken c) = rec.fence) :
    Next a r encode recordToken (⟨⟨dl, ⟨rg, disk⟩⟩, rec⟩, e)
      (⟨⟨dl, ⟨rg, disk'⟩⟩, rec⟩, update encode ⟨⟨dl, ⟨rg, disk⟩⟩, rec⟩ ⟨⟨dl, ⟨rg, disk'⟩⟩, rec⟩ e) := by
  obtain ⟨hst, hack⟩ := put_effect a.storage x _ hd
  refine hardened_step a r encode recordToken e
    (ParaleanProtocol.storage_step a r encode dl rg rec disk disk' _ hd trivial) ?_
  rintro c' (⟨y, h1, h2⟩ | ⟨h1, h2⟩)
  · have heq := (hst y _ h1 h2).2
    have : c' = c := hinj (ParaleanArtifacts.catalog_injective heq)
    subst this
    exact Or.inl current
  · dsimp only at h1 h2
    rw [hack] at h1
    simp_all

/-- Repair is unconditional: copying a record's bytes read from a live replica to
another live replica is a hardened step at any fence, whatever the record's token. -/
theorem repair_put_enabled (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : record → token) (hinj : Function.Injective encode)
    (dl : ParaleanDelivery.CanonicalState node group request packet snapshot name)
    (rg : ParaleanGroups.CanonicalState node group name snapshot)
    (rec : ParaleanRecovery.CanonicalState record workspace snapshot group name token scan)
    (disk disk' : ParaleanGroupComposition.DiskState replica (ParaleanAdmission.StoredObject group snapshot) writeQuorum readQuorum)
    (x : replica) (c : record) (e : Extra record)
    (hd : ParaleanGroupComposition.StorageNext a.storage disk (.Put x (.catalog (encode c))) disk')
    (present : ∃ y, disk.live y = true ∧ disk.stored y (.catalog (encode c)) = true) :
    Next a r encode recordToken (⟨⟨dl, ⟨rg, disk⟩⟩, rec⟩, e)
      (⟨⟨dl, ⟨rg, disk'⟩⟩, rec⟩, update encode ⟨⟨dl, ⟨rg, disk⟩⟩, rec⟩ ⟨⟨dl, ⟨rg, disk'⟩⟩, rec⟩ e) := by
  obtain ⟨hst, hack⟩ := put_effect a.storage x _ hd
  refine no_first_write_step a r encode recordToken e
    (ParaleanProtocol.storage_step a r encode dl rg rec disk disk' _ hd trivial) ?_
  rintro c' (⟨y, h1, h2⟩ | ⟨h1, h2⟩)
  · have heq := (hst y _ h1 h2).2
    have : c' = c := hinj (ParaleanArtifacts.catalog_injective heq)
    subst this
    exact present
  · dsimp only at h1 h2
    rw [hack] at h1
    simp_all

/-- Acknowledgement is unconditional: acknowledging a record whose bytes a live
replica holds is a hardened step at any fence, whatever the record's token. (The
base Ack already needs the bytes on every member of a live write quorum.) -/
theorem ack_unfenced (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : record → token) (hinj : Function.Injective encode)
    (dl : ParaleanDelivery.CanonicalState node group request packet snapshot name)
    (rg : ParaleanGroups.CanonicalState node group name snapshot)
    (rec : ParaleanRecovery.CanonicalState record workspace snapshot group name token scan)
    (disk disk' : ParaleanGroupComposition.DiskState replica (ParaleanAdmission.StoredObject group snapshot) writeQuorum readQuorum)
    (w : writeQuorum) (c : record) (e : Extra record)
    (hd : ParaleanGroupComposition.StorageNext a.storage disk (.Ack (.catalog (encode c)) w) disk')
    (present : ∃ y, disk.live y = true ∧ disk.stored y (.catalog (encode c)) = true) :
    Next a r encode recordToken (⟨⟨dl, ⟨rg, disk⟩⟩, rec⟩, e)
      (⟨⟨dl, ⟨rg, disk'⟩⟩, rec⟩, update encode ⟨⟨dl, ⟨rg, disk⟩⟩, rec⟩ ⟨⟨dl, ⟨rg, disk'⟩⟩, rec⟩ e) := by
  obtain ⟨hst, hack⟩ := ack_effect a.storage _ w hd
  refine no_first_write_step a r encode recordToken e
    (ParaleanProtocol.storage_step a r encode dl rg rec disk disk' _ hd trivial) ?_
  rintro c' (⟨y, h1, h2⟩ | ⟨h1, h2⟩)
  · dsimp only at h1 h2
    rw [hst] at h1
    simp_all
  · have heq := hack _ h1 h2
    have : c' = c := hinj (ParaleanArtifacts.catalog_injective heq)
    subst this
    exact present


/-- The base protocol with the same ghost bookkeeping but no fence check. -/
inductive GhostReachable (a : ATheory) (r : RTheory) (encode : record → Nat) :
    ModelState × Extra record → Prop where
  | initial {p} : Initial a r p → GhostReachable a r encode p
  | step {s t e} : GhostReachable a r encode (s, e) → ParaleanProtocol.Next a r encode s t →
      GhostReachable a r encode (t, update encode s t e)

theorem update_quiet (encode : record → Nat) {s t : ModelState} (e : Extra record)
    (h : ∀ c, ¬ NewWrite encode s t c) : update encode s t e = e := by
  funext c
  simp [update, h c]

theorem same_storage_no_write (encode : record → Nat) {s t : ModelState}
    (h : t.admission.protocol.storage = s.admission.protocol.storage) (c : record) :
    ¬ NewWrite encode s t c := by
  rintro (⟨x, h1, h2⟩ | ⟨h1, h2⟩) <;> rw [h] at h1 <;> simp_all

end

namespace Example
noncomputable section
open ParaleanAdmission
open ParaleanCompletionRecovery.Example (theory recoveryTheory encode put ack disk0 disk1 disk2
  disk3 disk4 disk5 disk6 disk7 disk8 disk9 diskCatalog1 diskCatalog2 diskCatalog diskCatalogLost
  put_step ack_step rec0 recCommitted recForgotten forget_desktop destroy_catalog_replica
  assumptions recovery_assumptions recovery_initial initial_valid groupTheory storageTheory
  dl0 rg0 state CState idScan)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

/-- Every catalogue record embeds the oldest token (rank 0). -/
def tok : Bool → Bool := fun _ => false

def mk (disk : ParaleanCompletionRecovery.Example.Disk)
    (rec : ParaleanRecovery.CanonicalState Bool Unit Bool Bool (Fin 3) Bool ParaleanCompletionRecovery.Example.Scan) : CState :=
  ⟨state dl0 rg0 disk, rec⟩

-- Hardened run: commit under fence 0, lose a replica and the desktop, rotate.
def fRot := { recCommitted with fence := 1 }
def fScan := { fRot with known := id, scanned := true }
def fRebuilt := { fScan with heads := id, reconstructed := true }
def fAuto := { fRebuilt with selected := true, selectedRecord := true }
-- Unfenced run: rotate first, then write and acknowledge the old-token record.
def nRot := { rec0 with fence := 1 }
def nScan := { nRot with committed := id, durableAck := id, known := id, scanned := true }
def nRebuilt := { nScan with heads := id, reconstructed := true }
def nAuto := { nRebuilt with selected := true, selectedRecord := true }

local instance : delta% (ParaleanRecovery.reconstruct._veil_dec_type_0
  (record := Bool) (workspace := Unit) (snapshot := Bool)
  (decl := Bool) (name := Fin 3) (token := Bool) (scan := ParaleanCompletionRecovery.Example.Scan)
  (χ := ParaleanRecovery.CanonicalRep Bool Unit Bool Bool (Fin 3) Bool ParaleanCompletionRecovery.Example.Scan)) :=
  fun _ _ _ => Classical.propDecidable _
local instance : delta% (ParaleanRecovery.reconstruct._veil_dec_type_1
  (record := Bool) (workspace := Unit) (snapshot := Bool)
  (decl := Bool) (name := Fin 3) (token := Bool) (scan := ParaleanCompletionRecovery.Example.Scan)
  (χ := ParaleanRecovery.CanonicalRep Bool Unit Bool Bool (Fin 3) Bool ParaleanCompletionRecovery.Example.Scan)) :=
  fun _ _ => Classical.propDecidable _
local instance : delta% (ParaleanRecovery.automatic._veil_dec_type_0
  (record := Bool) (workspace := Unit) (snapshot := Bool)
  (decl := Bool) (name := Fin 3) (token := Bool) (scan := ParaleanCompletionRecovery.Example.Scan)
  (χ := ParaleanRecovery.CanonicalRep Bool Unit Bool Bool (Fin 3) Bool ParaleanCompletionRecovery.Example.Scan)) :=
  fun _ _ => Classical.propDecidable _

macro "fence_simp" : tactic => `(tactic| simp [ParaleanRecovery.RecoveryNext, ParaleanRecovery.Next,
    ParaleanRecovery.NextAct, ParaleanRecovery.commit.ext.derived_eq,
    ParaleanRecovery.rotateFence.ext.derived_eq, ParaleanRecovery.enumerate.ext.derived_eq,
    ParaleanRecovery.reconstruct.ext.derived_eq, ParaleanRecovery.automatic.ext.derived_eq,
    ParaleanRecovery.commit.ext.tr, ParaleanRecovery.rotateFence.ext.tr,
    ParaleanRecovery.enumerate.ext.tr, ParaleanRecovery.reconstruct.ext.tr,
    ParaleanRecovery.automatic.ext.tr, ParaleanRecovery.admissible, ParaleanRecovery.buildable,
    fRot, fScan, fRebuilt, fAuto, nRot, nScan, nRebuilt, nAuto, recForgotten, recCommitted, rec0,
    recoveryTheory, groupTheory, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanRecovery.canonicalFieldRep, Veil.canonicalFieldRepresentation,
    Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
    funext_iff, Bool.forall_bool, Bool.exists_bool])

theorem recovery_steps :
    ParaleanRecovery.RecoveryNext recoveryTheory rec0 (.commit true false) recCommitted ∧
    ParaleanRecovery.RecoveryNext recoveryTheory recForgotten (.rotateFence true) fRot ∧
    ParaleanRecovery.RecoveryNext recoveryTheory fRot (.enumerate idScan) fScan ∧
    ParaleanRecovery.RecoveryNext recoveryTheory fScan .reconstruct fRebuilt ∧
    ParaleanRecovery.RecoveryNext recoveryTheory fRebuilt (.automatic true) fAuto ∧
    ParaleanRecovery.RecoveryNext recoveryTheory rec0 (.rotateFence true) nRot ∧
    ParaleanRecovery.RecoveryNext recoveryTheory nRot (.enumerate idScan) nScan ∧
    ParaleanRecovery.RecoveryNext recoveryTheory nScan .reconstruct nRebuilt ∧
    ParaleanRecovery.RecoveryNext recoveryTheory nRebuilt (.automatic true) nAuto := by
  repeat' apply And.intro
  all_goals fence_simp

abbrev N := ParaleanProtocol.Next theory recoveryTheory encode

theorem put_base (disk : ParaleanCompletionRecovery.Example.Disk) rec (x : Bool) (o : StoredObject Bool Bool)
    (live : disk.live x = true) : N (mk disk rec) (mk (put disk x o) rec) :=
  ParaleanProtocol.storage_step theory recoveryTheory encode dl0 rg0 rec disk _ (.Put x o)
    (put_step disk x o live) trivial

theorem ack_base (disk : ParaleanCompletionRecovery.Example.Disk) rec (o : StoredObject Bool Bool)
    (quorum : ∀ x, disk.live x = true ∧ disk.stored x o = true)
    (guard : ParaleanPublicationDiscovery.StorageGuard
      (Durability.Label.Ack o () : Durability.Label Bool (StoredObject Bool Bool) Unit Unit)) :
    N (mk disk rec) (mk (ack disk o) rec) :=
  ParaleanProtocol.storage_step theory recoveryTheory encode dl0 rg0 rec disk _ (.Ack o ())
    (ack_step disk o quorum) guard

theorem rec_base (disk : ParaleanCompletionRecovery.Example.Disk) rec rec'
    (l : ParaleanRecovery.Label Bool Unit Bool Bool (Fin 3) Bool ParaleanCompletionRecovery.Example.Scan)
    (hl : ∀ c epoch, l ≠ .commit c epoch)
    (ready : ∀ v, l = .enumerate v → ∀ c, recoveryTheory.ready v c = true →
      ParaleanRecovery.StorageReady (ParaleanRecovery.ofAdmission theory recoveryTheory encode).base disk
        (ParaleanRecovery.ofAdmission theory recoveryTheory encode |>.recordObject c) (recoveryTheory.image c))
    (h : ParaleanRecovery.RecoveryNext recoveryTheory rec l rec') : N (mk disk rec) (mk disk rec') :=
  ParaleanProtocol.recovery_step theory recoveryTheory encode (state dl0 rg0 disk) rec rec'
    (.recovery l hl ready h)

theorem ready_on (disk : ParaleanCompletionRecovery.Example.Disk)
    (hcat : disk.acknowledged (.catalog 1) = true) (hman : disk.acknowledged (.manifest true) = true)
    (hpay : ∀ g, disk.acknowledged (.payload g) = true) :
    ∀ v, (ParaleanRecovery.Label.enumerate idScan : ParaleanRecovery.Label Bool Unit Bool Bool (Fin 3) Bool ParaleanCompletionRecovery.Example.Scan) = .enumerate v →
      ∀ c, recoveryTheory.ready v c = true →
      ParaleanRecovery.StorageReady (ParaleanRecovery.ofAdmission theory recoveryTheory encode).base disk
        (ParaleanRecovery.ofAdmission theory recoveryTheory encode |>.recordObject c) (recoveryTheory.image c) := by
  intro v hv c hc
  cases hv
  cases c
  · simp [recoveryTheory] at hc
  · refine ⟨hcat, hman, ?_⟩
    intro d _
    exact hpay d

theorem commit_on {rec rec'} (epoch : Bool)
    (hr : ParaleanRecovery.RecoveryNext recoveryTheory rec (.commit true epoch) rec') :
    N (mk diskCatalog2 rec) (mk diskCatalog rec') := by
  have hd := ack_step diskCatalog2 (.catalog 1) (by
    intro x; cases x <;> simp [diskCatalog2, diskCatalog1, disk9, disk8, disk7, disk6, disk5,
      disk4, disk3, disk2, disk1, disk0, put, ack])
  refine .paired (.coupled (.protocol (.storage (.Ack (.catalog 1) ()) hd)) rfl rfl
    (.commit true epoch () hr hd ?_ ?_)) (.storage (.Ack (.catalog 1) ()) trivial hd)
  · simp [mk, state, ParaleanRecovery.ofAdmission, protocolTheory, theory, recoveryTheory,
      diskCatalog2, diskCatalog1, disk9, disk8, disk7, disk6, disk5, disk4, disk3, disk2, disk1,
      disk0, put, ack]
  · intro g _
    cases g <;> simp [mk, state, ParaleanRecovery.ofAdmission, protocolTheory, theory, recoveryTheory,
      diskCatalog2, diskCatalog1, disk9, disk8, disk7, disk6, disk5, disk4, disk3, disk2, disk1,
      disk0, put, ack]

theorem commit_base : N (mk diskCatalog2 rec0) (mk diskCatalog recCommitted) :=
  commit_on false recovery_steps.1

theorem fenced_at (disk : ParaleanCompletionRecovery.Example.Disk) rec
    (hf : rec.fence = 0) (c : Bool) :
    Fenced recoveryTheory tok (mk disk rec) c := by
  simp [Fenced, tok, recoveryTheory, mk, hf]

/-- A step under fence 0, where every record's (rank-0) token is current. -/
theorem hstep0 {disk disk' : ParaleanCompletionRecovery.Example.Disk} {rec rec'} (e : Extra Bool)
    (hb : N (mk disk rec) (mk disk' rec')) (hf : rec.fence = 0) :
    Next theory recoveryTheory encode tok (mk disk rec, e)
      (mk disk' rec', update encode (mk disk rec) (mk disk' rec') e) :=
  hardened_step _ _ _ _ e hb (fun c _ => Or.inl (fenced_at disk rec hf c))

/-- A step that leaves the store unchanged. -/
theorem hquiet {disk : ParaleanCompletionRecovery.Example.Disk} {rec rec'} (e : Extra Bool)
    (hb : N (mk disk rec) (mk disk rec')) :
    Next theory recoveryTheory encode tok (mk disk rec, e) (mk disk rec', e) := by
  have hq : ∀ c, ¬ NewWrite encode (mk disk rec) (mk disk rec') c :=
    same_storage_no_write (s := mk disk rec) (t := mk disk rec') encode rfl
  have h := hardened_step theory recoveryTheory encode tok e hb
    (fun c hn => absurd hn (hq c))
  rwa [update_quiet encode e hq] at h

macro "disk_simp" : tactic => `(tactic| (intro x; cases x <;> simp [diskCatalog, diskCatalog2,
  diskCatalog1, disk9, disk8, disk7, disk6, disk5, disk4, disk3, disk2, disk1, disk0, put, ack]))

theorem initial_mk : ParaleanCompletionRecovery.Initial theory recoveryTheory (mk disk0 rec0) :=
  ⟨initial_valid, recovery_initial⟩

/-- Base prefix shared by both runs: payloads and the manifest of snapshot `true`. -/
theorem prefix_base (rec : ParaleanRecovery.CanonicalState Bool Unit Bool Bool (Fin 3) Bool ParaleanCompletionRecovery.Example.Scan) :
    N (mk disk0 rec) (mk disk1 rec) ∧ N (mk disk1 rec) (mk disk2 rec) ∧
    N (mk disk2 rec) (mk disk3 rec) ∧ N (mk disk3 rec) (mk disk4 rec) ∧
    N (mk disk4 rec) (mk disk5 rec) ∧ N (mk disk5 rec) (mk disk6 rec) ∧
    N (mk disk6 rec) (mk disk7 rec) ∧ N (mk disk7 rec) (mk disk8 rec) ∧
    N (mk disk8 rec) (mk disk9 rec) ∧
    N (mk disk9 rec) (mk diskCatalog1 rec) ∧ N (mk diskCatalog1 rec) (mk diskCatalog2 rec) := by
  refine ⟨put_base _ _ _ _ rfl, put_base _ _ _ _ rfl, ack_base _ _ _ (by disk_simp) trivial,
    put_base _ _ _ _ rfl, put_base _ _ _ _ rfl, ack_base _ _ _ (by disk_simp) trivial,
    put_base _ _ _ _ rfl, put_base _ _ _ _ rfl, ack_base _ _ _ (by disk_simp) trivial,
    put_base _ _ _ _ rfl, put_base _ _ _ _ rfl⟩

theorem lose_base : N (mk diskCatalog recCommitted) (mk diskCatalogLost recCommitted) :=
  ParaleanProtocol.storage_step theory recoveryTheory encode dl0 rg0 recCommitted diskCatalog
    diskCatalogLost (.Lose false) destroy_catalog_replica trivial

theorem desktop_base : N (mk diskCatalogLost recCommitted) (mk diskCatalogLost recForgotten) :=
  ParaleanProtocol.failure_step theory recoveryTheory encode (.desktop forget_desktop)

theorem lost_ready : ∀ v, (ParaleanRecovery.Label.enumerate idScan : ParaleanRecovery.Label Bool Unit Bool Bool (Fin 3) Bool ParaleanCompletionRecovery.Example.Scan) = .enumerate v →
      ∀ c, recoveryTheory.ready v c = true →
      ParaleanRecovery.StorageReady (ParaleanRecovery.ofAdmission theory recoveryTheory encode).base diskCatalogLost
        (ParaleanRecovery.ofAdmission theory recoveryTheory encode |>.recordObject c) (recoveryTheory.image c) :=
  ready_on _ (by simp [diskCatalogLost, diskCatalog, ack]) (by simp [diskCatalogLost, diskCatalog,
    diskCatalog2, diskCatalog1, disk9, ack, put])
    (by intro g; cases g <;> simp [diskCatalogLost, diskCatalog, diskCatalog2, diskCatalog1, disk9,
      disk8, disk7, disk6, disk5, disk4, disk3, ack, put])

/-- Non-vacuity. A current writer writes and commits record `true` under fence 0.
A replica and the desktop are lost, the fence rotates to 1, and a first write of
a fresh rank-0 record is disabled although the base storage step is enabled.
Recovery scans and automatically selects the legitimately fenced record. -/
theorem fenced_recovery_execution :
    (∃ e, Reachable theory recoveryTheory encode tok (mk diskCatalogLost fRot, e)) ∧
    (∀ e, ¬ ∃ t e', Next theory recoveryTheory encode tok (mk diskCatalogLost fRot, e) (t, e') ∧
      NewWrite encode (mk diskCatalogLost fRot) t false) ∧
    N (mk diskCatalogLost fRot) (mk (put diskCatalogLost true (.catalog 0)) fRot) ∧
    NewWrite encode (mk diskCatalogLost fRot) (mk (put diskCatalogLost true (.catalog 0)) fRot) false ∧
    ∃ e, Reachable theory recoveryTheory encode tok (mk diskCatalogLost fAuto, e) ∧
      fAuto.selected = true ∧ fAuto.selectedRecord = true ∧ fAuto.fence = 1 ∧ fAuto.writer = true ∧
      e true = some 0 := by
  have pre := prefix_base rec0
  have h0 : Reachable theory recoveryTheory encode tok (mk disk0 rec0, fun _ => none) :=
    .initial ⟨initial_mk, rfl⟩
  have h1 := Reachable.step h0 (hstep0 _ pre.1 rfl)
  have h2 := Reachable.step h1 (hstep0 _ pre.2.1 rfl)
  have h3 := Reachable.step h2 (hstep0 _ pre.2.2.1 rfl)
  have h4 := Reachable.step h3 (hstep0 _ pre.2.2.2.1 rfl)
  have h5 := Reachable.step h4 (hstep0 _ pre.2.2.2.2.1 rfl)
  have h6 := Reachable.step h5 (hstep0 _ pre.2.2.2.2.2.1 rfl)
  have h7 := Reachable.step h6 (hstep0 _ pre.2.2.2.2.2.2.1 rfl)
  have h8 := Reachable.step h7 (hstep0 _ pre.2.2.2.2.2.2.2.1 rfl)
  have h9 := Reachable.step h8 (hstep0 _ pre.2.2.2.2.2.2.2.2.1 rfl)
  have h10 := Reachable.step h9 (hstep0 _ pre.2.2.2.2.2.2.2.2.2.1 rfl)
  have h11 := Reachable.step h10 (hstep0 _ pre.2.2.2.2.2.2.2.2.2.2 rfl)
  have h12 := Reachable.step h11 (hstep0 _ commit_base rfl)
  have h13 := Reachable.step h12 (hstep0 _ lose_base rfl)
  have h14 := Reachable.step h13 (hstep0 _ desktop_base rfl)
  have h15 := Reachable.step h14 (hquiet _ (rec_base _ _ _ (.rotateFence true)
    (by intro c epoch h; cases h) (by intro v h; cases h) recovery_steps.2.1))
  have h16 := Reachable.step h15 (hquiet _ (rec_base _ _ _ (.enumerate idScan)
    (by intro c epoch h; cases h) lost_ready recovery_steps.2.2.1))
  have h17 := Reachable.step h16 (hquiet _ (rec_base _ _ _ .reconstruct
    (by intro c epoch h; cases h) (by intro v h; cases h) recovery_steps.2.2.2.1))
  have h18 := Reachable.step h17 (hquiet _ (rec_base _ _ _ (.automatic true)
    (by intro c epoch h; cases h) (by intro v h; cases h) recovery_steps.2.2.2.2.1))
  refine ⟨⟨_, h15⟩, ?_, put_base _ _ _ _ rfl, ?_, _, h18, rfl, rfl, rfl, rfl, ?_⟩
  · rintro e ⟨t, e', hn, hw⟩
    refine stale_first_write_rejected theory recoveryTheory encode tok _ e false
      (by simp [mk, fRot, recForgotten, recCommitted, rec0, tok, recoveryTheory]) ⟨t, e', hn, hw, ?_⟩
    rintro ⟨x, hx⟩
    cases x <;> simp [mk, state, encode, diskCatalogLost, diskCatalog, diskCatalog2, diskCatalog1,
      disk9, disk8, disk7, disk6, disk5, disk4, disk3, disk2, disk1, disk0, put, ack] at hx
  · left
    exact ⟨true, by simp [mk, state, encode, put], by
      simp [mk, state, encode, diskCatalogLost, diskCatalog, diskCatalog2, diskCatalog1, disk9,
        disk8, disk7, disk6, disk5, disk4, disk3, disk2, disk1, disk0, put, ack]⟩
  · have := (selected_not_stale theory recoveryTheory encode tok assumptions recovery_assumptions
      h18 rfl).1
    simpa [mk, fAuto, fRebuilt, fScan, fRot, recCommitted, tok, recoveryTheory] using this

/-- Guard necessity. Without the fence check, after rotating to fence 1 a stale
rank-0 record is written and acknowledged; `enumerate` adopts it and `automatic`
selects it. The same write is rejected by the hardened step, and the ghost
bookkeeping records that it was first written under fence 1, not its own token. -/
theorem unfenced_stale_selection :
    ParaleanProtocol.Reachable theory recoveryTheory encode (mk diskCatalog nAuto) ∧
    nAuto.selected = true ∧ nAuto.selectedRecord = true ∧ nAuto.committed true = true ∧
    recoveryTheory.tokenRank (tok true) < nAuto.fence ∧
    N (mk disk9 nRot) (mk diskCatalog1 nRot) ∧
    NewWrite encode (mk disk9 nRot) (mk diskCatalog1 nRot) true ∧
    recoveryTheory.tokenRank (tok true) < nRot.fence ∧
    (∀ e e', ¬ Next theory recoveryTheory encode tok (mk disk9 nRot, e) (mk diskCatalog1 nRot, e')) ∧
    ∃ e, GhostReachable theory recoveryTheory encode (mk diskCatalog nAuto, e) ∧
      e true = some 1 ∧ e true ≠ some (recoveryTheory.tokenRank (tok true)) := by
  have pre := prefix_base rec0
  have preR := prefix_base nRot
  have hrot : N (mk disk9 rec0) (mk disk9 nRot) := rec_base _ _ _ (.rotateFence true)
    (by intro c epoch h; cases h) (by intro v h; cases h) recovery_steps.2.2.2.2.2.1
  have hack : N (mk diskCatalog2 nRot) (mk diskCatalog nRot) :=
    ack_base _ _ _ (by disk_simp) trivial
  have henum : N (mk diskCatalog nRot) (mk diskCatalog nScan) := rec_base _ _ _ (.enumerate idScan)
    (by intro c epoch h; cases h)
    (ready_on _ (by simp [diskCatalog, ack]) (by simp [diskCatalog, diskCatalog2, diskCatalog1, disk9, ack, put])
      (by intro g; cases g <;> simp [diskCatalog, diskCatalog2, diskCatalog1, disk9, disk8, disk7,
        disk6, disk5, disk4, disk3, ack, put]))
    recovery_steps.2.2.2.2.2.2.1
  have hrec : N (mk diskCatalog nScan) (mk diskCatalog nRebuilt) := rec_base _ _ _ .reconstruct
    (by intro c epoch h; cases h) (by intro v h; cases h) recovery_steps.2.2.2.2.2.2.2.1
  have hauto : N (mk diskCatalog nRebuilt) (mk diskCatalog nAuto) := rec_base _ _ _ (.automatic true)
    (by intro c epoch h; cases h) (by intro v h; cases h) recovery_steps.2.2.2.2.2.2.2.2
  have hnew : NewWrite encode (mk disk9 nRot) (mk diskCatalog1 nRot) true :=
    Or.inl ⟨false, by simp [mk, state, encode, diskCatalog1, put], by
      simp [mk, state, encode, disk9, disk8, disk7, disk6, disk5, disk4, disk3, disk2, disk1, disk0, put, ack]⟩
  -- Ghost bookkeeping along the unfenced run.
  have q : ∀ (d d' : ParaleanCompletionRecovery.Example.Disk) rec rec',
      (∀ c, ¬ NewWrite encode (mk d rec) (mk d' rec') c) → ∀ e,
      GhostReachable theory recoveryTheory encode (mk d rec, e) →
      N (mk d rec) (mk d' rec') → GhostReachable theory recoveryTheory encode (mk d' rec', e) := by
    intro d d' rec rec' hq e hg hb
    have := GhostReachable.step hg hb
    rwa [update_quiet encode e hq] at this
  have nw : ∀ (d d' : ParaleanCompletionRecovery.Example.Disk),
      (∀ x n, d'.stored x (.catalog n) = true → d.stored x (.catalog n) = true) →
      (∀ n, d'.acknowledged (.catalog n) = true → d.acknowledged (.catalog n) = true) →
      ∀ rec rec' c, ¬ NewWrite encode (mk d rec) (mk d' rec') c := by
    intro d d' hs ha rec rec' c hn
    rcases hn with ⟨x, h1, h2⟩ | ⟨h1, h2⟩
    · have := hs x _ h1; simp_all [mk, state]
    · have := ha _ h1; simp_all [mk, state]
  let e₁ : Extra Bool := fun c => if c then some 1 else none
  have g0 : GhostReachable theory recoveryTheory encode (mk disk0 rec0, fun _ => none) :=
    .initial ⟨initial_mk, rfl⟩
  have stp := fun d d' rec rec' hs ha => q d d' rec rec' (nw d d' hs ha rec rec')
  have g9 : GhostReachable theory recoveryTheory encode (mk disk9 rec0, fun _ => none) := by
    refine stp _ _ _ _ ?_ ?_ _ ?_ pre.2.2.2.2.2.2.2.2.1
    · intro x n h; simpa [disk9, disk8, put, ack] using h
    · intro n h; simpa [disk9, disk8, put, ack] using h
    refine stp _ _ _ _ ?_ ?_ _ ?_ pre.2.2.2.2.2.2.2.1
    · intro x n h; simpa [disk8, put] using h
    · intro n h; simpa [disk8, put] using h
    refine stp _ _ _ _ ?_ ?_ _ ?_ pre.2.2.2.2.2.2.1
    · intro x n h; simpa [disk7, put] using h
    · intro n h; simpa [disk7, put] using h
    refine stp _ _ _ _ ?_ ?_ _ ?_ pre.2.2.2.2.2.1
    · intro x n h; simpa [disk6, ack] using h
    · intro n h; simpa [disk6, ack] using h
    refine stp _ _ _ _ ?_ ?_ _ ?_ pre.2.2.2.2.1
    · intro x n h; simpa [disk5, put] using h
    · intro n h; simpa [disk5, put] using h
    refine stp _ _ _ _ ?_ ?_ _ ?_ pre.2.2.2.1
    · intro x n h; simpa [disk4, put] using h
    · intro n h; simpa [disk4, put] using h
    refine stp _ _ _ _ ?_ ?_ _ ?_ pre.2.2.1
    · intro x n h; simpa [disk3, ack] using h
    · intro n h; simpa [disk3, ack] using h
    refine stp _ _ _ _ ?_ ?_ _ ?_ pre.2.1
    · intro x n h; simpa [disk2, put] using h
    · intro n h; simpa [disk2, put] using h
    refine stp _ _ _ _ ?_ ?_ _ g0 pre.1
    · intro x n h; simpa [disk1, put] using h
    · intro n h; simpa [disk1, put] using h
  have g10 := stp _ _ _ _ (fun x n h => h) (fun n h => h) _ g9 hrot
  have g11 := GhostReachable.step g10 preR.2.2.2.2.2.2.2.2.2.1
  have hfalse : ¬ NewWrite encode (mk disk9 nRot) (mk diskCatalog1 nRot) false := by
    simp [NewWrite, mk, state, encode, diskCatalog1, put]
  have hu : update encode (mk disk9 nRot) (mk diskCatalog1 nRot) (fun _ => none) = e₁ := by
    funext c
    cases c
    · simp [update, e₁, hfalse]
    · dsimp only [update, e₁]
      rw [if_pos ⟨rfl, hnew⟩, if_pos rfl]
      rfl
  rw [hu] at g11
  have quietE : ∀ (d d' : ParaleanCompletionRecovery.Example.Disk) rec rec',
      GhostReachable theory recoveryTheory encode (mk d rec, e₁) → N (mk d rec) (mk d' rec') →
      ¬ NewWrite encode (mk d rec) (mk d' rec') false →
      GhostReachable theory recoveryTheory encode (mk d' rec', e₁) := by
    intro d d' rec rec' hg hb hq
    have := GhostReachable.step hg hb
    have he : update encode (mk d rec) (mk d' rec') e₁ = e₁ := by
      funext c
      cases c
      · simp [update, e₁, hq]
      · simp [update, e₁]
    rwa [he] at this
  have g12 := quietE _ _ _ _ g11 preR.2.2.2.2.2.2.2.2.2.2
    (by simp [NewWrite, mk, state, encode, diskCatalog2, put])
  have g13 := quietE _ _ _ _ g12 hack (by simp [NewWrite, mk, state, encode, diskCatalog, ack])
  have g14 := quietE _ _ _ _ g13 henum (same_storage_no_write encode rfl false)
  have g15 := quietE _ _ _ _ g14 hrec (same_storage_no_write encode rfl false)
  have g16 := quietE _ _ _ _ g15 hauto (same_storage_no_write encode rfl false)
  have base : ParaleanProtocol.Reachable theory recoveryTheory encode (mk diskCatalog nAuto) := by
    have b0 : ParaleanProtocol.Reachable theory recoveryTheory encode (mk disk0 rec0) := .initial initial_mk
    exact .step (.step (.step (.step (.step (.step (.step (.step (.step (.step (.step (.step
      (.step (.step (.step (.step b0 pre.1) pre.2.1) pre.2.2.1) pre.2.2.2.1) pre.2.2.2.2.1)
      pre.2.2.2.2.2.1) pre.2.2.2.2.2.2.1) pre.2.2.2.2.2.2.2.1) pre.2.2.2.2.2.2.2.2.1) hrot)
      preR.2.2.2.2.2.2.2.2.2.1) preR.2.2.2.2.2.2.2.2.2.2) hack) henum) hrec) hauto
  refine ⟨base, rfl, rfl, rfl, by simp [tok, recoveryTheory, nAuto, nRebuilt, nScan, nRot, rec0],
    preR.2.2.2.2.2.2.2.2.2.1, hnew, by simp [tok, recoveryTheory, nRot, rec0], ?_, e₁, g16, rfl,
    by intro h; simp [e₁, tok, recoveryTheory] at h⟩
  intro e e' h
  refine stale_first_write_rejected theory recoveryTheory encode tok _ e true
    (by simp [mk, nRot, rec0, tok, recoveryTheory]) ⟨_, _, h, hnew, ?_⟩
  rintro ⟨x, hx⟩
  cases x <;> simp [mk, state, encode, disk9, disk8, disk7, disk6, disk5, disk4, disk3, disk2,
    disk1, disk0, put, ack] at hx

/-- Commit after rotation under the current epoch `true` (rank 1). -/
def lRec := { nRot with committed := id, durableAck := id }

theorem late_commit_step :
    ParaleanRecovery.RecoveryNext recoveryTheory nRot (.commit true true) lRec := by
  fence_simp; simp [lRec, nRot, rec0]

/-- In a step that leaves record `false`'s object untouched, only `true` is newly written. -/
theorem only_true_written (d : ParaleanCompletionRecovery.Example.Disk) rec
    (d' : ParaleanCompletionRecovery.Example.Disk) rec'
    (hs : ∀ x, d'.stored x (.catalog 0) = d.stored x (.catalog 0))
    (ha : d'.acknowledged (.catalog 0) = d.acknowledged (.catalog 0))
    (c : Bool) (hn : NewWrite encode (mk d rec) (mk d' rec') c) : c = true := by
  cases c
  · exfalso
    rcases hn with ⟨x, h1, h2⟩ | ⟨h1, h2⟩
    · have e1 : d'.stored x (.catalog 0) = true := by simpa [mk, state, encode] using h1
      have e2 : d.stored x (.catalog 0) = false := by simpa [mk, state, encode] using h2
      rw [hs x] at e1; rw [e1] at e2; cases e2
    · have e1 : d'.acknowledged (.catalog 0) = true := by simpa [mk, state, encode] using h1
      have e2 : d.acknowledged (.catalog 0) = false := by simpa [mk, state, encode] using h2
      rw [ha] at e1; rw [e1] at e2; cases e2
  · rfl

/-- Non-vacuity of the relaxed guard. Under fence 0 the rank-0 record `true` is
first written to replica `false`. The fence rotates to 1. A repair Put then copies
those bytes to replica `true`, and the record is acknowledged and committed, all
after rotation and with the record's token below the fence. The old guard (every
new copy or acknowledgement fenced) rejects both steps; the hardened guard admits
them, and the committed record still has `writtenAt = some 0`. -/
theorem late_ack_and_repair_execution :
    recoveryTheory.tokenRank (tok true) < nRot.fence ∧
    -- repair copy after rotation
    NewWrite encode (mk diskCatalog1 nRot) (mk diskCatalog2 nRot) true ∧
    ¬ FirstWrite encode (mk diskCatalog1 nRot) (mk diskCatalog2 nRot) true ∧
    (∃ e, Reachable theory recoveryTheory encode tok (mk diskCatalog2 nRot, e)) ∧
    -- acknowledgement and commit after rotation
    NewWrite encode (mk diskCatalog2 nRot) (mk diskCatalog lRec) true ∧
    ∃ e, Reachable theory recoveryTheory encode tok (mk diskCatalog lRec, e) ∧
      lRec.committed true = true ∧ lRec.fence = 1 ∧ e true = some 0 := by
  have pre := prefix_base rec0
  have h0 : Reachable theory recoveryTheory encode tok (mk disk0 rec0, fun _ => none) :=
    .initial ⟨initial_mk, rfl⟩
  have h1 := Reachable.step h0 (hstep0 _ pre.1 rfl)
  have h2 := Reachable.step h1 (hstep0 _ pre.2.1 rfl)
  have h3 := Reachable.step h2 (hstep0 _ pre.2.2.1 rfl)
  have h4 := Reachable.step h3 (hstep0 _ pre.2.2.2.1 rfl)
  have h5 := Reachable.step h4 (hstep0 _ pre.2.2.2.2.1 rfl)
  have h6 := Reachable.step h5 (hstep0 _ pre.2.2.2.2.2.1 rfl)
  have h7 := Reachable.step h6 (hstep0 _ pre.2.2.2.2.2.2.1 rfl)
  have h8 := Reachable.step h7 (hstep0 _ pre.2.2.2.2.2.2.2.1 rfl)
  have h9 := Reachable.step h8 (hstep0 _ pre.2.2.2.2.2.2.2.2.1 rfl)
  -- first write under fence 0
  have h10 := Reachable.step h9 (hstep0 _ pre.2.2.2.2.2.2.2.2.2.1 rfl)
  -- rotation
  have h11 := Reachable.step h10 (hquiet _ (rec_base _ _ _ (.rotateFence true)
    (by intro c epoch h; cases h) (by intro v h; cases h) recovery_steps.2.2.2.2.2.1))
  have held : CopySource encode (mk diskCatalog1 nRot) true :=
    ⟨false, rfl, by simp [mk, state, encode, diskCatalog1, put]⟩
  have only1 := @only_true_written
  -- repair copy after rotation
  have hrepNew : NewWrite encode (mk diskCatalog1 nRot) (mk diskCatalog2 nRot) true :=
    Or.inl ⟨true, by simp [mk, state, encode, diskCatalog2, put], by
      simp [mk, state, encode, diskCatalog1, disk9, disk8, disk7, disk6, disk5, disk4, disk3,
        disk2, disk1, disk0, put, ack]⟩
  have h12 := Reachable.step h11 (no_first_write_step theory recoveryTheory encode tok _
    (put_base diskCatalog1 nRot true (.catalog 1) rfl) (by
      intro c hn
      have := only1 _ _ _ _ (by intro x; simp [diskCatalog2, put]) (by simp [diskCatalog2, put]) c hn
      subst this; exact held))
  -- acknowledgement and commit after rotation
  have held2 : CopySource encode (mk diskCatalog2 nRot) true :=
    ⟨false, rfl, by simp [mk, state, encode, diskCatalog2, diskCatalog1, put]⟩
  have hcommit := commit_on (rec := nRot) (rec' := lRec) true late_commit_step
  have h13 := Reachable.step h12 (no_first_write_step theory recoveryTheory encode tok _ hcommit (by
      intro c hn
      have := only1 _ _ _ _ (by intro x; simp [diskCatalog, diskCatalog2, ack, put]) (by simp [diskCatalog, diskCatalog2, ack, put]) c hn
      subst this; exact held2))
  have hackNew : NewWrite encode (mk diskCatalog2 nRot) (mk diskCatalog lRec) true :=
    Or.inr ⟨by simp [mk, state, encode, diskCatalog, ack], by
      simp [mk, state, encode, diskCatalog2, diskCatalog1, disk9, disk8, disk7, disk6, disk5, disk4,
        disk3, disk2, disk1, disk0, put, ack]⟩
  refine ⟨by simp [tok, recoveryTheory, nRot], hrepNew, fun h => h.2 (copySource_stored encode held), ⟨_, h12⟩, hackNew,
    _, h13, rfl, rfl, ?_⟩
  have := ((catalog_objects_fenced theory recoveryTheory encode tok assumptions recovery_assumptions
    h13).2 true rfl).1
  simpa [tok, recoveryTheory] using this

end
end Example
#print axioms guard_stutter
#print axioms reachable_protocol
#print axioms fence_mono
#print axioms reachable_inv
#print axioms present_fenced
#print axioms stale_first_write_rejected
#print axioms repair_put_enabled
#print axioms ack_unfenced
#print axioms catalog_objects_fenced
#print axioms selected_not_stale
#print axioms completion_not_stale
#print axioms guard_enabled_iff
#print axioms fenced_put_enabled
#print axioms Example.fenced_recovery_execution
#print axioms Example.unfenced_stale_selection
#print axioms Example.late_ack_and_repair_execution
end ParaleanCatalogFencing
