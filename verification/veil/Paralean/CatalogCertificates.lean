import Paralean.Protocol
import Paralean.CatalogFencing
import Paralean.AckCertificates

/-! Physically readable catalogue certificates and fenced commit records.

`ParaleanRecovery.StorageReady` (the base readiness test of `enumerate`) reads
Durability's ghost `acknowledged` flag for the catalogue record, its manifest and
its payloads. After replica loss a lone surviving copy cannot show whether it was
acknowledged. `ParaleanCatalogFencing` fences only first writes, so a stale
writer's record that was first written before a rotation can be repaired,
acknowledged and adopted after it (`late_ack_and_repair_execution`).

This layer adds per-replica certificate records, erased with their replica:

- `ocert x o`: replica `x` holds an acknowledgement certificate for object `o`
  (a manifest or payload). Written only for an acknowledged object.
- `rcert x c`: replica `x` holds the commit certificate of catalogue record `c`.
  It is written by a store-side conditional write that checks the fence: the
  record's token rank must equal the current fence. It is the commit point.
- `certFence c` (ghost): the fence at which `c`'s commit certificate was written.

A record is certified (`CatReady`) when, for its record, manifest and every
payload, every live member of some write quorum holds the certificate. A reader
checks this by reading live replicas only. Every step that makes a record
committed (the writer's commit or recovery adoption by `enumerate`) requires
`CatReady` in the pre-state. Recovery uses a scan built from the store:
decoded = record bytes on a live member of the read quorum, ready = `CatReady`. -/
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ParaleanRecovery
noncomputable section CoverAdequacy
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
attribute [local instance] Classical.propDecidable

/-- `ReadyScan` asks the scan's readiness to coincide with ghost acknowledgement.
Enumeration needs less: the scan covers committed records, and readiness implies
the base `StorageReady` test. A physical certificate scan satisfies both. -/
theorem committed_admissible_of_cover
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (s : CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (hs : CoupledSafe th s) (v : scan)
    (hcover : ∀ c, s.recovery.committed c = true →
      th.recovery.decoded v c = true ∧ th.recovery.ready v c = true)
    (c : record) (hc : s.recovery.committed c = true) : admissible v c th.recovery s.recovery := by
  have facts := hs.1.1 c hc
  refine ⟨(hcover c hc).1, (hcover c hc).2, facts.1, facts.2.2.1, ?_⟩
  intro p hp
  have pc := facts.2.2.2 p hp
  have pfacts := hs.1.1 p pc
  exact ⟨(hcover p pc).1, (hcover p pc).2, pfacts.1, pfacts.2.2.1⟩

theorem enumeration_enabled_of_cover
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (s : CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (v : scan)
    (hcover : ∀ c, s.recovery.committed c = true →
      th.recovery.decoded v c = true ∧ th.recovery.ready v c = true)
    (hsound : ∀ c, th.recovery.ready v c = true →
      StorageReady th.base s.storage (th.recordObject c) (th.recovery.image c)) :
    ∃ rec', CoupledNext th s ⟨rec', s.storage⟩ ∧
      RecoveryNext th.recovery s.recovery (.enumerate v) rec' ∧
      rec'.scanned = true ∧ rec'.writer = s.recovery.writer ∧ rec'.fence = s.recovery.fence ∧
      (∀ c, rec'.known c = true ↔ admissible v c th.recovery s.recovery) ∧
      (∀ c, rec'.committed c = true ↔
        s.recovery.committed c = true ∨ admissible v c th.recovery s.recovery) := by
  let accepted := fun c => decide (admissible v c th.recovery s.recovery)
  let rec' : CanonicalState record workspace snapshot decl name token scan :=
    { s.recovery with
      known := accepted
      committed := fun c => s.recovery.committed c || accepted c
      durableAck := fun c => s.recovery.durableAck c || accepted c
      heads := fun _ => false
      scanned := true
      reconstructed := false
      conflict := false
      selected := false }
  have ht : RecoveryNext th.recovery s.recovery (.enumerate v) rec' := by
    simp only [RecoveryNext, Next, NextAct, enumerate.ext.derived_eq]
    dsimp [enumerate.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
      instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep, Veil.canonicalFieldRepresentation]
    refine ⟨hcover, ?_⟩
    simp [rec', accepted, admissible, readFrom, buildable,
      Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp]
  refine ⟨rec', ?_, ht, rfl, rfl, rfl, ?_, ?_⟩
  · apply CoupledNext.recovery (.enumerate v) (fun c epoch he => by cases he) _ ht
    intro v' hv c hc
    cases hv
    exact hsound c hc
  · intro c
    simp [rec', accepted]
  · intro c
    simp [rec', accepted]

theorem reconstruct_committed_same
    (r : Theory record workspace snapshot decl name token scan)
    {rec rec' : CanonicalState record workspace snapshot decl name token scan}
    (ht : RecoveryNext r rec .reconstruct rec') : rec'.committed = rec.committed := by
  simp only [RecoveryNext, Next, NextAct, reconstruct.ext.derived_eq] at ht
  dsimp [reconstruct.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
    Veil.canonicalFieldRepresentation] at ht
  repeat' rcases ht with ⟨_, ht⟩
  subst_vars
  rfl

theorem historical_committed_same
    (r : Theory record workspace snapshot decl name token scan) (c : record)
    {rec rec' : CanonicalState record workspace snapshot decl name token scan}
    (ht : RecoveryNext r rec (.historical c) rec') : rec'.committed = rec.committed := by
  simp only [RecoveryNext, Next, NextAct, historical.ext.derived_eq] at ht
  dsimp [historical.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
    Veil.canonicalFieldRepresentation] at ht
  repeat' rcases ht with ⟨_, ht⟩
  subst_vars
  rfl

end CoverAdequacy
end ParaleanRecovery

namespace ParaleanCatalogCertificates
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
local notation "Obj" => ParaleanAdmission.StoredObject group snapshot

/-- `rcert` and `ocert` are store state on replicas. `certFence` is ghost history. -/
structure Extra (replica record obj : Type) where
  rcert : replica → record → Bool
  ocert : replica → obj → Bool
  certFence : record → Option Nat

local notation "XState" => Extra replica record Obj

def initExtra : Extra replica record obj := ⟨fun _ _ => false, fun _ _ => false, fun _ => none⟩

/-- Static hardening inputs: the token embedded in each record. -/
abbrev RecordToken (record token : Type) := record → token

/-- A replica that goes from live to lost loses its certificates. -/
def clearLost (s t : ModelState) (e : XState) : XState :=
  { e with
    rcert := fun x c => if s.admission.protocol.storage.live x = true ∧
        t.admission.protocol.storage.live x = false then false else e.rcert x c
    ocert := fun x o => if s.admission.protocol.storage.live x = true ∧
        t.admission.protocol.storage.live x = false then false else e.ocert x o }

/-- Every live member of some write quorum holds `c`'s commit certificate. -/
def RecordDurable (a : ATheory) (s : ModelState) (e : XState) (c : record) : Prop :=
  ∃ w, ∀ x, a.storage.memberW x w = true → s.admission.protocol.storage.live x = true →
    e.rcert x c = true

/-- Every live member of some write quorum holds `o`'s acknowledgement certificate. -/
def ObjectDurable (a : ATheory) (s : ModelState) (e : XState) (o : Obj) : Prop :=
  ∃ w, ∀ x, a.storage.memberW x w = true → s.admission.protocol.storage.live x = true →
    e.ocert x o = true

/-- Physical readiness of a catalogue record: its commit certificate, its manifest
certificate and every payload certificate are durable. Reads live replicas only. -/
def CatReady (a : ATheory) (r : RTheory) (s : ModelState) (e : XState) (c : record) : Prop :=
  RecordDurable a s e c ∧ ObjectDurable a s e (.manifest (r.image c)) ∧
    ∀ d, a.registry.contents (r.image c) d = true → ObjectDurable a s e (.payload d)

/-- A step that makes a record committed (commit or adoption) needs `CatReady`. -/
def AdoptGuard (a : ATheory) (r : RTheory) (s : ModelState) (e : XState) (t : ModelState) : Prop :=
  ∀ c, s.recovery.committed c = false → t.recovery.committed c = true → CatReady a r s e c

/-- Write `c`'s commit certificate on `x`, recording the fence it was checked against. -/
def putRecord (e : XState) (x : replica) (c : record) (k : Nat) : XState :=
  { e with
    rcert := fun x' c' => if x' = x ∧ c' = c then true else e.rcert x' c'
    certFence := fun c' => if c' = c then some k else e.certFence c' }

def putObject (e : XState) (x : replica) (o : Obj) : XState :=
  { e with ocert := fun x' o' => if x' = x ∧ o' = o then true else e.ocert x' o' }

/-- Extra-only certificate writes. A commit certificate is a conditional write on
the fence register: the record's token rank equals the current fence. The writer
writes it after its own Ack of the record bytes. Object certificates follow the
writer's Ack of the object and are not fenced. -/
inductive CertStep (r : RTheory) (encode : record → Nat) (recordToken : RecordToken record token)
    (s : ModelState) (e : XState) : XState → Prop where
  | record (x : replica) (c : record) : s.admission.protocol.storage.live x = true →
      s.admission.protocol.storage.acknowledged (.catalog (encode c)) = true →
      r.tokenRank (recordToken c) = s.recovery.fence →
      CertStep r encode recordToken s e (putRecord e x c s.recovery.fence)
  | object (x : replica) (o : Obj) : s.admission.protocol.storage.live x = true →
      s.admission.protocol.storage.acknowledged o = true →
      CertStep r encode recordToken s e (putObject e x o)

def Guard (a : ATheory) (r : RTheory) (encode : record → Nat) (recordToken : RecordToken record token)
    (s : ModelState) (e : XState) (t : ModelState) (e' : XState) : Prop :=
  (AdoptGuard a r s e t ∧ e' = clearLost s t e) ∨ (t = s ∧ CertStep r encode recordToken s e e')

def Next (a : ATheory) (r : RTheory) (encode : record → Nat) (recordToken : RecordToken record token)
    (p q : ModelState × XState) : Prop :=
  ParaleanProtocol.Next a r encode p.1 q.1 ∧ Guard a r encode recordToken p.1 p.2 q.1 q.2

def Initial (a : ATheory) (r : RTheory) (p : ModelState × XState) : Prop :=
  ParaleanCompletionRecovery.Initial a r p.1 ∧ p.2 = initExtra

inductive Reachable (a : ATheory) (r : RTheory) (encode : record → Nat) (recordToken : RecordToken record token) :
    ModelState × XState → Prop where
  | initial {p} : Initial a r p → Reachable a r encode recordToken p
  | step {p q} : Reachable a r encode recordToken p → Next a r encode recordToken p q →
      Reachable a r encode recordToken q

theorem clearLost_same (s t : ModelState) (e : XState)
    (h : s.admission.protocol.storage.live = t.admission.protocol.storage.live) :
    clearLost s t e = e := by
  cases e with
  | mk rc oc cf =>
    simp only [clearLost, Extra.mk.injEq, and_true]
    rw [← h]
    constructor <;> funext x y <;> cases s.admission.protocol.storage.live x <;> simp

theorem guard_stutter (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : RecordToken record token) (s : ModelState) (e : XState) :
    Guard a r encode recordToken s e s e := by
  refine Or.inl ⟨?_, (clearLost_same s s e rfl).symm⟩
  intro c h1 h2; rw [h1] at h2; cases h2

theorem reachable_protocol (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : RecordToken record token)
    {p : ModelState × XState} (h : Reachable a r encode recordToken p) :
    ParaleanProtocol.Reachable a r encode p.1 := by
  induction h with
  | initial hi => exact .initial hi.1
  | step _ ht ih => exact .step ih ht.1

/-! The certificate invariant. -/

def Inv (a : ATheory) (r : RTheory) (encode : record → Nat) (recordToken : RecordToken record token)
    (p : ModelState × XState) : Prop :=
  (∀ x c, p.2.rcert x c = true →
    p.1.admission.protocol.storage.acknowledged (.catalog (encode c)) = true ∧
    p.2.certFence c = some (r.tokenRank (recordToken c))) ∧
  (∀ x o, p.2.ocert x o = true → p.1.admission.protocol.storage.acknowledged o = true) ∧
  (∀ c k, p.2.certFence c = some k → k = r.tokenRank (recordToken c) ∧ k ≤ p.1.recovery.fence) ∧
  (∀ c, p.1.recovery.committed c = true → CatReady a r p.1 p.2 c) ∧
  (∀ c, p.1.recovery.committed c = true → p.2.certFence c = some (r.tokenRank (recordToken c)))

theorem initial_committed_empty (a : ATheory) (r : RTheory) {s : ModelState}
    (hi : ParaleanCompletionRecovery.Initial a r s) : ∀ c, s.recovery.committed c = false := by
  have h := hi.2
  obtain ⟨ad, rec⟩ := s
  dsimp [ParaleanRecovery.RecoveryInit, ParaleanRecovery.Init, ParaleanRecovery.initializer.ext.tr,
    getFrom, setIn, readFrom, Veil.FieldRepresentation.get, instIsSubStateOfRefl,
    instIsSubReaderOfRefl, ParaleanRecovery.canonicalFieldRep,
    Veil.canonicalFieldRepresentation] at h
  subst rec
  intro c
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

theorem inv_initial (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : RecordToken record token)
    {p : ModelState × XState} (hi : Initial a r p) : Inv a r encode recordToken p := by
  rcases p with ⟨s, e⟩
  rcases hi with ⟨hi, he⟩
  dsimp at he
  subst he
  have hc := initial_committed_empty a r hi
  refine ⟨fun _ _ h => by simp [initExtra] at h, fun _ _ h => by simp [initExtra] at h,
    fun _ _ h => by simp [initExtra] at h, fun c h => ?_, fun c h => ?_⟩ <;>
    (dsimp at h; rw [hc c] at h; cases h)

/-- Some member of every write quorum is live (the failure envelope and `meet`). -/
theorem write_quorum_has_live (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a) {s : ModelState}
    (hs : ParaleanProtocol.Reachable a r encode s) (w : writeQuorum) :
    ∃ x, a.storage.memberW x w = true ∧ s.admission.protocol.storage.live x = true := by
  have hsafe := ParaleanPublicationDiscovery.reachable_safe _ ha.2.1
    (ParaleanProtocol.reachable_discovery a r encode hs)
  obtain ⟨q, hq⟩ := ParaleanPublicationDiscovery.surviving_scan_exists _ _ hsafe
  have hm := ha.2.1.2 w q
  exact ⟨_, hm.1, hq _ hm.2⟩

theorem recordDurable_transfer (a : ATheory) {s t : ModelState} {e : XState} {c : record}
    (hmono : ∀ x, t.admission.protocol.storage.live x = true → s.admission.protocol.storage.live x = true)
    (h : RecordDurable a s e c) : RecordDurable a t (clearLost s t e) c := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w, fun x hx hl => ?_⟩
  simp only [clearLost]
  rw [if_neg (by simp [hl])]
  exact hw x hx (hmono x hl)

theorem objectDurable_transfer (a : ATheory) {s t : ModelState} {e : XState} {o : Obj}
    (hmono : ∀ x, t.admission.protocol.storage.live x = true → s.admission.protocol.storage.live x = true)
    (h : ObjectDurable a s e o) : ObjectDurable a t (clearLost s t e) o := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w, fun x hx hl => ?_⟩
  simp only [clearLost]
  rw [if_neg (by simp [hl])]
  exact hw x hx (hmono x hl)

theorem catReady_transfer (a : ATheory) (r : RTheory) {s t : ModelState} {e : XState} {c : record}
    (hmono : ∀ x, t.admission.protocol.storage.live x = true → s.admission.protocol.storage.live x = true)
    (h : CatReady a r s e c) : CatReady a r t (clearLost s t e) c :=
  ⟨recordDurable_transfer a hmono h.1, objectDurable_transfer a hmono h.2.1,
    fun d hd => objectDurable_transfer a hmono (h.2.2 d hd)⟩

theorem catReady_putRecord (a : ATheory) (r : RTheory) {s : ModelState} {e : XState}
    (x0 : replica) (c0 : record) (k : Nat) {c : record} (h : CatReady a r s e c) :
    CatReady a r s (putRecord e x0 c0 k) c := by
  obtain ⟨⟨w, hw⟩, hm, hp⟩ := h
  refine ⟨⟨w, fun x hx hl => ?_⟩, hm, hp⟩
  simp only [putRecord]
  split_ifs
  · rfl
  · exact hw x hx hl

theorem catReady_putObject (a : ATheory) (r : RTheory) {s : ModelState} {e : XState}
    (x0 : replica) (o0 : Obj) {c : record} (h : CatReady a r s e c) :
    CatReady a r s (putObject e x0 o0) c := by
  have hob : ∀ o, ObjectDurable a s e o → ObjectDurable a s (putObject e x0 o0) o := by
    rintro o ⟨w, hw⟩
    refine ⟨w, fun x hx hl => ?_⟩
    simp only [putObject]
    split_ifs
    · rfl
    · exact hw x hx hl
  exact ⟨h.1, hob _ h.2.1, fun d hd => hob _ (h.2.2 d hd)⟩

theorem inv_step (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : RecordToken record token) (ha : ParaleanAdmission.Assumptions a)
    {p p' : ModelState × XState} (hr : Reachable a r encode recordToken p)
    (hinv : Inv a r encode recordToken p) (ht : Next a r encode recordToken p p') :
    Inv a r encode recordToken p' := by
  rcases p with ⟨s, e⟩
  rcases p' with ⟨t, e'⟩
  rcases ht with ⟨hb, hg⟩
  dsimp only at hb hg
  obtain ⟨hI1, hI2, hI3, hI4, hI5⟩ := hinv
  dsimp only at hI1 hI2 hI3 hI4 hI5
  have mono := ParaleanAckCertificates.protocol_storage_mono a r encode hb
  have fmono := ParaleanCatalogFencing.fence_mono a r encode hb
  have hbase := reachable_protocol a r encode recordToken hr
  rcases hg with ⟨hadopt, he'⟩ | ⟨hts, hcs⟩
  · subst he'
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x c hc
      dsimp [clearLost] at hc
      split_ifs at hc
      exact ⟨mono.2 _ (hI1 x c hc).1, (hI1 x c hc).2⟩
    · intro x o hc
      dsimp [clearLost] at hc
      split_ifs at hc
      exact mono.2 _ (hI2 x o hc)
    · intro c k hk
      obtain ⟨h1, h2⟩ := hI3 c k hk
      exact ⟨h1, Nat.le_trans h2 fmono⟩
    · intro c hc
      by_cases hsc : s.recovery.committed c = true
      · exact catReady_transfer a r mono.1 (hI4 c hsc)
      · exact catReady_transfer a r mono.1 (hadopt c (by simpa using hsc) hc)
    · intro c hc
      by_cases hsc : s.recovery.committed c = true
      · exact hI5 c hsc
      · obtain ⟨⟨w, hw⟩, _⟩ := hadopt c (by simpa using hsc) hc
        obtain ⟨x, hx, hl⟩ := write_quorum_has_live a r encode ha hbase w
        exact (hI1 x c (hw x hx hl)).2
  · subst hts
    cases hcs with
    | record x0 c0 hl hack hf =>
      refine ⟨?_, hI2, ?_, ?_, ?_⟩
      · intro x c hc
        dsimp [putRecord] at hc ⊢
        by_cases hc0 : c = c0
        · subst hc0
          rw [if_pos rfl, hf]
          exact ⟨hack, rfl⟩
        · rw [if_neg hc0]
          rw [if_neg (by simp [hc0])] at hc
          exact hI1 x c hc
      · intro c k hk
        dsimp [putRecord] at hk
        split_ifs at hk with hc0
        · subst hc0; cases hk; exact ⟨hf.symm, Nat.le_refl _⟩
        · exact hI3 c k hk
      · intro c hc
        exact catReady_putRecord a r x0 c0 _ (hI4 c hc)
      · intro c hc
        dsimp [putRecord]
        split_ifs with hc0
        · subst hc0; rw [hf]
        · exact hI5 c hc
    | object x0 o0 hl hack =>
      refine ⟨hI1, ?_, hI3, fun c hc => catReady_putObject a r x0 o0 (hI4 c hc), hI5⟩
      intro x o hc
      dsimp [putObject] at hc
      split_ifs at hc with h0
      · obtain ⟨_, rfl⟩ := h0; exact hack
      · exact hI2 x o hc

theorem reachable_inv (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : RecordToken record token) (ha : ParaleanAdmission.Assumptions a)
    {p : ModelState × XState} (hr : Reachable a r encode recordToken p) :
    Inv a r encode recordToken p := by
  induction hr with
  | initial hi => exact inv_initial a r encode recordToken hi
  | step hr ht ih => exact inv_step a r encode recordToken ha hr ih ht

/-! Fencing of commit records. -/

/-- Every commit certificate on any replica was written while the record's token
rank was the fence. -/
theorem record_cert_fenced (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : RecordToken record token) (ha : ParaleanAdmission.Assumptions a)
    {p : ModelState × XState} (hr : Reachable a r encode recordToken p)
    (x : replica) (c : record) (hc : p.2.rcert x c = true) :
    p.2.certFence c = some (r.tokenRank (recordToken c)) ∧
      r.tokenRank (recordToken c) ≤ p.1.recovery.fence := by
  have hi := reachable_inv a r encode recordToken ha hr
  have h := (hi.1 x c hc).2
  exact ⟨h, (hi.2.2.1 c _ h).2⟩

/-- Every committed record (by the writer's commit or by recovery adoption) has a
commit certificate written while its token rank was the fence. -/
theorem committed_fenced (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : RecordToken record token) (ha : ParaleanAdmission.Assumptions a)
    {p : ModelState × XState} (hr : Reachable a r encode recordToken p)
    (c : record) (hc : p.1.recovery.committed c = true) :
    p.2.certFence c = some (r.tokenRank (recordToken c)) ∧
      r.tokenRank (recordToken c) ≤ p.1.recovery.fence := by
  have hi := reachable_inv a r encode recordToken ha hr
  have h := hi.2.2.2.2 c hc
  exact ⟨h, (hi.2.2.1 c _ h).2⟩

/-- The usual fencing statement: a selected record was committed while its writer
held the fence (its commit certificate passed the fence check). -/
theorem selected_fenced (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : RecordToken record token) (ha : ParaleanAdmission.Assumptions a)
    (hra : ParaleanRecovery.CoupledAssumptions (ParaleanRecovery.ofAdmission a r encode))
    {p : ModelState × XState} (hr : Reachable a r encode recordToken p)
    (hsel : p.1.recovery.selected = true) :
    p.2.certFence p.1.recovery.selectedRecord =
        some (r.tokenRank (recordToken p.1.recovery.selectedRecord)) ∧
      r.tokenRank (recordToken p.1.recovery.selectedRecord) ≤ p.1.recovery.fence := by
  have hs := (ParaleanProtocol.reachable_safe a r encode ha hra (reachable_protocol a r encode recordToken hr)).1
  have hb := ParaleanRecovery.selected_record_backed r p.1.recovery hs.2.1 hsel
  exact committed_fenced a r encode recordToken ha hr _ hb.1

/-- The fence check is load-bearing in the step relation: a commit certificate for
a record whose token rank is not the fence is not a certificate step. -/
theorem stale_record_cert_rejected (r : RTheory) (encode : record → Nat)
    (recordToken : RecordToken record token) (s : ModelState) (e e' : XState) (c : record)
    (hstale : r.tokenRank (recordToken c) ≠ s.recovery.fence)
    (hnew : e'.certFence c ≠ e.certFence c) : ¬ CertStep r encode recordToken s e e' := by
  intro h
  cases h with
  | record x c0 _ _ hf =>
    apply hnew
    dsimp [putRecord]
    split_ifs with hc
    · subst hc; exact absurd hf hstale
    · rfl
  | object x o _ _ => exact hnew rfl

/-- Once the fence has passed a record's token rank, a record without a commit
certificate never gets one, so it is never committed or adopted afterwards. -/
theorem stale_stays_uncertified (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : RecordToken record token)
    {p q : ModelState × XState} (ht : Next a r encode recordToken p q) (c : record)
    (hstale : r.tokenRank (recordToken c) < p.1.recovery.fence)
    (hnone : p.2.certFence c = none) :
    q.2.certFence c = none ∧ r.tokenRank (recordToken c) < q.1.recovery.fence := by
  rcases p with ⟨s, e⟩
  rcases q with ⟨t, e'⟩
  rcases ht with ⟨hb, hg⟩
  dsimp only at hb hg hstale hnone ⊢
  have fmono := ParaleanCatalogFencing.fence_mono a r encode hb
  refine ⟨?_, Nat.lt_of_lt_of_le hstale fmono⟩
  rcases hg with ⟨_, rfl⟩ | ⟨rfl, hcs⟩
  · exact hnone
  · cases hcs with
    | record x c0 _ _ hf =>
      dsimp [putRecord]
      split_ifs with hc
      · subst hc; omega
      · exact hnone
    | object x o _ _ => exact hnone

/-- A record without a commit certificate is not committed. -/
theorem uncertified_not_committed (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : RecordToken record token) (ha : ParaleanAdmission.Assumptions a)
    {p : ModelState × XState} (hr : Reachable a r encode recordToken p)
    (c : record) (hnone : p.2.certFence c = none) : p.1.recovery.committed c = false := by
  cases hc : p.1.recovery.committed c
  · rfl
  · have := (committed_fenced a r encode recordToken ha hr c hc).1
    rw [hnone] at this; cases this

/-! Soundness of the physical readiness test. -/

/-- `CatReady` implies the base readiness test (`StorageReady`), which reads
ghost acknowledgements. The base guard of `enumerate` is discharged physically. -/
theorem catReady_storageReady (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : RecordToken record token) (ha : ParaleanAdmission.Assumptions a)
    {p : ModelState × XState} (hr : Reachable a r encode recordToken p)
    (c : record) (h : CatReady a r p.1 p.2 c) :
    ParaleanRecovery.StorageReady (ParaleanRecovery.ofAdmission a r encode).base
      p.1.admission.protocol.storage ((ParaleanRecovery.ofAdmission a r encode).recordObject c) (r.image c) := by
  have hi := reachable_inv a r encode recordToken ha hr
  have hbase := reachable_protocol a r encode recordToken hr
  obtain ⟨⟨w, hw⟩, ⟨wm, hwm⟩, hp⟩ := h
  obtain ⟨x, hx, hl⟩ := write_quorum_has_live a r encode ha hbase w
  obtain ⟨xm, hxm, hlm⟩ := write_quorum_has_live a r encode ha hbase wm
  refine ⟨(hi.1 x c (hw x hx hl)).1, hi.2.1 xm _ (hwm xm hxm hlm), ?_⟩
  intro d hd
  obtain ⟨wp, hwp⟩ := hp d hd
  obtain ⟨xp, hxp, hlp⟩ := write_quorum_has_live a r encode ha hbase wp
  exact hi.2.1 xp _ (hwp xp hxp hlp)

/-- Every committed record is certified; certification survives any later loss
allowed by the failure envelope. -/
theorem committed_catReady (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : RecordToken record token) (ha : ParaleanAdmission.Assumptions a)
    {p : ModelState × XState} (hr : Reachable a r encode recordToken p)
    (c : record) (hc : p.1.recovery.committed c = true) : CatReady a r p.1 p.2 c :=
  (reachable_inv a r encode recordToken ha hr).2.2.2.1 c hc


/-! Concrete certificate scan and recovery adequacy. -/

/-- The recovery theory's scan type can carry any decode/readiness pair. This is a
property of the scan representation, not of any state. -/
structure ScanCodec (r : RTheory) where
  build : (record → Bool) → (record → Bool) → scan
  decoded_build : ∀ D R c, r.decoded (build D R) c = D c
  ready_build : ∀ D R c, r.ready (build D R) c = R c

/-- The scan value recovery computes from the store at read quorum `q`: decoded =
the record's bytes are on a live member of `q`; ready = `CatReady`. -/
def certScanValue {r : RTheory} (codec : ScanCodec r) (a : ATheory) (encode : record → Nat)
    (s : ModelState) (e : XState) (q : readQuorum) : scan :=
  codec.build
    (fun c => decide (ParaleanRecovery.QuorumCatalog (ParaleanRecovery.ofAdmission a r encode).base
      s.admission.protocol.storage q ((ParaleanRecovery.ofAdmission a r encode).recordObject c)))
    (fun c => decide (CatReady a r s e c))

/-- The concrete scan of a fully live read quorum covers every committed record. -/
theorem certScanValue_covers (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : RecordToken record token) (ha : ParaleanAdmission.Assumptions a)
    (hra : ParaleanRecovery.CoupledAssumptions (ParaleanRecovery.ofAdmission a r encode))
    (codec : ScanCodec r) {s : ModelState} {e : XState}
    (hr : Reachable a r encode recordToken (s, e))
    (q : readQuorum) (hq : ∀ x, a.storage.memberR x q = true → s.admission.protocol.storage.live x = true)
    (c : record) (hc : s.recovery.committed c = true) :
    r.decoded (certScanValue codec a encode s e q) c = true ∧
      r.ready (certScanValue codec a encode s e q) c = true := by
  have hsafe := (ParaleanProtocol.reachable_safe a r encode ha hra (reachable_protocol a r encode recordToken hr)).1.2
  refine ⟨?_, ?_⟩
  · simp only [certScanValue, codec.decoded_build, decide_eq_true_eq]
    have hk := hsafe.2.2.1 c hc
    have hw := ParaleanGroupComposition.acknowledged_recoverable
      (ParaleanRecovery.ofAdmission a r encode).base s.admission.protocol.storage hra.1 hsafe.2.1
      _ q hk hq
    have hm := hra.1 (s.admission.protocol.storage.witness
      ((ParaleanRecovery.ofAdmission a r encode).recordObject c)) q
    exact ⟨_, hm.2, hw⟩
  · simp only [certScanValue, codec.ready_build, decide_eq_true_eq]
    exact committed_catReady a r encode recordToken ha hr c hc

/-- A record the concrete scan marks ready passes the base (ghost) readiness test. -/
theorem certScanValue_sound (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : RecordToken record token) (ha : ParaleanAdmission.Assumptions a)
    (codec : ScanCodec r) {s : ModelState} {e : XState}
    (hr : Reachable a r encode recordToken (s, e)) (q : readQuorum) (c : record)
    (h : r.ready (certScanValue codec a encode s e q) c = true) :
    ParaleanRecovery.StorageReady (ParaleanRecovery.ofAdmission a r encode).base
      s.admission.protocol.storage ((ParaleanRecovery.ofAdmission a r encode).recordObject c) (r.image c) := by
  simp only [certScanValue, codec.ready_build, decide_eq_true_eq] at h
  exact catReady_storageReady a r encode recordToken ha hr c h

/-- Lift a base step that changes neither storage nor `committed` into this layer. -/
theorem lift_quiet {a : ATheory} {r : RTheory} {encode : record → Nat}
    {recordToken : RecordToken record token} {s t : ModelState} {e : XState}
    (hb : ParaleanProtocol.Next a r encode s t)
    (hc : t.recovery.committed = s.recovery.committed)
    (hl : s.admission.protocol.storage.live = t.admission.protocol.storage.live) :
    Next a r encode recordToken (s, e) (t, e) := by
  refine ⟨hb, Or.inl ⟨?_, (clearLost_same s t e hl).symm⟩⟩
  intro c h1 h2
  rw [hc, h1] at h2
  cases h2

/-- Certified recovery adequacy. From any reachable state and any fully live read
quorum, recovery reads the store into the concrete certificate scan, enumerates,
reconstructs and selects any committed record in three hardened steps. No scan
value or readiness oracle is assumed; adoption needs only certificates. -/
theorem certified_recovery (a : ATheory) (r : RTheory) (encode : record → Nat)
    (recordToken : RecordToken record token) (ha : ParaleanAdmission.Assumptions a)
    (hra : ParaleanRecovery.CoupledAssumptions (ParaleanRecovery.ofAdmission a r encode))
    (codec : ScanCodec r) {s : ModelState} {e : XState}
    (hr : Reachable a r encode recordToken (s, e))
    (q : readQuorum) (hq : ∀ x, a.storage.memberR x q = true → s.admission.protocol.storage.live x = true)
    (c : record) (hc : s.recovery.committed c = true) :
    ∃ s₁ s₂ s₃ : ModelState,
      Next a r encode recordToken (s, e) (s₁, e) ∧ Next a r encode recordToken (s₁, e) (s₂, e) ∧
      Next a r encode recordToken (s₂, e) (s₃, e) ∧
      ParaleanRecovery.RecoveryNext r s.recovery (.enumerate (certScanValue codec a encode s e q)) s₁.recovery ∧
      (∀ d, s₁.recovery.known d = true → CatReady a r s e d) ∧
      s₃.recovery.selected = true ∧ s₃.recovery.selectedRecord = c ∧
      s₃.recovery.writer = s.recovery.writer ∧ s₃.recovery.fence = s.recovery.fence ∧
      s₁.admission = s.admission ∧ s₂.admission = s.admission ∧ s₃.admission = s.admission := by
  let cr := ParaleanRecovery.ofAdmission a r encode
  let view := ParaleanCompletionRecovery.recoveryView s
  let v := certScanValue codec a encode s e q
  have safe := (ParaleanProtocol.reachable_safe a r encode ha hra (reachable_protocol a r encode recordToken hr)).1.2
  have hcover := certScanValue_covers a r encode recordToken ha hra codec hr q hq
  have hsound := certScanValue_sound a r encode recordToken ha codec hr q
  have hadm := ParaleanRecovery.committed_admissible_of_cover cr view safe v hcover c hc
  obtain ⟨rec₁, ht₁, label₁, scanned, writer₁, fence₁, known₁, committed₁⟩ :=
    ParaleanRecovery.enumeration_enabled_of_cover cr view v hcover hsound
  let s₁ : ModelState := ⟨s.admission, rec₁⟩
  have hready : ∀ d, ParaleanRecovery.admissible v d r s.recovery → CatReady a r s e d := by
    intro d hd
    have h := hd.2.1
    simp only [v, certScanValue, codec.ready_build, decide_eq_true_eq] at h
    exact h
  have step₁ : Next a r encode recordToken (s, e) (s₁, e) := by
    refine ⟨ParaleanProtocol.recovery_step a r encode s.admission s.recovery rec₁ ht₁,
      Or.inl ⟨?_, (clearLost_same _ _ e rfl).symm⟩⟩
    intro d h1 h2
    rcases (committed₁ d).1 h2 with h | h
    · have h1' : s.recovery.committed d = false := h1
      have h' : s.recovery.committed d = true := h
      rw [h1'] at h'; cases h'
    · exact hready d h
  have hk : s₁.recovery.known c = true := (known₁ c).2 hadm
  obtain ⟨v₂, ht₂, label₂, reconstructed, known₂, writer₂, fence₂, disk₂⟩ :=
    ParaleanRecovery.reconstruction_enabled_for_known_record cr (ParaleanCompletionRecovery.recoveryView s₁) c scanned hk
  have hv₂ : v₂ = ⟨v₂.recovery, s.admission.protocol.storage⟩ := by
    cases v₂; simp only at disk₂ ⊢; rw [disk₂]; rfl
  let s₂ : ModelState := ⟨s.admission, v₂.recovery⟩
  have step₂ : Next a r encode recordToken (s₁, e) (s₂, e) := by
    rw [hv₂] at ht₂
    exact lift_quiet (ParaleanProtocol.recovery_step a r encode s.admission rec₁ v₂.recovery ht₂)
      (ParaleanRecovery.reconstruct_committed_same r label₂) rfl
  obtain ⟨v₃, ht₃, label₃, selected, exactRecord, writer₃, fence₃, disk₃⟩ :=
    ParaleanRecovery.historical_enabled_for_known_record cr (ParaleanCompletionRecovery.recoveryView s₂) c
      reconstructed known₂
  have hv₃ : v₃ = ⟨v₃.recovery, s.admission.protocol.storage⟩ := by
    cases v₃; simp only at disk₃ ⊢; rw [disk₃]; rfl
  let s₃ : ModelState := ⟨s.admission, v₃.recovery⟩
  have step₃ : Next a r encode recordToken (s₂, e) (s₃, e) := by
    rw [hv₃] at ht₃
    exact lift_quiet (ParaleanProtocol.recovery_step a r encode s.admission v₂.recovery v₃.recovery ht₃)
      (ParaleanRecovery.historical_committed_same r c label₃) rfl
  refine ⟨s₁, s₂, s₃, step₁, step₂, step₃, label₁, fun d hd => hready d ((known₁ d).1 hd),
    selected, exactRecord, ?_, ?_, rfl, rfl, rfl⟩
  · exact writer₃.trans (writer₂.trans writer₁)
  · exact fence₃.trans (fence₂.trans fence₁)

end
#print axioms inv_step
#print axioms record_cert_fenced
#print axioms committed_fenced
#print axioms selected_fenced
#print axioms stale_record_cert_rejected
#print axioms stale_stays_uncertified
#print axioms uncertified_not_committed
#print axioms catReady_storageReady
#print axioms committed_catReady
#print axioms certScanValue_covers
#print axioms certScanValue_sound
#print axioms certified_recovery
end ParaleanCatalogCertificates
