import Paralean.Protocol
import Paralean.ProtocolExecution

/-! Durable, physically readable publication-acknowledgement certificates.
`ParaleanPublicationDiscovery` accepts a scanned marker by reading Durability's
ghost `acknowledged` flag. A real store cannot read that flag: after replica loss a
surviving staged marker and a surviving acknowledged marker have the same bytes.

This layer adds two pieces of state. `cert r d` is a per-replica durable
certificate record: physical store state, readable by a scan, erased when `r` is
lost. `certReply n d r` is node `n`'s own record that replica `r` acknowledged its
certificate write for `d`: it lives at the writer, not in the store, so it
persists after `r` is lost. Replies are collected one `put` at a time; there is
no step that needs a whole write quorum live at one instant.

A receive of an already-published group needs a physical certificate read on a
live replica of some read quorum. A head change of node `n` needs, for every
checkpoint group, a write quorum of `n`'s own certificate replies. Neither guard
reads ghost state. Object constructors of `ParaleanArtifacts.Object` are unchanged. -/
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ParaleanAckCertificates
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

/-- `cert` is physical store state on replicas. `certReply n d r` is writer `n`'s
local record of a received acknowledgement from replica `r`; it is not store state
and is not erased by the loss of `r`. -/
structure Extra (node replica group : Type) where
  cert : replica → group → Bool
  certReply : node → group → replica → Bool

local notation "XState" => Extra node replica group

def initExtra : Extra node replica group :=
  ⟨fun _ _ => false, fun _ _ _ => false⟩

/-- A replica that goes from live to lost loses its certificate records. Writers'
reply records are untouched. -/
def clearLost (s t : ModelState) (e : XState) : XState :=
  { e with cert := fun r d =>
      if s.admission.protocol.storage.live r = true ∧ t.admission.protocol.storage.live r = false
      then false else e.cert r d }

/-- Writer `n` stores a certificate for `d` on replica `r` and records `r`'s reply. -/
def putCert (e : XState) (n : node) (r : replica) (d : group) : XState :=
  { cert := fun r' d' => if r' = r ∧ d' = d then true else e.cert r' d'
    certReply := fun n' d' r' => if n' = n ∧ d' = d ∧ r' = r then true else e.certReply n' d' r' }

/-- Node `n` holds replies for `d` from every member of some write quorum. The
replies may have been collected at different times; members may since be lost. -/
def CertQuorumBy (a : ATheory) (e : XState) (n : node) (d : group) : Prop :=
  ∃ w, ∀ r, a.storage.memberW r w = true → e.certReply n d r = true

/-- Some writer holds a certificate quorum for `d`. -/
def CertQuorum (a : ATheory) (e : XState) (d : group) : Prop :=
  ∃ n, CertQuorumBy a e n d

/-- What a discovery scan physically reads: a certificate on a live replica of a quorum. -/
def CertEvidence (a : ATheory) (s : ModelState) (e : XState) (d : group) : Prop :=
  ∃ q r, a.storage.memberR r q = true ∧ s.admission.protocol.storage.live r = true ∧
    e.cert r d = true

/-- Physical certificate scan of quorum `q`. -/
def certScan (a : ATheory) (s : ModelState) (e : XState) (q : readQuorum) : group → Prop :=
  fun d => ∃ r, a.storage.memberR r q = true ∧ s.admission.protocol.storage.live r = true ∧
    e.cert r d = true

/-- New knowledge of an already-published group needs a physical certificate read.
(A first publish has `published d = false` in the pre-state and is not affected.) -/
def ReceiveGuard (a : ATheory) (s : ModelState) (e : XState) (t : ModelState) : Prop :=
  ∀ n d, s.admission.protocol.registry.known n d = false →
    t.admission.protocol.registry.known n d = true →
    s.admission.protocol.registry.published d = true → CertEvidence a s e d

/-- A head change of node `n` needs, for every checkpoint group, a write quorum of
`n`'s own certificate replies. -/
def CommitGuard (a : ATheory) (s : ModelState) (e : XState) (t : ModelState) : Prop :=
  ∀ n, t.admission.protocol.registry.head n ≠ s.admission.protocol.registry.head n →
    ∀ d, a.registry.contents (t.admission.protocol.registry.head n) d = true → CertQuorumBy a e n d

/-- Extra-only certificate step: writer `n`, which knows `d`, stores a certificate
on live replica `r` and receives the reply. -/
inductive CertStep (a : ATheory) (s : ModelState) (e : XState) : XState → Prop where
  | put (n : node) (r : replica) (d : group) : s.admission.protocol.storage.live r = true →
      s.admission.protocol.registry.known n d = true → CertStep a s e (putCert e n r d)

def Guard (a : ATheory) (r : RTheory) (encode : record → Nat)
    (s : ModelState) (e : XState) (t : ModelState) (e' : XState) : Prop :=
  (ReceiveGuard a s e t ∧ CommitGuard a s e t ∧ e' = clearLost s t e) ∨
  (t = s ∧ CertStep a s e e')

def Next (a : ATheory) (r : RTheory) (encode : record → Nat)
    (p p' : ModelState × XState) : Prop :=
  ParaleanProtocol.Next a r encode p.1 p'.1 ∧ Guard a r encode p.1 p.2 p'.1 p'.2

def Initial (a : ATheory) (r : RTheory) (p : ModelState × XState) : Prop :=
  ParaleanCompletionRecovery.Initial a r p.1 ∧ p.2 = initExtra

inductive Reachable (a : ATheory) (r : RTheory) (encode : record → Nat) :
    ModelState × XState → Prop where
  | initial {p} : Initial a r p → Reachable a r encode p
  | step {p p'} : Reachable a r encode p → Next a r encode p p' → Reachable a r encode p'

/-- Base stutter: carries the extra-only certificate steps. -/
theorem protocol_stutter (a : ATheory) (r : RTheory) (encode : record → Nat) (s : ModelState) :
    ParaleanProtocol.Next a r encode s s := by
  cases s with
  | mk ad rec => exact .paired (.admission .stutter rfl) .stutter

theorem clearLost_same (s t : ModelState) (e : XState)
    (h : s.admission.protocol.storage.live = t.admission.protocol.storage.live) :
    clearLost s t e = e := by
  cases e with
  | mk c rp =>
    simp only [clearLost, Extra.mk.injEq, and_true]
    funext r d
    rw [← h]
    cases s.admission.protocol.storage.live r <;> simp

theorem guard_stutter (a : ATheory) (r : RTheory) (encode : record → Nat)
    (s : ModelState) (e : XState) : Guard a r encode s e s e := by
  refine Or.inl ⟨?_, ?_, (clearLost_same s s e rfl).symm⟩
  · intro n d h1 h2; rw [h1] at h2; cases h2
  · intro n h; exact absurd rfl h

theorem reachable_protocol (a : ATheory) (r : RTheory) (encode : record → Nat)
    {p : ModelState × XState} (h : Reachable a r encode p) :
    ParaleanProtocol.Reachable a r encode p.1 := by
  induction h with
  | initial hi => exact .initial hi.1
  | step _ ht ih => exact .step ih ht.1

/-! Storage monotonicity: liveness only decreases, acknowledgements only grow. -/

theorem storage_live_mono (th : Durability.Theory replica (ParaleanAdmission.StoredObject group snapshot) writeQuorum readQuorum)
    (s s' : ParaleanGroupComposition.DiskState replica (ParaleanAdmission.StoredObject group snapshot) writeQuorum readQuorum)
    (label : Durability.Label replica (ParaleanAdmission.StoredObject group snapshot) writeQuorum readQuorum)
    (ht : ParaleanGroupComposition.StorageNext th s label s') :
    ∀ r, s'.live r = true → s.live r = true := by
  cases label <;>
    simp only [ParaleanGroupComposition.StorageNext, Durability.Next, Durability.NextAct,
      Durability.Put.ext.derived_eq, Durability.Ack.ext.derived_eq,
      Durability.Lose.ext.derived_eq] at ht
  all_goals
    dsimp [Durability.Put.ext.tr, Durability.Ack.ext.tr, Durability.Lose.ext.tr,
      getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
      instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanGroupComposition.diskFieldRep,
      Veil.canonicalFieldRepresentation] at ht
    repeat' rcases ht with ⟨ha, ht⟩
    try subst s'
    simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp]
    try grind

theorem discovery_storage_mono
    (th : ParaleanPublicationDiscovery.Theory node group name snapshot replica writeQuorum readQuorum)
    {p p' : ParaleanPublicationDiscovery.State node group name snapshot replica writeQuorum readQuorum}
    (h : ParaleanPublicationDiscovery.Next th p p') :
    (∀ r, p'.storage.live r = true → p.storage.live r = true) ∧
    (∀ o, p.storage.acknowledged o = true → p'.storage.acknowledged o = true) := by
  cases h with
  | publish n d w hp hd _ =>
    exact ⟨storage_live_mono _ _ _ _ hd, ParaleanGroupComposition.storage_acknowledged_mono _ _ _ _ hd⟩
  | registry => exact ⟨fun _ h => h, fun _ h => h⟩
  | storage l _ hd =>
    exact ⟨storage_live_mono _ _ _ _ hd, ParaleanGroupComposition.storage_acknowledged_mono _ _ _ _ hd⟩
  | stutter => exact ⟨fun _ h => h, fun _ h => h⟩

theorem protocol_storage_mono (a : ATheory) (r : RTheory) (encode : record → Nat)
    {s t : ModelState} (ht : ParaleanProtocol.Next a r encode s t) :
    (∀ x, t.admission.protocol.storage.live x = true → s.admission.protocol.storage.live x = true) ∧
    (∀ o, s.admission.protocol.storage.acknowledged o = true →
      t.admission.protocol.storage.acknowledged o = true) :=
  discovery_storage_mono _ (ht.discovery a r encode)

theorem init_head (th : ParaleanGroups.Theory node group name snapshot)
    (rg : ParaleanGroups.CanonicalState node group name snapshot)
    (hr : ParaleanGroups.GroupsInit th rg) : ∀ n, rg.head n = th.emptySnapshot := by
  dsimp [ParaleanGroups.GroupsInit, ParaleanGroups.Init,
    ParaleanGroups.initializer.ext.tr, getFrom, setIn, instIsSubStateOfRefl, readFrom,
    instIsSubReaderOfRefl] at hr
  subst rg
  intro n
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

/-! The certificate invariant. -/

def Inv (a : ATheory) (p : ModelState × XState) : Prop :=
  (∀ r d, p.2.cert r d = true → p.1.admission.protocol.storage.acknowledged (.publication d) = true) ∧
  (∀ n d r, p.2.certReply n d r = true → p.1.admission.protocol.storage.live r = true →
    p.2.cert r d = true) ∧
  (∀ n d, a.registry.contents (p.1.admission.protocol.registry.head n) d = true →
    CertQuorumBy a p.2 n d)

theorem inv_initial (a : ATheory) (r : RTheory) (ha : ParaleanAdmission.Assumptions a)
    {p : ModelState × XState} (hi : Initial a r p) : Inv a p := by
  rcases p with ⟨s, e⟩
  rcases hi with ⟨hi, he⟩
  dsimp at he
  subst he
  unfold Inv
  refine ⟨fun _ _ h => by simp [initExtra] at h, fun _ _ _ h => by simp [initExtra] at h, ?_⟩
  intro n d hc
  have hh := init_head a.registry _ hi.1.2.1 n
  dsimp at hc
  rw [hh] at hc
  exact absurd hc (ha.2.1.1.2.1 d)

theorem certQuorumBy_putCert (a : ATheory) (e : XState) (n0 : node) (x0 : replica) (d0 : group)
    {n : node} {d : group} (h : CertQuorumBy a e n d) : CertQuorumBy a (putCert e n0 x0 d0) n d := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w, fun x hx => ?_⟩
  simp only [putCert]
  split_ifs
  · rfl
  · exact hw x hx

theorem inv_step (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    {p p' : ModelState × XState} (hr : Reachable a r encode p) (hinv : Inv a p)
    (ht : Next a r encode p p') : Inv a p' := by
  rcases p with ⟨s, e⟩
  rcases p' with ⟨t, e'⟩
  rcases ht with ⟨hb, hg⟩
  dsimp only at hb hg
  obtain ⟨hJ1, hJ2, hJ3⟩ := hinv
  dsimp only at hJ1 hJ2 hJ3
  have mono := protocol_storage_mono a r encode hb
  rcases hg with ⟨_, hcommit, he'⟩ | ⟨hts, hcs⟩
  · subst he'
    refine ⟨?_, ?_, ?_⟩
    · intro x d hc
      dsimp [clearLost] at hc
      split_ifs at hc
      exact mono.2 _ (hJ1 x d hc)
    · intro n d x hrep hl
      dsimp [clearLost] at hrep hl ⊢
      rw [if_neg (by simp [hl])]
      exact hJ2 n d x hrep (mono.1 x hl)
    · intro n d hc
      by_cases hh : t.admission.protocol.registry.head n = s.admission.protocol.registry.head n
      · dsimp at hc; rw [hh] at hc
        obtain ⟨w, hw⟩ := hJ3 n d hc
        exact ⟨w, fun x hx => by dsimp [clearLost]; exact hw x hx⟩
      · obtain ⟨w, hw⟩ := hcommit n hh d hc
        exact ⟨w, fun x hx => by dsimp [clearLost]; exact hw x hx⟩
  · subst hts
    have hsafe := ParaleanPublicationDiscovery.reachable_safe _ ha.2.1
      (ParaleanProtocol.reachable_discovery a r encode (reachable_protocol a r encode hr))
    cases hcs with
    | put n0 x0 d0 hl hk =>
      refine ⟨?_, ?_, ?_⟩
      · intro x d hc
        dsimp [putCert] at hc
        split_ifs at hc with heq
        · obtain ⟨_, rfl⟩ := heq
          exact (hsafe.2 d).2 (hsafe.1.1.2.2.1 n0 d hk)
        · exact hJ1 x d hc
      · intro n d x hrep hl'
        dsimp [putCert] at hrep ⊢
        by_cases hxd : x = x0 ∧ d = d0
        · rw [if_pos hxd]
        · rw [if_neg hxd]
          split_ifs at hrep with h2
          · exact absurd ⟨h2.2.2, h2.2.1⟩ hxd
          · exact hJ2 n d x hrep hl'
      · intro n d hc
        exact certQuorumBy_putCert a e n0 x0 d0 (hJ3 n d hc)

theorem reachable_inv (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    {p : ModelState × XState} (hr : Reachable a r encode p) : Inv a p := by
  induction hr with
  | initial hi => exact inv_initial a r ha hi
  | step hr ht ih => exact inv_step a r encode ha hr ih ht

/-! Headline results. -/

/-- A durable certificate is only ever written for a published, acknowledged marker. -/
theorem cert_sound (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    {s : ModelState} {e : XState} (hr : Reachable a r encode (s, e))
    (x : replica) (d : group) (hc : e.cert x d = true) :
    s.admission.protocol.registry.published d = true ∧
      s.admission.protocol.storage.acknowledged (.publication d) = true := by
  have hack := (reachable_inv a r encode ha hr).1 x d hc
  have hsafe := ParaleanPublicationDiscovery.reachable_safe _ ha.2.1
    (ParaleanProtocol.reachable_discovery a r encode (reachable_protocol a r encode hr))
  exact ⟨(hsafe.2 d).1 hack, hack⟩

/-- A replica that replied to a certificate write and is still live still holds
the certificate (liveness only shrinks; only loss erases certificates). -/
theorem reply_survives (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    {s : ModelState} {e : XState} (hr : Reachable a r encode (s, e))
    (n : node) (d : group) (x : replica) (hrep : e.certReply n d x = true)
    (hl : s.admission.protocol.storage.live x = true) : e.cert x d = true :=
  (reachable_inv a r encode ha hr).2.1 n d x hrep hl

/-- A certificate quorum is found by every scan of a fully live read quorum
(at `meet`), however long ago the replies were collected. -/
theorem scan_complete (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    {s : ModelState} {e : XState} (hr : Reachable a r encode (s, e))
    (d : group) (hcq : CertQuorum a e d)
    (q : readQuorum) (hq : ∀ x, a.storage.memberR x q = true → s.admission.protocol.storage.live x = true) :
    certScan a s e q d := by
  obtain ⟨n, w, hw⟩ := hcq
  have hm := ha.2.1.2 w q
  have hl := hq _ hm.2
  exact ⟨_, hm.2, hl, reply_survives a r encode ha hr n d _ (hw _ hm.1) hl⟩

/-- The failure envelope always supplies such a quorum. -/
theorem live_quorum_exists (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    {s : ModelState} {e : XState} (hr : Reachable a r encode (s, e)) :
    ∃ q, ∀ x, a.storage.memberR x q = true → s.admission.protocol.storage.live x = true :=
  ParaleanPublicationDiscovery.surviving_scan_exists _ _
    (ParaleanPublicationDiscovery.reachable_safe _ ha.2.1
      (ParaleanProtocol.reachable_discovery a r encode (reachable_protocol a r encode hr)))

/-- The physical certificate scan `S` of a fully live read quorum is bracketed:
`CertQuorum ⊆ S ⊆ published`. It holds in every reachable state, with or without
worker indexes. A published group without a certificate quorum may be absent. -/
theorem scan_between (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    {s : ModelState} {e : XState} (hr : Reachable a r encode (s, e))
    (q : readQuorum) (hq : ∀ x, a.storage.memberR x q = true → s.admission.protocol.storage.live x = true) :
    ∀ d, (CertQuorum a e d → certScan a s e q d) ∧
      (certScan a s e q d → s.admission.protocol.registry.published d = true) := by
  intro d
  refine ⟨fun hcq => scan_complete a r encode ha hr d hcq q hq, ?_⟩
  rintro ⟨x, _, _, hc⟩
  exact (cert_sound a r encode ha hr x d hc).1

/-- Every checkpoint group of node `n` has a certificate quorum of `n`'s own
replies, hence is found by every fully live read-quorum scan. -/
theorem checkpoint_contents_discoverable (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    {s : ModelState} {e : XState} (hr : Reachable a r encode (s, e))
    (n : node) (d : group)
    (hc : a.registry.contents (s.admission.protocol.registry.head n) d = true) :
    CertQuorumBy a e n d ∧ ∀ q, (∀ x, a.storage.memberR x q = true →
      s.admission.protocol.storage.live x = true) → certScan a s e q d := by
  have hcq := (reachable_inv a r encode ha hr).2.2 n d hc
  exact ⟨hcq, fun q hq => scan_complete a r encode ha hr d ⟨n, hcq⟩ q hq⟩

/-- Soundness of the physical read: it implies the base guard's premises. -/
theorem receive_guard_sound (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    {s : ModelState} {e : XState} (hr : Reachable a r encode (s, e))
    (d : group) (hev : CertEvidence a s e d) :
    s.admission.protocol.registry.published d = true ∧
      s.admission.protocol.storage.acknowledged (.publication d) = true := by
  obtain ⟨_, x, _, _, hc⟩ := hev
  exact cert_sound a r encode ha hr x d hc

theorem receive_effect (th : ParaleanGroups.Theory node group name snapshot)
    (s s' : ParaleanGroups.CanonicalState node group name snapshot) (n : node) (d : group)
    (h : ParaleanGroups.ReceiveStep th s s' n d) :
    (∀ n' d', s.known n' d' = false → s'.known n' d' = true → n' = n ∧ d' = d) ∧
      s'.head = s.head := by
  simp only [ParaleanGroups.ReceiveStep, ParaleanGroups.receive.ext.tr] at h
  dsimp [getFrom, setIn, instIsSubStateOfRefl, Veil.FieldRepresentation.get,
    ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation] at h
  rcases h with ⟨_, _, _, _, hs⟩
  subst s'
  refine ⟨?_, rfl⟩
  intro n' d' h1 h2
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp] at h2
  by_cases hn : n' = n <;> by_cases hd : d' = d <;> simp_all

/-- Implementability: the hardened receive is enabled from the physical
certificate read plus the base non-storage guards (alive, online, not known). -/
theorem receive_guard_physical (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    {s : ModelState} {e : XState} (hr : Reachable a r encode (s, e))
    (n : node) (d : group) (hev : CertEvidence a s e d)
    (alive : s.admission.protocol.registry.alive n = true)
    (online : s.admission.protocol.registry.online n = true)
    (missing : s.admission.protocol.registry.known n d = false) :
    ∃ rg', ParaleanGroups.ReceiveStep a.registry s.admission.protocol.registry rg' n d ∧
      rg'.known n d = true ∧
      Next a r encode (s, e)
        (⟨⟨s.admission.delivery, ⟨rg', s.admission.protocol.storage⟩⟩, s.recovery⟩, e) := by
  have hbase := reachable_protocol a r encode hr
  have hsafe := ParaleanPublicationDiscovery.reachable_safe _ ha.2.1
    (ParaleanProtocol.reachable_discovery a r encode hbase)
  have hpub := (receive_guard_sound a r encode ha hr d hev).1
  obtain ⟨q, hq⟩ := ParaleanPublicationDiscovery.surviving_scan_exists _ _ hsafe
  have hacc := ParaleanPublicationDiscovery.surviving_quorum_coverage _ ha.2.1 _ hsafe q hq _
    (ParaleanPublicationDiscovery.enumerate_physical _ _ q) d hpub
  obtain ⟨rg', ht, hk, hd⟩ := ParaleanPublicationDiscovery.scan_receive_enabled _ _ hsafe q _
    (ParaleanPublicationDiscovery.enumerate_physical _ _ q) n d hacc ⟨alive, online⟩
    (by simp [missing])
  have heff := receive_effect a.registry _ _ n d ht
  refine ⟨rg', ht, hk, ?_, Or.inl ⟨?_, ?_, ?_⟩⟩
  · refine .paired ?_ hd
    refine ParaleanCompletionRecovery.Next.admission ?_ rfl
    apply ParaleanCompletionRecovery.OrdinaryNext.registry (.receive n d) trivial _ trivial
    simpa only [ParaleanGroups.GroupsNext, ParaleanGroups.Next,
      ParaleanGroups.NextAct, ParaleanGroups.receive.ext.derived_eq] using ht
  · intro n' d' h1 h2 _
    obtain ⟨rfl, rfl⟩ := heff.1 n' d' h1 h2
    exact hev
  · intro n' hh
    exact absurd (congrFun heff.2 n') hh
  · exact (clearLost_same _ _ e rfl).symm

/-! Lifting base steps into the hardened model. -/

theorem lift {a : ATheory} {r : RTheory} {encode : record → Nat} {s t : ModelState} {e : XState}
    (hb : ParaleanProtocol.Next a r encode s t) (hr : ReceiveGuard a s e t) (hc : CommitGuard a s e t)
    (hl : s.admission.protocol.storage.live = t.admission.protocol.storage.live) :
    Next a r encode (s, e) (t, e) :=
  ⟨hb, Or.inl ⟨hr, hc, (clearLost_same s t e hl).symm⟩⟩

theorem lift_registry {a : ATheory} {r : RTheory} {encode : record → Nat} {s t : ModelState} {e : XState}
    (hb : ParaleanProtocol.Next a r encode s t)
    (hreg : t.admission.protocol.registry = s.admission.protocol.registry) :
    Next a r encode (s, e) (t, clearLost s t e) := by
  refine ⟨hb, Or.inl ⟨?_, ?_, rfl⟩⟩
  · intro n d h1 h2 _; rw [hreg, h1] at h2; cases h2
  · intro n h; rw [hreg] at h; exact absurd rfl h

theorem lift_same {a : ATheory} {r : RTheory} {encode : record → Nat} {s t : ModelState} {e : XState}
    (hb : ParaleanProtocol.Next a r encode s t)
    (hreg : t.admission.protocol.registry = s.admission.protocol.registry)
    (hl : s.admission.protocol.storage.live = t.admission.protocol.storage.live) :
    Next a r encode (s, e) (t, e) := by
  have h := lift_registry (e := e) hb hreg
  rwa [clearLost_same s t e hl] at h

theorem cert_step {a : ATheory} {r : RTheory} {encode : record → Nat} {s : ModelState} {e e' : XState}
    (h : CertStep a s e e') : Next a r encode (s, e) (s, e') :=
  ⟨protocol_stutter a r encode s, Or.inr ⟨rfl, h⟩⟩

end
#print axioms guard_stutter
#print axioms reachable_protocol
#print axioms cert_sound
#print axioms reply_survives
#print axioms scan_complete
#print axioms scan_between
#print axioms checkpoint_contents_discoverable
#print axioms receive_guard_sound
#print axioms receive_guard_physical
end ParaleanAckCertificates

/-! Concrete instance: the ProtocolExecution store (two replicas, write quorum =
both, recovery quorum = replica `true`, meet = `true`), two groups, two workers. -/
namespace ParaleanAckCertificates.Example
noncomputable section
open ParaleanAdmission ParaleanCompletionRecovery.Example
open ParaleanProtocol.Example (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18
  lostDisk put_joint ack_joint prepare_joint publish_joint control_joint accept_joint
  catalogue_commit_joint guarded_finish_joint destroy_replica)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

abbrev X := Extra Bool Bool Bool
abbrev R := Reachable theory recoveryTheory encode
abbrev pst (dl : ParaleanProtocol.Example.Delivery) (rg : ParaleanProtocol.Example.Registry)
    (disk : ParaleanProtocol.Example.Disk) (rec : ParaleanProtocol.Example.Recovery := rec0) :=
  ParaleanProtocol.Example.state dl rg disk rec

def e0 : X := initExtra
/-- Publisher (node `false`) writes certificates for both groups on replica `true`
only: enough for a physical read, not a certificate quorum. -/
def eA : X := putCert (putCert e0 false true false) false true true
/-- The committer (node `true`) collects replies one put at a time, interleaved
with base steps: group `false` on replica `false`, then on `true`, then group `true`. -/
def eB1 : X := putCert eA true false false
def eB2 : X := putCert eB1 true true false
def eB3 : X := putCert eB2 true false true
def eB4 : X := putCert eB3 true true true

theorem eA_cert (d : Bool) : eA.cert true d = true := by
  cases d <;> simp [eA, putCert, e0, initExtra]
theorem eB4_reply (d x : Bool) : eB4.certReply true d x = true := by
  cases d <;> cases x <;> simp [eB4, eB3, eB2, eB1, eA, putCert, e0, initExtra]
theorem eA_no_quorum (n d : Bool) : ¬CertQuorumBy theory eA n d := by
  rintro ⟨w, hw⟩
  have := hw false rfl
  cases n <;> cases d <;> simp [eA, putCert, e0, initExtra] at this

/-! Crash/recover states that erase every worker index. -/
def dlC1 : ParaleanProtocol.Example.Delivery := { dlDone with epoch := (fun n => if n then 2 else 1) }
def dlC2 : ParaleanProtocol.Example.Delivery :=
  { dlDone with
    epoch := fun n => if n then 3 else 1
    active := fun _ => false
    accepted := fun _ => false
    done := fun _ => false }
def rgC1 : ParaleanProtocol.Example.Registry := { rgCommitted with alive := id, known := (fun n _ => n) }
def rgC2 : ParaleanProtocol.Example.Registry :=
  { rgCommitted with alive := (fun _ => false), known := (fun _ _ => false) }
def rgR : ParaleanProtocol.Example.Registry := { rgC2 with alive := id }

theorem crash_steps :
    ParaleanDelivery.Step deliveryTheory dlDone (.cancel false) dlC1 ∧
    ParaleanDelivery.Step deliveryTheory dlC1 (.cancel true) dlC2 ∧
    ParaleanGroups.GroupsNext groupTheory rgCommitted (.crash false) rgC1 ∧
    ParaleanGroups.GroupsNext groupTheory rgC1 (.crash true) rgC2 ∧
    ParaleanGroups.GroupsNext groupTheory rgC2 (.recover true) rgR := by
  repeat' apply And.intro
  all_goals simp [ParaleanDelivery.Step, ParaleanDelivery.Next, ParaleanDelivery.NextAct,
    ParaleanDelivery.cancel.ext.derived_eq, ParaleanDelivery.cancel.ext.tr,
    ParaleanGroups.GroupsNext, ParaleanGroups.Next, ParaleanGroups.NextAct,
    ParaleanGroups.crash.ext.derived_eq, ParaleanGroups.recover.ext.derived_eq,
    ParaleanGroups.crash.ext.tr, ParaleanGroups.recover.ext.tr,
    deliveryTheory, groupTheory, dlDone, dlAcceptedTarget, dlStartedTarget, dlAcceptedHelper,
    dlStartedHelper, dl0, dlC1, dlC2, rgCommitted, rgReceived, rgPublished, rg0, rgC1, rgC2, rgR,
    getFrom, setIn, readFrom, Veil.FieldRepresentation.get, instIsSubStateOfRefl,
    instIsSubReaderOfRefl, ParaleanDelivery.canonicalFieldRep, ParaleanGroups.canonicalFieldRep,
    Veil.canonicalFieldRepresentation, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]

theorem crash_joint (n : Bool) (dl dl' : ParaleanProtocol.Example.Delivery)
    (rg rg' : ParaleanProtocol.Example.Registry) (disk : ParaleanProtocol.Example.Disk)
    (rec : ParaleanProtocol.Example.Recovery)
    (hd : ParaleanDelivery.Step deliveryTheory dl (.cancel n) dl')
    (hg : ParaleanGroups.GroupsNext groupTheory rg (.crash n) rg') :
    ParaleanProtocol.Next theory recoveryTheory encode (pst dl rg disk rec) (pst dl' rg' disk rec) :=
  .paired (.admission (.crash n (.paired hd hg)) rfl)
    (.registry (.crash n) (by intros; simp) hg trivial (by intros; contradiction))

theorem recover_joint (dl : ParaleanProtocol.Example.Delivery)
    (rg rg' : ParaleanProtocol.Example.Registry) (disk : ParaleanProtocol.Example.Disk)
    (rec : ParaleanProtocol.Example.Recovery)
    (hg : ParaleanGroups.GroupsNext groupTheory rg (.recover true) rg') :
    ParaleanProtocol.Next theory recoveryTheory encode (pst dl rg disk rec) (pst dl rg' disk rec) :=
  .paired (.admission (.registry (.recover true) trivial hg trivial) rfl)
    (.registry (.recover true) (by intros; simp) hg trivial (by intros; contradiction))

/-- Prefix through the second publish (shared by the witness and the necessity branch). -/
theorem published_reachable :
    R (pst dl0 rgHelper d11, e0) ∧ R (pst dl0 rgPublished d12, e0) := by
  have h0 : R (ParaleanProtocol.Example.initial, e0) := .initial ⟨ParaleanProtocol.Example.initial_valid, rfl⟩
  have h1 := Reachable.step h0 (lift_same (put_joint dl0 rg0 d0 false (.payload false) rfl) rfl rfl)
  have h2 := Reachable.step h1 (lift_same (put_joint dl0 rg0 d1 true (.payload false) rfl) rfl rfl)
  have h3 := Reachable.step h2 (lift_same (ack_joint dl0 rg0 d2 (.payload false)
    (by intro r; cases r <;> simp [d2, d1, d0, disk0, put]) trivial) rfl rfl)
  have h4 := Reachable.step h3 (lift_same (put_joint dl0 rg0 d3 false (.publication false) rfl) rfl rfl)
  have h5 := Reachable.step h4 (lift_same (put_joint dl0 rg0 d4 true (.publication false) rfl) rfl rfl)
  have h6 := Reachable.step h5 (lift (prepare_joint dl0 rg0 rgPreparedHelper d5 false group_steps.2.1)
    (fun n d h1 h2 _ => absurd (h1.symm.trans h2) (by decide)) (fun n h => absurd rfl h) rfl)
  have h7 := Reachable.step h6 (lift (publish_joint dl0 rgPreparedHelper rgHelper d5 false
    group_steps.2.2.1 (by simp [d5, d4, d3, ack, put])
    (by intro r; cases r <;> simp [d5, d4, d3, d2, d1, d0, disk0, put, ack]))
    (fun n d _ _ h3 => by simp [pst, ParaleanProtocol.Example.state, rgPreparedHelper, rg0] at h3)
    (fun n h => absurd rfl h) rfl)
  have h8 := Reachable.step h7 (lift_same (put_joint dl0 rgHelper d6 false (.payload true) rfl) rfl rfl)
  have h9 := Reachable.step h8 (lift_same (put_joint dl0 rgHelper d7 true (.payload true) rfl) rfl rfl)
  have h10 := Reachable.step h9 (lift_same (ack_joint dl0 rgHelper d8 (.payload true)
    (by intro r; cases r <;> simp [d8, d7, d6, d5, d4, d3, d2, d1, d0, disk0, put, ack]) trivial) rfl rfl)
  have h11 := Reachable.step h10 (lift_same (put_joint dl0 rgHelper d9 false (.publication true) rfl) rfl rfl)
  have h12 := Reachable.step h11 (lift_same (put_joint dl0 rgHelper d10 true (.publication true) rfl) rfl rfl)
  have h13 := Reachable.step h12 (lift (prepare_joint dl0 rgHelper rgPreparedTarget d11 true
    group_steps.2.2.2.1)
    (fun n d h1 h2 _ => absurd (h1.symm.trans h2) (by decide)) (fun n h => absurd rfl h) rfl)
  have h14 := Reachable.step h13 (lift (publish_joint dl0 rgPreparedTarget rgPublished d11 true
    group_steps.2.2.2.2.1 (by simp [d11, d10, d9, ack, put])
    (by intro r; cases r <;> simp [d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0, disk0, put, ack]))
    (fun n d h1 h2 h3 => by
      cases n <;> cases d <;> simp [pst, ParaleanProtocol.Example.state, rgPreparedTarget,
        rgPublished, rgHelper, rg0] at h1 h2 h3)
    (fun n h => absurd rfl h) rfl)
  exact ⟨h12, h14⟩

/-- Pre-commit state: catalogue committed, replica `false` not yet lost. -/
abbrev catalogued := pst dlAcceptedTarget rgReceived d18 recCommitted
/-- Replica `false` lost after it replied to the committer, before the commit. -/
abbrev lostPre := pst dlAcceptedTarget rgReceived lostDisk recCommitted
def lostState := pst dlDone rgCommitted lostDisk recCommitted
def eL : X := clearLost catalogued lostPre eB4
def erasedState := pst dlC2 rgR lostDisk recCommitted

theorem eL_cert (d : Bool) : eL.cert true d = true := by
  cases d <;> simp [eL, clearLost, lostPre, pst, ParaleanProtocol.Example.state, lostDisk,
    eB4, eB3, eB2, eB1, eA, putCert, e0, initExtra]
theorem eL_reply (d x : Bool) : eL.certReply true d x = true := eB4_reply d x
theorem eL_quorum (d : Bool) : CertQuorumBy theory eL true d := ⟨(), fun x _ => eL_reply d x⟩

/-- The checkpoint commit after the loss: the base guarded finish on `lostDisk`. -/
theorem finish_after_loss : ParaleanCompletionRecovery.FinishStep theory recoveryTheory true true true
    lostPre lostState := by
  refine .guarded (.paired delivery_steps.2.2.2.2.2.2.2
    (.registry group_steps.2.2.2.2.2.2.2 ?_)) rfl rfl rfl
  simp [ParaleanGroupComposition.Guard, protocolTheory, theory, lostDisk,
    ParaleanCompletionRecovery.Example.put, ParaleanCompletionRecovery.Example.ack,
    d18, d17, d16, d15, d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0]

/-- Publisher certificates on one replica, two receipts through the physical read,
the committer's certificate puts interleaved with manifest and catalogue writes,
catalogue commit, loss of replica `false`, then the checkpoint commit. -/
theorem lost_reachable : R (lostPre, eL) ∧ R (lostState, eL) := by
  have h14 := published_reachable.2
  have c1 := Reachable.step h14 (cert_step (.put false true false rfl rfl))
  have c2 := Reachable.step c1 (cert_step (.put false true true rfl rfl))
  have h15 := Reachable.step c2 (lift_same (control_joint dl0 dlStartedHelper rgPublished d12
    (.start true false) trivial delivery_steps.2.1) rfl rfl)
  have h16 := Reachable.step h15 (lift_same (control_joint dlStartedHelper dlSentHelper rgPublished d12
    (.send false) trivial delivery_steps.2.2.1) rfl rfl)
  have h17 := Reachable.step h16 (lift (accept_joint dlSentHelper dlAcceptedHelper rgPublished
    rgReceivedHelper d12 false delivery_steps.2.2.2.1 group_steps.2.2.2.2.2.1
    (by simp [d12, d11, d10, d9, d8, d7, d6, put, ack])
    (by simp [d12, d11, d10, d9, d8, d7, d6, d5, d4, put, ack]) rfl)
    (fun n d _ _ _ => ⟨(), true, rfl, rfl, eA_cert d⟩) (fun n h => absurd rfl h) rfl)
  have h18 := Reachable.step h17 (lift_same (control_joint dlAcceptedHelper dlStartedTarget
    rgReceivedHelper d12 (.start true true) trivial delivery_steps.2.2.2.2.1) rfl rfl)
  have h19 := Reachable.step h18 (lift_same (control_joint dlStartedTarget dlSentTarget
    rgReceivedHelper d12 (.send true) trivial delivery_steps.2.2.2.2.2.1) rfl rfl)
  have h20 := Reachable.step h19 (lift (accept_joint dlSentTarget dlAcceptedTarget rgReceivedHelper
    rgReceived d12 true delivery_steps.2.2.2.2.2.2.1 group_steps.2.2.2.2.2.2.1
    (by simp [d12, ack]) (by simp [d12, d11, d10, put, ack]) rfl)
    (fun n d _ _ _ => ⟨(), true, rfl, rfl, eA_cert d⟩) (fun n h => absurd rfl h) rfl)
  have p1 := Reachable.step h20 (cert_step (.put true false false rfl rfl))
  have h21 := Reachable.step p1 (lift_same (put_joint dlAcceptedTarget rgReceived d12 false (.manifest true) rfl) rfl rfl)
  have p2 := Reachable.step h21 (cert_step (.put true true false rfl rfl))
  have h22 := Reachable.step p2 (lift_same (put_joint dlAcceptedTarget rgReceived d13 true (.manifest true) rfl) rfl rfl)
  have p3 := Reachable.step h22 (cert_step (.put true false true rfl rfl))
  have h23 := Reachable.step p3 (lift_same (ack_joint dlAcceptedTarget rgReceived d14 (.manifest true)
    (by intro r; cases r <;> simp [d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0,
      disk0, put, ack]) trivial) rfl rfl)
  have h24 := Reachable.step h23 (lift_same (put_joint dlAcceptedTarget rgReceived d15 false (.catalog 1) rfl) rfl rfl)
  have p4 := Reachable.step h24 (cert_step (.put true true true rfl rfl))
  have h25 := Reachable.step p4 (lift_same (put_joint dlAcceptedTarget rgReceived d16 true (.catalog 1) rfl) rfl rfl)
  have h26 := Reachable.step h25 (lift_same catalogue_commit_joint rfl rfl)
  have l1 : R (lostPre, eL) := Reachable.step h26 (lift_registry (e := eB4)
    (ParaleanProtocol.failure_step theory recoveryTheory encode
      (.storage false destroy_replica)) rfl)
  refine ⟨l1, Reachable.step l1 (lift (ParaleanProtocol.finish_step theory recoveryTheory encode
    true true true finish_after_loss)
    (fun n d h1 h2 _ => absurd (h1.symm.trans h2) (by decide)) ?_ rfl)⟩
  intro n hn d _
  cases n
  · exact absurd (by simp [lostState, lostPre, pst, ParaleanProtocol.Example.state, rgCommitted,
      rgReceived, rgPublished, rgPreparedTarget, rgHelper, rgPreparedHelper, rg0]) hn
  · exact eL_quorum d

/-- Crash both workers (all indexes erased), recover one. -/
theorem erased_reachable : R (erasedState, eL) := by
  have hc := lost_reachable.2
  have k1 := Reachable.step hc (lift (crash_joint false dlDone dlC1 rgCommitted rgC1 lostDisk
    recCommitted crash_steps.1 crash_steps.2.2.1)
    (fun n d h1 _ _ => by simp [lostState, pst, ParaleanProtocol.Example.state, rgCommitted, rgReceived,
      rgPublished, rg0] at h1)
    (fun n h => absurd rfl h) rfl)
  have k2 := Reachable.step k1 (lift (crash_joint true dlC1 dlC2 rgC1 rgC2 lostDisk
    recCommitted crash_steps.2.1 crash_steps.2.2.2.1)
    (fun n d _ h2 _ => by simp [pst, ParaleanProtocol.Example.state, rgC2] at h2)
    (fun n h => absurd rfl h) rfl)
  exact Reachable.step k2 (lift (recover_joint dlC2 rgC2 rgR lostDisk recCommitted
    crash_steps.2.2.2.2)
    (fun n d h1 h2 _ => absurd (h1.symm.trans h2) (by decide)) (fun n h => absurd rfl h) rfl)

/-- Non-vacuity. Before the committer's puts no node holds a certificate quorum.
The committer then collects replies across separate steps; replica `false`,
which replied for both groups, is lost; the commit still succeeds from the
committer's own replies. After every index is erased, the certificate scan of
the surviving quorum finds both groups and the hardened receive succeeds. -/
theorem nonvacuous_certificate_rediscovery :
    (∀ n d, ¬CertQuorumBy theory eA n d) ∧
    R (lostPre, eL) ∧
    lostPre.admission.protocol.storage.live false = false ∧
    (∀ d, eL.certReply true d false = true) ∧
    lostPre.admission.protocol.registry.head true = false ∧
    R (lostState, eL) ∧
    lostState.admission.protocol.registry.head true = true ∧
    (∀ d, CertQuorumBy theory eL true d) ∧
    R (erasedState, eL) ∧
    erasedState.admission.protocol.storage.live false = false ∧
    (∀ n d, erasedState.admission.protocol.registry.known n d = false) ∧
    (∀ d, certScan theory erasedState eL () d) ∧
    (∀ d, certScan theory erasedState eL () d → erasedState.admission.protocol.registry.published d = true) ∧
    ∃ rg', rg'.known true true = true ∧
      Next theory recoveryTheory encode (erasedState, eL)
        (⟨⟨erasedState.admission.delivery, ⟨rg', erasedState.admission.protocol.storage⟩⟩,
          erasedState.recovery⟩, eL) := by
  have hr := erased_reachable
  have hq : ∀ x, theory.storage.memberR x () = true → erasedState.admission.protocol.storage.live x = true :=
    fun x hx => hx
  have hb := scan_between theory recoveryTheory encode assumptions hr () hq
  obtain ⟨rg', _, hk, ht⟩ := receive_guard_physical theory recoveryTheory encode assumptions hr
    true true ⟨(), true, rfl, rfl, eL_cert true⟩ rfl rfl rfl
  refine ⟨eA_no_quorum, lost_reachable.1, rfl, fun d => eL_reply d false, ?_, lost_reachable.2,
    rfl, eL_quorum, hr, rfl, fun _ _ => rfl, fun d => (hb d).1 ⟨true, eL_quorum d⟩,
    fun d => (hb d).2, rg', hk, ht⟩
  simp [lostPre, pst, ParaleanProtocol.Example.state, rgReceived, rgPublished, rgPreparedTarget,
    rgHelper, rgPreparedHelper, rg0]

/-! Guard necessity. Branch after both markers are staged but only group `false`
is published, then lose replica `false`. The surviving bytes of the acknowledged
and the staged marker are identical, so no function of physical marker bytes
decides acceptance; the hardened model never holds a certificate for the staged one. -/
def stagedLost : ParaleanProtocol.Example.Disk :=
  { d11 with live := id, stored := fun r o => if r then d11.stored r o else false }
def stagedState := pst dl0 rgHelper stagedLost

theorem lose_staged : ParaleanGroupComposition.StorageNext storageTheory d11 (.Lose false) stagedLost := by
  simp only [ParaleanGroupComposition.StorageNext, Durability.Next, Durability.NextAct, Durability.Lose.ext.derived_eq]
  dsimp [Durability.Lose.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanGroupComposition.diskFieldRep,
    Veil.canonicalFieldRepresentation]
  simp [storageTheory, stagedLost, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0, disk0, put, ack,
    Veil.FieldRepresentation.setSingle,
    Veil.CanonicalField.set, Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry,
    Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]

theorem staged_reachable :
    R (stagedState, clearLost (pst dl0 rgHelper d11) stagedState e0) :=
  Reachable.step published_reachable.1 (lift_registry
    (ParaleanProtocol.failure_step theory recoveryTheory encode (.storage false lose_staged)) rfl)

theorem guard_necessity :
    ParaleanProtocol.Reachable theory recoveryTheory encode stagedState ∧
    stagedState.admission.protocol.registry.published false = true ∧
    stagedState.admission.protocol.registry.published true = false ∧
    stagedState.admission.protocol.storage.acknowledged (.publication false) = true ∧
    stagedState.admission.protocol.storage.acknowledged (.publication true) = false ∧
    (∀ x, stagedState.admission.protocol.storage.live x = true →
      stagedState.admission.protocol.storage.stored x (.publication false) = true ∧
      stagedState.admission.protocol.storage.stored x (.publication true) = true) ∧
    stagedState.admission.protocol.storage.live false = false ∧
    (¬∃ accept : (Bool → Bool) → (Bool → Bool) → Bool, ∀ g,
      accept stagedState.admission.protocol.storage.live
        (fun x => stagedState.admission.protocol.storage.stored x (.publication g)) =
      stagedState.admission.protocol.storage.acknowledged (.publication g)) ∧
    (∀ e, R (stagedState, e) → ∀ x, e.cert x true = false) := by
  have hbytes : ∀ g, (fun x => stagedState.admission.protocol.storage.stored x (.publication g)) =
      stagedState.admission.protocol.storage.live := by
    intro g; funext x
    cases x <;> cases g <;> simp [stagedState, pst, ParaleanProtocol.Example.state, stagedLost,
      d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, d0, disk0, put, ack]
  refine ⟨reachable_protocol theory recoveryTheory encode staged_reachable, rfl, rfl, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · simp [stagedState, pst, ParaleanProtocol.Example.state, stagedLost, d11, d10, d9, d8, d7, d6, put, ack]
  · simp [stagedState, pst, ParaleanProtocol.Example.state, stagedLost, d11, d10, d9, d8, d7, d6,
      d5, d4, d3, d2, d1, d0, disk0, put, ack]
  · intro x hx
    exact ⟨(congrFun (hbytes false) x).trans hx, (congrFun (hbytes true) x).trans hx⟩
  · rintro ⟨accept, h⟩
    have h0 := h false
    have h1 := h true
    rw [hbytes] at h0 h1
    have := h0.symm.trans h1
    revert this
    simp [stagedState, pst, ParaleanProtocol.Example.state, stagedLost, d11, d10, d9, d8, d7, d6,
      d5, d4, d3, d2, d1, d0, disk0, put, ack]
  · intro e he x
    cases hc : e.cert x true
    · rfl
    · have := (cert_sound theory recoveryTheory encode assumptions he x true hc).1
      exact absurd this (by decide)

end
#print axioms published_reachable
#print axioms lost_reachable
#print axioms erased_reachable
#print axioms nonvacuous_certificate_rediscovery
#print axioms guard_necessity
end ParaleanAckCertificates.Example
