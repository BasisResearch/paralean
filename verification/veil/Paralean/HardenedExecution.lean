import Paralean.Hardened

/-! Joint non-vacuity of the hardened protocol. One concrete trace on the
`ParaleanCompletionRecovery.Example` instance (two workers, two groups, two
replicas, fence tokens of rank 0/1) satisfies all five guards on every step:
receipt-gated prepares, target-name ownership with epochs and a recorded head,
fenced first catalogue writes, physical publication certificates, and physical
catalogue certificates with fenced commit records. Worker `false` owns name `2`
initially; it prepares and publishes a helper and the required target under
held receipts (the target becomes the name's recorded head) and writes a
certificate for each on replica `true`. Worker `true` receives each group
through the physical certificate read, then puts certificates for both groups
on both replicas. The catalogue record is acknowledged, its manifest and
payloads are certified, and its commit certificate is written under fence 0;
the catalogue commits and the worker finishes. The desktop is lost, the
controller reassigns name `2` to worker `true`, the fence rotates to 1, and
record `false` (rank-1 token) is first written, acknowledged and given a commit
certificate under fence 1. A replica is lost, every worker index is erased, a
certificate scan rediscovers the published groups, the new owner receives the
recorded head through a certificate read, and recovery selects the record whose
commit certificate passed the fence check. -/
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace ParaleanHardened.Example
noncomputable section
open ParaleanAdmission
open ParaleanCompletionRecovery.Example (theory recoveryTheory encode deliveryTheory groupTheory
  storageTheory assumptions recovery_assumptions rg0 rgPreparedHelper rgHelper rgPublished
  rgReceivedHelper rgReceived rgCommitted dl0 dlStartedHelper dlSentHelper dlAcceptedHelper
  dlStartedTarget dlSentTarget dlAcceptedTarget dlDone disk0 put ack rec0 recCommitted recForgotten
  forget_desktop delivery_steps group_steps CState)
open ParaleanProtocol.Example (state d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17
  d18 lostDisk put_joint ack_joint prepare_joint publish_joint control_joint accept_joint
  catalogue_commit_joint guarded_finish_joint destroy_replica)
open ParaleanAckCertificates.Example (dlC1 dlC2 rgC1 rgC2 rgR crash_steps crash_joint recover_joint)
open ParaleanCatalogFencing.Example (fRot fScan fRebuilt fAuto recovery_steps ready_on)
attribute [local instance] Classical.propDecidable

abbrev TH := theory
abbrev RT := recoveryTheory
abbrev EN := encode
abbrev X := ParaleanAckCertificates.Extra Bool Bool Bool
abbrev XT := ParaleanTargetNames.Extra Bool Bool (Fin 3)
abbrev XC := ParaleanCatalogCertificates.Extra Bool Bool (StoredObject Bool Bool)
abbrev k0 : XC := ParaleanCatalogCertificates.initExtra
abbrev Registry := ParaleanGroups.CanonicalState Bool Bool (Fin 3) Bool

/-- Record `true` (catalogue object 1) embeds the rank-0 token; record `false`
(catalogue object 0) embeds the rank-1 token, so it can only be written after the
fence rotates to 1. -/
def tok : Bool → Bool := fun c => !c

/-- Every request is pinned to name `2` (declared only by group `true`). -/
def targets : ParaleanTargetNames.TargetAssumptions TH where
  targetName := fun _ => 2
  pinned := by
    intro o q h1 h2
    cases o <;> cases q <;> simp_all [TH, theory, deliveryTheory, groupTheory]

def cfg : ParaleanHardened.Config TH Bool Bool := ⟨targets, tok⟩

/-- Initial ownership: worker `false` owns every name, at epoch `0`. -/
abbrev eT0 : XT := ParaleanTargetNames.initExtra (fun _ => false)
/-- Owner `false`'s epoch-conditional publication of the target records it as
the head of name `2`. -/
abbrev eTP : XT := { eT0 with head := fun x => if x = 2 then some true else none }
/-- After the desktop loss the controller hands name `2` to worker `true` (epoch
`1`); the record keeps head `true`. -/
abbrev eT1 : XT := ParaleanTargetNames.reassign eTP 2 true

/-- The instance satisfies the admission and coupled recovery assumptions, so
`ParaleanHardened.hardened_safe` applies to it. -/
theorem instance_assumptions :
    ParaleanAdmission.Assumptions TH ∧
    ParaleanRecovery.CoupledAssumptions (ParaleanRecovery.ofAdmission TH RT EN) :=
  ⟨assumptions, recovery_assumptions⟩

/-! ## New registry states

Under the receipt guard the target prepare needs the target receipt in flight,
which the delivery layer only sends after accepting the helper, and that accept
needs the helper received. So the helper is received before the target is prepared. -/

def rgHelperRecv : Registry := { rgHelper with known := fun _ g => !g }
def rgPrepT : Registry := { rgHelperRecv with pending := fun n g => !n && g }
def rgRecv : Registry := { rgR with known := fun n g => n && g }

theorem new_group_steps :
    ParaleanGroups.GroupsNext groupTheory rgHelper (.receive true false) rgHelperRecv ∧
    ParaleanGroups.GroupsNext groupTheory rgHelperRecv (.prepare false true) rgPrepT ∧
    ParaleanGroups.GroupsNext groupTheory rgPrepT (.publish false true) rgReceivedHelper ∧
    ParaleanGroups.GroupsNext groupTheory rgR (.receive true true) rgRecv := by
  repeat' apply And.intro
  all_goals simp [ParaleanGroups.GroupsNext, ParaleanGroups.Next, ParaleanGroups.NextAct,
    ParaleanGroups.prepare.ext.derived_eq, ParaleanGroups.publish.ext.derived_eq,
    ParaleanGroups.receive.ext.derived_eq,
    ParaleanGroups.prepare.ext.tr, ParaleanGroups.publish.ext.tr, ParaleanGroups.receive.ext.tr,
    groupTheory, rg0, rgHelper, rgHelperRecv, rgPrepT, rgPublished, rgReceivedHelper,
    rgCommitted, rgReceived, rgC2, rgR, rgRecv, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation,
    Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]

attribute [local simp] d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18

macro "regs" : tactic => `(tactic| (intro n d h; cases n <;> cases d <;>
  simp [state, rg0, rgPreparedHelper, rgHelper, rgHelperRecv, rgPrepT, rgPublished,
    rgReceivedHelper, rgReceived, rgCommitted, rgC1, rgC2, rgR, rgRecv] at h ⊢))

/-- Publication fence obligation: trivial under the initial ownership state, and
otherwise discharged by the step publishing nothing new. -/
macro "pubs" : tactic => `(tactic| first
  | exact ParaleanTargetNames.publishOk_initExtra _ _ _ _ _
  | (apply ParaleanTargetNames.publishOk_of_no_new_published; intro d h; cases d <;>
      simp [state, rg0, rgPreparedHelper, rgHelper, rgHelperRecv, rgPrepT, rgPublished,
        rgReceivedHelper, rgReceived, rgCommitted, rgC1, rgC2, rgR, rgRecv] at h ⊢))

/-! ## Step combinators -/

/-- Hardened reachability with the fencing ghost left existential. -/
def HR (s : CState) (eA : X) (eC : XC) (eT : XT) : Prop :=
  ∃ eF, ParaleanHardened.Reachable TH RT EN cfg (s, (eF, eA, eC, eT))

abbrev NoNewPending (s t : CState) : Prop :=
  ∀ n d, t.admission.protocol.registry.pending n d = true → s.admission.protocol.registry.pending n d = true

theorem hr_initial : HR (state dl0 rg0 d0) ParaleanAckCertificates.initExtra k0 eT0 :=
  ⟨fun _ => none, .initial ⟨ParaleanProtocol.Example.initial_valid, rfl, rfl, rfl, rfl⟩⟩

/-- Catalogue object 0 (record `false`) is absent; it is first written at fence 1. -/
def NoCat0 (t : CState) : Prop :=
  (∀ x, t.admission.protocol.storage.stored x (.catalog 0) = false) ∧
    t.admission.protocol.storage.acknowledged (.catalog 0) = false

macro "nocat0" : tactic => `(tactic| (refine ⟨fun x => ?_, ?_⟩ <;> (try cases x) <;>
  simp [state, disk0, put, ack, lostDisk]))

theorem cc_quiet {s t : CState} {eC : XC}
    (hc : t.recovery.committed = s.recovery.committed)
    (hl : s.admission.protocol.storage.live = t.admission.protocol.storage.live) :
    ParaleanCatalogCertificates.Guard TH RT EN tok s eC t eC := by
  refine Or.inl ⟨?_, (ParaleanCatalogCertificates.clearLost_same s t eC hl).symm⟩
  intro c h1 h2; rw [hc, h1] at h2; cases h2

theorem cc_lost {s t : CState} {eC : XC}
    (hc : t.recovery.committed = s.recovery.committed) :
    ParaleanCatalogCertificates.Guard TH RT EN tok s eC t (ParaleanCatalogCertificates.clearLost s t eC) := by
  refine Or.inl ⟨?_, rfl⟩
  intro c h1 h2; rw [hc, h1] at h2; cases h2

theorem hstep {s t : CState} {eA eA' : X} {eC eC' : XC} {eT eT' : XT} (h : HR s eA eC eT)
    (hb : ParaleanProtocol.Next TH RT EN s t)
    (hrc : ParaleanPublicationReceipts.Guard TH RT EN s () t ())
    (htg : ParaleanTargetNames.Guard TH targets RT EN s eT t eT')
    (hw : ∀ c, ParaleanCatalogFencing.NewWrite EN s t c → ParaleanCatalogFencing.Fenced RT tok s c)
    (ha : ParaleanAckCertificates.Guard TH RT EN s eA t eA')
    (hcc : ParaleanCatalogCertificates.Guard TH RT EN tok s eC t eC') : HR t eA' eC' eT' := by
  obtain ⟨eF, h⟩ := h
  exact ⟨ParaleanCatalogFencing.update EN s t eF, .step h
    ⟨hb, hrc, htg, ParaleanCatalogFencing.guard_of_fenced_writes _ _ _ _ eF hw, ha, hcc⟩⟩

theorem rguard_of {s t : CState} (h : NoNewPending s t) :
    ParaleanPublicationReceipts.Guard TH RT EN s () t () :=
  fun n d ht hs => absurd (h n d ht) hs

/-- Publishing a group that declares no target name leaves the ownership state unchanged. -/
theorem update_nontarget {s t : CState} {eT : XT} (hp : NoNewPending s t)
    (hn : ∀ d, s.admission.protocol.registry.published d = false →
      t.admission.protocol.registry.published d = true → d = false) :
    ParaleanTargetNames.update TH targets s t eT = eT := by
  refine (ParaleanTargetNames.update_eq _ _ _ _ _ eT.head hp fun x => Or.inl ⟨?_, rfl⟩)
  rintro d ⟨⟨_, _, hq⟩, hm, h1, h2⟩
  have hx : x = 2 := by simpa [targets] using hq.symm
  subst hx
  rw [hn d h1 h2] at hm
  simp [TH, theory, groupTheory] at hm

theorem tguard_of {s t : CState} {eT : XT} (h : NoNewPending s t)
    (hp : ParaleanTargetNames.PublishOk TH targets s eT t)
    (hu : ParaleanTargetNames.update TH targets s t eT = eT) :
    ParaleanTargetNames.Guard TH targets RT EN s eT t eT := by
  have g := ParaleanTargetNames.guard_of_no_new_pending TH targets RT EN s t eT h hp
  rwa [hu] at g

/-- The ownership state is unchanged by a step that neither prepares nor
publishes a target proof. -/
macro "upd" : tactic => `(tactic| (apply ParaleanTargetNames.update_same <;> first
  | (intro n d h; cases n <;> cases d <;>
      simp [state, rg0, rgPreparedHelper, rgHelper, rgHelperRecv, rgPrepT, rgPublished,
        rgReceivedHelper, rgReceived, rgCommitted, rgC1, rgC2, rgR, rgRecv] at h ⊢)
  | (intro d h; cases d <;>
      simp [state, rg0, rgPreparedHelper, rgHelper, rgHelperRecv, rgPrepT, rgPublished,
        rgReceivedHelper, rgReceived, rgCommitted, rgC1, rgC2, rgR, rgRecv] at h ⊢)))

theorem fenced0 {s : CState} (hf : s.recovery.fence = 0) :
    ParaleanCatalogFencing.Fenced RT tok s true := by
  simp [ParaleanCatalogFencing.Fenced, hf, tok, RT, recoveryTheory]

theorem fenced1 {s : CState} (hf : s.recovery.fence = 1) :
    ParaleanCatalogFencing.Fenced RT tok s false := by
  simp [ParaleanCatalogFencing.Fenced, hf, tok, RT, recoveryTheory]

/-- Under fence 0 only record `true` may be written; record `false` is absent. -/
theorem fenced_writes0 {s t : CState} (hf : s.recovery.fence = 0) (h0 : NoCat0 t) :
    ∀ c, ParaleanCatalogFencing.NewWrite EN s t c → ParaleanCatalogFencing.Fenced RT tok s c := by
  intro c hn
  cases c
  · exfalso
    rcases hn with ⟨x, h1, _⟩ | ⟨h1, _⟩
    · have := h0.1 x; simp [EN, encode] at h1; rw [this] at h1; cases h1
    · have := h0.2; simp [EN, encode] at h1; rw [this] at h1; cases h1
  · exact fenced0 hf

theorem ack_same {s t : CState} {eA : X}
    (hr : ParaleanAckCertificates.ReceiveGuard TH s eA t)
    (hc : ParaleanAckCertificates.CommitGuard TH s eA t)
    (hl : s.admission.protocol.storage.live = t.admission.protocol.storage.live) :
    ParaleanAckCertificates.Guard TH RT EN s eA t eA :=
  Or.inl ⟨hr, hc, (ParaleanAckCertificates.clearLost_same s t eA hl).symm⟩

theorem ack_reg {s t : CState} {eA : X}
    (hreg : t.admission.protocol.registry = s.admission.protocol.registry) :
    ParaleanAckCertificates.Guard TH RT EN s eA t (ParaleanAckCertificates.clearLost s t eA) := by
  refine Or.inl ⟨?_, ?_, rfl⟩
  · intro n d h1 h2 _; rw [hreg, h1] at h2; cases h2
  · intro n h; rw [hreg] at h; exact absurd rfl h

/-- A step creating no pending bit under fence 0. -/
theorem wstep {s t : CState} {eA eA' : X} {eC : XC} {eT : XT} (h : HR s eA eC eT)
    (hb : ParaleanProtocol.Next TH RT EN s t) (hp : NoNewPending s t)
    (hf : s.recovery.fence = 0)
    (ha : ParaleanAckCertificates.Guard TH RT EN s eA t eA')
    (hpub : ParaleanTargetNames.PublishOk TH targets s eT t := by pubs)
    (hu : ParaleanTargetNames.update TH targets s t eT = eT := by upd)
    (h0 : NoCat0 t := by nocat0)
    (hcc : ParaleanCatalogCertificates.Guard TH RT EN tok s eC t eC := by exact cc_quiet rfl rfl) :
    HR t eA' eC eT :=
  hstep h hb (rguard_of hp) (tguard_of hp hpub hu) (fenced_writes0 hf h0) ha hcc

/-- A registry-preserving, liveness-preserving step under fence 0. -/
theorem pstep {s t : CState} {eA : X} {eC : XC} {eT : XT} (h : HR s eA eC eT)
    (hb : ParaleanProtocol.Next TH RT EN s t)
    (hreg : t.admission.protocol.registry = s.admission.protocol.registry)
    (hl : s.admission.protocol.storage.live = t.admission.protocol.storage.live)
    (hf : s.recovery.fence = 0)
    (h0 : NoCat0 t := by nocat0)
    (hc : t.recovery.committed = s.recovery.committed := by rfl) : HR t eA eC eT := by
  have ha := ack_reg (eA := eA) hreg
  rw [ParaleanAckCertificates.clearLost_same s t eA hl] at ha
  exact wstep h hb (fun n d h' => by rw [hreg] at h'; exact h') hf ha
    (ParaleanTargetNames.publishOk_of_no_new_published _ _ _ _ _
      (fun d h' => by rw [hreg] at h'; exact h'))
    (ParaleanTargetNames.update_same _ _ _ _ _ (fun n d h' => by rw [hreg] at h'; exact h')
      (fun d h' => by rw [hreg] at h'; exact h')) h0 (cc_quiet hc hl)

/-- A step that writes no catalogue bytes (any fence). -/
theorem qstep {s t : CState} {eA eA' : X} {eC : XC} {eT : XT} (h : HR s eA eC eT)
    (hb : ParaleanProtocol.Next TH RT EN s t) (hp : NoNewPending s t)
    (hst : t.admission.protocol.storage = s.admission.protocol.storage)
    (ha : ParaleanAckCertificates.Guard TH RT EN s eA t eA')
    (hpub : ParaleanTargetNames.PublishOk TH targets s eT t := by pubs)
    (hu : ParaleanTargetNames.update TH targets s t eT = eT := by upd)
    (hcc : ParaleanCatalogCertificates.Guard TH RT EN tok s eC t eC := by exact cc_quiet rfl rfl) :
    HR t eA' eC eT :=
  hstep h hb (rguard_of hp) (tguard_of hp hpub hu)
    (fun c hn => absurd hn (ParaleanCatalogFencing.same_storage_no_write EN hst c)) ha hcc

/-- An extra-only certificate step. -/
theorem cstep {s : CState} {eA eA' : X} {eC : XC} {eT : XT} (h : HR s eA eC eT)
    (hc : ParaleanAckCertificates.CertStep TH s eA eA') : HR s eA' eC eT := by
  obtain ⟨eF, h⟩ := h
  exact ⟨eF, .step h ⟨ParaleanAckCertificates.protocol_stutter TH RT EN s,
    ParaleanPublicationReceipts.guard_stutter _ _ _ s (),
    ParaleanTargetNames.guard_stutter _ _ _ _ s eT,
    ParaleanCatalogFencing.guard_stutter _ _ _ _ s eF, Or.inr ⟨rfl, hc⟩,
    ParaleanCatalogCertificates.guard_stutter _ _ _ _ s eC⟩⟩

/-- An extra-only catalogue certificate step. -/
theorem ccstep {s : CState} {eA : X} {eC eC' : XC} {eT : XT} (h : HR s eA eC eT)
    (hc : ParaleanCatalogCertificates.CertStep RT EN tok s eC eC') : HR s eA eC' eT := by
  obtain ⟨eF, h⟩ := h
  exact ⟨eF, .step h ⟨ParaleanAckCertificates.protocol_stutter TH RT EN s,
    ParaleanPublicationReceipts.guard_stutter _ _ _ s (),
    ParaleanTargetNames.guard_stutter _ _ _ _ s eT,
    ParaleanCatalogFencing.guard_stutter _ _ _ _ s eF,
    ParaleanAckCertificates.guard_stutter _ _ _ s eA, Or.inr ⟨rfl, hc⟩⟩⟩

/-- An extra-only controller reassignment of name `x` to node `n`. -/
theorem rstep {s : CState} {eA : X} {eC : XC} {eT : XT} (h : HR s eA eC eT) (x : Fin 3) (n : Bool) :
    HR s eA eC (ParaleanTargetNames.reassign eT x n) := by
  obtain ⟨eF, h⟩ := h
  exact ⟨eF, .step h ⟨ParaleanAckCertificates.protocol_stutter TH RT EN s,
    ParaleanPublicationReceipts.guard_stutter _ _ _ s (),
    ParaleanTargetNames.guard_reassign _ _ _ _ s eT x n,
    ParaleanCatalogFencing.guard_stutter _ _ _ _ s eF,
    ParaleanAckCertificates.guard_stutter _ _ _ s eA,
    ParaleanCatalogCertificates.guard_stutter _ _ _ _ s eC⟩⟩

/-! ## Certificate extras

Publisher `false` writes one certificate per group on replica `true` (enough for
the physical read that guards worker `true`'s receive, not a quorum). Committer
`true` then puts each group on both replicas itself, after receiving it. -/

open ParaleanAckCertificates (putCert clearLost initExtra certScan CertQuorumBy)

def eP1 : X := putCert initExtra false true false
def eC1 : X := putCert eP1 true false false
def eC2 : X := putCert eC1 true true false
def eP2 : X := putCert eC2 false true true
def eC3 : X := putCert eP2 true false true
def eFull : X := putCert eC3 true true true

theorem eP2_cert (d : Bool) : eP2.cert true d = true := by
  cases d <;> simp [eP2, eC2, eC1, eP1, putCert, initExtra]
theorem eFull_reply (d x : Bool) : eFull.certReply true d x = true := by
  cases d <;> cases x <;> simp [eFull, eC3, eP2, eC2, eC1, eP1, putCert, initExtra]
theorem eFull_quorum (d : Bool) : CertQuorumBy TH eFull true d := ⟨(), fun x _ => eFull_reply d x⟩
/-- Before the committer's puts nobody holds a certificate quorum for the target. -/
theorem eP2_no_quorum (n : Bool) : ¬CertQuorumBy TH eP2 n true := by
  rintro ⟨w, hw⟩
  have := hw false rfl
  cases n <;> simp [eP2, eC2, eC1, eP1, putCert, initExtra] at this

/-! ## States -/

abbrev preparedS : CState := state dlSentTarget rgPrepT d11
abbrev completedS : CState := state dlDone rgCommitted d18 recCommitted

/-! ## Catalogue certificates

Before the commit the writer acknowledges the catalogue record itself, writes
acknowledgement certificates for both payloads and the manifest on both replicas,
and writes the record's commit certificate on both replicas under fence 0. After
the fence rotates to 1, record `false` (rank-1 token) is first written, acknowledged
and given a commit certificate under fence 1. -/

open ParaleanCatalogCertificates (putRecord putObject CatReady)

def k1 : XC := putObject k0 false (.payload false)
def k2 : XC := putObject k1 true (.payload false)
def k3 : XC := putObject k2 false (.payload true)
def k4 : XC := putObject k3 true (.payload true)
def k5 : XC := putObject k4 false (.manifest true)
def k6 : XC := putObject k5 true (.manifest true)
def k7 : XC := putRecord k6 false true 0
def kFull : XC := putRecord k7 true true 0
def kZ1 : XC := putRecord kFull false false 1
def kZ : XC := putRecord kZ1 true false 1

theorem kFull_ready (s : CState) : CatReady TH RT s kFull true := by
  refine ⟨⟨(), fun x _ _ => ?_⟩, ⟨(), fun x _ _ => ?_⟩, fun d _ => ⟨(), fun x _ _ => ?_⟩⟩ <;>
    (try cases d) <;> cases x <;>
    simp [kFull, k7, k6, k5, k4, k3, k2, k1, k0, putRecord, putObject,
      ParaleanCatalogCertificates.initExtra, RT, recoveryTheory]

def dZ1 := put d18 false (.catalog 0)
def dZ2 := put dZ1 true (.catalog 0)
def dZ3 := ack dZ2 (.catalog 0)
def lostZ : ParaleanProtocol.Example.Disk :=
  { dZ3 with live := id, stored := fun r o => if r then dZ3.stored r o else false }

abbrev rotS : CState := state dlDone rgCommitted d18 fRot
abbrev zS : CState := state dlDone rgCommitted dZ3 fRot
abbrev lostS : CState := state dlDone rgCommitted lostZ fRot
def eLost : X := clearLost zS lostS eFull
def kLost : XC := ParaleanCatalogCertificates.clearLost zS lostS kZ
abbrev erasedS : CState := state dlC2 rgR lostZ fRot
abbrev receivedS : CState := state dlC2 rgRecv lostZ fRot
abbrev recoveredS : CState := state dlC2 rgRecv lostZ fAuto

theorem eLost_cert (d : Bool) : eLost.cert true d = true := by
  cases d <;> simp [eLost, clearLost, lostS, zS, state, lostZ, dZ3, dZ2, dZ1, eFull, eC3, eP2,
    eC2, eC1, eP1, putCert, initExtra, put, ack]
theorem eLost_quorum (d : Bool) : CertQuorumBy TH eLost true d :=
  ⟨(), fun x _ => by simpa [eLost, clearLost] using eFull_reply d x⟩

theorem ack18 : ack d18 (.catalog 1) = d18 := by
  simp only [d18, ack]
  congr 1
  funext p
  split <;> simp_all

/-- Catalogue commit from the acknowledged record: the base commit step re-acknowledges it. -/
theorem recommit_joint : ParaleanProtocol.Next TH RT EN (state dlAcceptedTarget rgReceived d18)
    (state dlAcceptedTarget rgReceived d18 recCommitted) := by
  have hd := ParaleanCompletionRecovery.Example.ack_step d18 (.catalog 1)
    (by intro r; cases r <;> simp [disk0, put, ack])
  rw [ack18] at hd
  refine .paired (.coupled (.protocol (.storage (.Ack (.catalog 1) ()) hd)) rfl rfl
    (.commit true false () ParaleanProtocol.Example.recovery_commit hd ?_ ?_))
    (.storage (.Ack (.catalog 1) ()) trivial hd)
  · simp [state, ParaleanRecovery.ofAdmission, protocolTheory, theory, recoveryTheory, put, ack]
  · intro g hg
    cases g <;> simp [state, ParaleanRecovery.ofAdmission, protocolTheory, theory, recoveryTheory, put, ack]

/-- The commit adopts only record `true`, which is certified. -/
theorem cc_commit : ParaleanCatalogCertificates.Guard TH RT EN tok
    (state dlAcceptedTarget rgReceived d18) kFull (state dlAcceptedTarget rgReceived d18 recCommitted) kFull := by
  refine Or.inl ⟨?_, (ParaleanCatalogCertificates.clearLost_same _ _ _ rfl).symm⟩
  intro c h1 h2
  cases c
  · simp [state, recCommitted, rec0] at h2
  · exact kFull_ready _

theorem destroyZ : ParaleanGroupComposition.StorageNext storageTheory dZ3 (.Lose false) lostZ := by
  simp only [ParaleanGroupComposition.StorageNext, Durability.Next, Durability.NextAct, Durability.Lose.ext.derived_eq]
  dsimp [Durability.Lose.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanGroupComposition.diskFieldRep,
    Veil.canonicalFieldRepresentation]
  simp [storageTheory, lostZ, dZ3, dZ2, dZ1, disk0, put, ack, Veil.FieldRepresentation.setSingle,
    Veil.CanonicalField.set, Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry,
    Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]

/-! ## The trace -/

/-- Helper receipt in flight; owner `false` prepares and publishes the helper. -/
theorem helper_published : HR (state dlSentHelper rgHelper d6) initExtra k0 eT0 := by
  have h0 := hr_initial
  have h1 := pstep h0 (control_joint dl0 dlStartedHelper rg0 d0 (.start true false) trivial
    delivery_steps.2.1) rfl rfl rfl
  have h2 := pstep h1 (control_joint dlStartedHelper dlSentHelper rg0 d0 (.send false) trivial
    delivery_steps.2.2.1) rfl rfl rfl
  have h3 := pstep h2 (put_joint dlSentHelper rg0 d0 false (.payload false) rfl) rfl rfl rfl
  have h4 := pstep h3 (put_joint dlSentHelper rg0 d1 true (.payload false) rfl) rfl rfl rfl
  have h5 := pstep h4 (ack_joint dlSentHelper rg0 d2 (.payload false)
    (by intro r; cases r <;> simp [disk0, put]) trivial) rfl rfl rfl
  have h6 := pstep h5 (put_joint dlSentHelper rg0 d3 false (.publication false) rfl) rfl rfl rfl
  have h7 := pstep h6 (put_joint dlSentHelper rg0 d4 true (.publication false) rfl) rfl rfl rfl
  have held : ParaleanPublicationReceipts.HeldReceipt TH dlSentHelper false := ⟨false, rfl, rfl, rfl, rfl⟩
  have h8 : HR (state dlSentHelper rgPreparedHelper d5) initExtra k0 eT0 := by
    refine hstep h7 (prepare_joint dlSentHelper rg0 rgPreparedHelper d5 false group_steps.2.1)
      ?_ (ParaleanTargetNames.guard_of_synced_prepare _ _ _ _ _ _ _ (fun _ _ _ => rfl) ?_ (by
      intro d h; cases d <;> simp [state, rg0, rgPreparedHelper, rgHelper, rgHelperRecv, rgPrepT] at h ⊢)) (fenced_writes0 rfl (by nocat0))
      (ack_same (fun n d h1 h2 _ => absurd (h1.symm.trans h2) (by decide))
        (fun n h => absurd rfl h) rfl) (cc_quiet rfl rfl)
    · intro n d ht _
      cases n <;> cases d <;> simp [state, rgPreparedHelper, rg0] at ht
      exact held
    · intro n d x hp hs hm hx
      have hx2 : x = 2 := by obtain ⟨q, _, hq⟩ := hx; simpa [targets] using hq.symm
      subst hx2
      cases n <;> cases d <;> simp [state, rg0, rgPreparedHelper, TH, theory, groupTheory] at hp hs hm
  exact wstep h8 (publish_joint dlSentHelper rgPreparedHelper rgHelper d5 false group_steps.2.2.1
      (by simp [ack, put]) (by intro r; cases r <;> simp [disk0, put, ack]))
    (by regs) rfl
    (ack_same (fun n d _ _ h3 => by simp [state, rgPreparedHelper, rg0] at h3)
      (fun n h => absurd rfl h) rfl) (hu := update_nontarget (by regs) (by
        intro d h1 h2; cases d <;> simp [state, rgPreparedHelper, rgHelper, rg0] at h1 h2 ⊢))

theorem held_target : ParaleanPublicationReceipts.HeldReceipt TH dlSentTarget true :=
  ⟨true, rfl, rfl, rfl, rfl⟩

/-- Publisher certificate for the helper; worker `true` receives the helper
through the physical read and puts its own helper certificates on both replicas;
the target receipt is sent and owner `false` prepares the target while holding it. -/
theorem target_prepared : HR preparedS eC2 k0 eT0 := by
  have h9 := helper_published
  have c1 : HR (state dlSentHelper rgHelper d6) eP1 k0 eT0 := cstep h9 (.put false true false rfl rfl)
  have h10 : HR (state dlAcceptedHelper rgHelperRecv d6) eP1 k0 eT0 :=
    wstep c1 (accept_joint dlSentHelper dlAcceptedHelper rgHelper rgHelperRecv d6 false
        delivery_steps.2.2.2.1 new_group_steps.1 (by simp [put, ack]) (by simp [put, ack]) rfl)
      (by regs) rfl
      (ack_same (fun n d h1 h2 _ => ⟨(), true, rfl, rfl, by
          cases n <;> cases d <;> simp [state, rgHelper, rgHelperRecv, rg0] at h1 h2 ⊢
          simp [eP1, putCert, initExtra]⟩)
        (fun n h => absurd rfl h) rfl)
  have c2 : HR (state dlAcceptedHelper rgHelperRecv d6) eC1 k0 eT0 := cstep h10 (.put true false false rfl rfl)
  have c3 : HR (state dlAcceptedHelper rgHelperRecv d6) eC2 k0 eT0 := cstep c2 (.put true true false rfl rfl)
  have h11 := pstep c3 (put_joint dlAcceptedHelper rgHelperRecv d6 false (.payload true) rfl) rfl rfl rfl
  have h12 := pstep h11 (put_joint dlAcceptedHelper rgHelperRecv d7 true (.payload true) rfl) rfl rfl rfl
  have h13 := pstep h12 (ack_joint dlAcceptedHelper rgHelperRecv d8 (.payload true)
    (by intro r; cases r <;> simp [disk0, put, ack]) trivial) rfl rfl rfl
  have h14 := pstep h13 (put_joint dlAcceptedHelper rgHelperRecv d9 false (.publication true) rfl) rfl rfl rfl
  have h15 := pstep h14 (put_joint dlAcceptedHelper rgHelperRecv d10 true (.publication true) rfl) rfl rfl rfl
  have h16 := pstep h15 (control_joint dlAcceptedHelper dlStartedTarget rgHelperRecv d11
    (.start true true) trivial delivery_steps.2.2.2.2.1) rfl rfl rfl
  have h17 := pstep h16 (control_joint dlStartedTarget dlSentTarget rgHelperRecv d11
    (.send true) trivial delivery_steps.2.2.2.2.2.1) rfl rfl rfl
  refine hstep h17 (prepare_joint dlSentTarget rgHelperRecv rgPrepT d11 true new_group_steps.2.1)
    ?_ (ParaleanTargetNames.guard_of_synced_prepare _ _ _ _ _ _ _ (fun _ _ _ => rfl) ?_ (by
      intro d h; cases d <;> simp [state, rg0, rgPreparedHelper, rgHelper, rgHelperRecv, rgPrepT] at h ⊢)) (fenced_writes0 rfl (by nocat0))
    (ack_same (fun n d h1 h2 _ => absurd (h1.symm.trans h2) (by decide))
      (fun n h => absurd rfl h) rfl) (cc_quiet rfl rfl)
  · intro n d ht _
    cases n <;> cases d <;> simp [state, rgPrepT, rgHelperRecv, rgHelper, rg0] at ht
    exact held_target
  · intro n d x hp hs hm hx
    have hx2 : x = 2 := by obtain ⟨q, _, hq⟩ := hx; simpa [targets] using hq.symm
    subst hx2
    cases n <;> cases d <;> simp [state, rg0, rgHelper, rgHelperRecv, rgPrepT, TH, theory,
      groupTheory, targets, ParaleanTargetNames.initExtra, Bool.forall_bool] at hp hs hm ⊢

/-- Owner `false` publishes the target under the epoch fence and writes its
publisher certificate on replica `true`. -/
theorem target_published : HR (state dlSentTarget rgReceivedHelper d12) eP2 k0 eTP := by
  have hp : NoNewPending preparedS (state dlSentTarget rgReceivedHelper d12) := by regs
  have hu : ParaleanTargetNames.update TH targets preparedS
      (state dlSentTarget rgReceivedHelper d12) eT0 = eTP := by
    refine ParaleanTargetNames.update_eq _ _ _ _ _ _ hp ?_
    intro x
    by_cases hx : x = 2
    · subst hx
      refine Or.inr ⟨true, ⟨⟨true, rfl, rfl⟩, by simp [TH, theory, groupTheory],
        by simp [state, rgPrepT, rgHelperRecv, rgHelper], by simp [state, rgReceivedHelper, rgPublished]⟩,
        fun d hd => ?_, by simp⟩
      cases d
      · simp [TH, theory, groupTheory, ParaleanTargetNames.NewTarget] at hd
      · rfl
    · refine Or.inl ⟨fun d hd => hx ?_, by simp [hx, ParaleanTargetNames.initExtra]⟩
      obtain ⟨⟨_, _, hq⟩, _⟩ := hd
      simpa [targets] using hq.symm
  have g := ParaleanTargetNames.guard_of_no_new_pending TH targets RT EN preparedS
    (state dlSentTarget rgReceivedHelper d12) eT0 hp (ParaleanTargetNames.publishOk_initExtra _ _ _ _ _)
  rw [hu] at g
  have h19 : HR (state dlSentTarget rgReceivedHelper d12) eC2 k0 eTP :=
    hstep target_prepared (publish_joint dlSentTarget rgPrepT rgReceivedHelper d11 true
        new_group_steps.2.2.1 (by simp [ack, put]) (by intro r; cases r <;> simp [disk0, put, ack]))
      (rguard_of hp) g (fenced_writes0 rfl (by nocat0))
      (ack_same (fun n d h1 h2 h3 => by
          cases n <;> cases d <;> simp [state, rgPrepT, rgHelperRecv, rgHelper, rg0,
            rgReceivedHelper, rgPublished] at h1 h2 h3)
        (fun n h => absurd rfl h) rfl) (cc_quiet rfl rfl)
  exact cstep h19 (.put false true true rfl rfl)

/-- Guarded accept of the target by worker `true`, its own certificate puts for
the target interleaved with manifest writes, the record's own acknowledgement,
acknowledgement and commit certificates under fence 0, durable catalogue commit,
and the guarded finish whose head change has `true`'s reply quorum. -/
theorem completed_hr : HR completedS eFull kFull eTP := by
  have h20 : HR (state dlAcceptedTarget rgReceived d12) eP2 k0 eTP :=
    wstep target_published (accept_joint dlSentTarget dlAcceptedTarget rgReceivedHelper rgReceived d12 true
        delivery_steps.2.2.2.2.2.2.1 group_steps.2.2.2.2.2.2.1
        (by simp [ack]) (by simp [put, ack]) rfl)
      (by regs) rfl
      (ack_same (fun n d _ _ _ => ⟨(), true, rfl, rfl, eP2_cert d⟩)
        (fun n h => absurd rfl h) rfl)
  have c5 : HR (state dlAcceptedTarget rgReceived d12) eC3 k0 eTP := cstep h20 (.put true false true rfl rfl)
  have h21 := pstep c5 (put_joint dlAcceptedTarget rgReceived d12 false (.manifest true) rfl) rfl rfl rfl
  have c6 : HR (state dlAcceptedTarget rgReceived d13) eFull k0 eTP := cstep h21 (.put true true true rfl rfl)
  have h22 := pstep c6 (put_joint dlAcceptedTarget rgReceived d13 true (.manifest true) rfl) rfl rfl rfl
  have h23 := pstep h22 (ack_joint dlAcceptedTarget rgReceived d14 (.manifest true)
    (by intro r; cases r <;> simp [disk0, put, ack]) trivial) rfl rfl rfl
  have h24 := pstep h23 (put_joint dlAcceptedTarget rgReceived d15 false (.catalog 1) rfl) rfl rfl rfl
  have h25 := pstep h24 (put_joint dlAcceptedTarget rgReceived d16 true (.catalog 1) rfl) rfl rfl rfl
  have h25a : HR (state dlAcceptedTarget rgReceived d18) eFull k0 eTP :=
    pstep h25 (ack_joint dlAcceptedTarget rgReceived d17 (.catalog 1)
      (by intro r; cases r <;> simp [disk0, put, ack]) trivial) rfl rfl rfl
  have q1 := ccstep h25a (.object false (.payload false) rfl (by simp [state, put, ack]))
  have q2 := ccstep q1 (.object true (.payload false) rfl (by simp [state, put, ack]))
  have q3 := ccstep q2 (.object false (.payload true) rfl (by simp [state, put, ack]))
  have q4 := ccstep q3 (.object true (.payload true) rfl (by simp [state, put, ack]))
  have q5 := ccstep q4 (.object false (.manifest true) rfl (by simp [state, put, ack]))
  have q6 := ccstep q5 (.object true (.manifest true) rfl (by simp [state, put, ack]))
  have q7 := ccstep q6 (.record false true rfl (by simp [state, put, ack, EN, encode])
    (by simp [state, rec0, tok, RT, recoveryTheory]))
  have q8 : HR (state dlAcceptedTarget rgReceived d18) eFull kFull eTP :=
    ccstep q7 (.record true true rfl (by simp [state, put, ack, EN, encode])
      (by simp [state, rec0, tok, RT, recoveryTheory]))
  have h26 : HR (state dlAcceptedTarget rgReceived d18 recCommitted) eFull kFull eTP :=
    wstep q8 recommit_joint (by regs) rfl
      (ack_same (fun n d h1 h2 _ => absurd (h1.symm.trans h2) (by decide))
        (fun n h => absurd rfl h) rfl) (hcc := cc_commit)
  refine wstep h26 (ParaleanProtocol.finish_step TH RT EN true true true guarded_finish_joint)
    (by regs) rfl
    (ack_same (fun n d h1 h2 _ => absurd (h1.symm.trans h2) (by decide)) ?_ rfl)
  intro n hn d _
  cases n
  · exact absurd (by simp [state, rgCommitted, rgReceived, rgPublished, rgReceivedHelper,
      rgHelper, rgPreparedHelper, rg0]) hn
  · exact eFull_quorum d

/-- A registry receive at worker `true`, guarded by marker acknowledgement and bytes. -/
theorem receive_base (dl : ParaleanProtocol.Example.Delivery) (rg rg' : Registry)
    (disk : ParaleanProtocol.Example.Disk) (rec : ParaleanProtocol.Example.Recovery) (g : Bool)
    (registry : ParaleanGroups.GroupsNext groupTheory rg (.receive true g) rg')
    (marker : disk.acknowledged (.publication g) = true)
    (bytes : disk.stored true (.publication g) = true) (live : disk.live true = true) :
    ParaleanProtocol.Next TH RT EN (state dl rg disk rec) (state dl rg' disk rec) := by
  refine .paired (.admission (.registry (.receive true g) trivial registry trivial) rfl)
    (.registry (.receive true g) (by intros; simp) registry trivial ?_)
  intro n d h
  cases h
  let ids := fun d => ∃ r, storageTheory.memberR r () = true ∧ disk.live r = true ∧
    disk.stored r (.publication d) = true
  exact ⟨(), ids, by intro d; rfl, ⟨true, rfl, live, bytes⟩, marker⟩

/-- A storage step at fence 1 that writes only record `false`'s catalogue object. -/
theorem zstep {disk disk' : ParaleanProtocol.Example.Disk} {eC : XC}
    (h : HR (state dlDone rgCommitted disk fRot) eFull eC eT1)
    (hb : ParaleanProtocol.Next TH RT EN (state dlDone rgCommitted disk fRot) (state dlDone rgCommitted disk' fRot))
    (hl : disk.live = disk'.live)
    (hold : ∀ x, disk.stored x (.catalog 1) = true) (hack : disk.acknowledged (.catalog 1) = true) :
    HR (state dlDone rgCommitted disk' fRot) eFull eC eT1 := by
  refine hstep h hb (rguard_of (by regs)) (tguard_of (by regs) (by pubs) (by upd)) ?_
    (ack_same (fun n d h1 h2 _ => absurd (h1.symm.trans h2) (by decide)) (fun n h => absurd rfl h) hl)
    (cc_quiet rfl hl)
  intro c hn
  cases c
  · exact fenced1 rfl
  · exfalso
    rcases hn with ⟨x, _, h2⟩ | ⟨_, h2⟩
    · have := hold x; simp [state, EN, encode] at h2; rw [this] at h2; cases h2
    · simp [state, EN, encode] at h2; rw [hack] at h2; cases h2

/-- The desktop forgets the catalogue IDs, the controller reassigns name `2` to
worker `true`, and the fence rotates to 1. Under fence 1, record `false` (rank-1
token) is first written to both replicas, acknowledged, and given a commit
certificate on both replicas. Replica `false` is then lost (its certificates with
it; the committer's replies remain), and both workers crash (worker `true` recovers). -/
theorem erased_hr : HR erasedS eLost kLost eT1 := by
  have l2 : HR (state dlDone rgCommitted d18 recForgotten) eFull kFull eTP :=
    pstep completed_hr (ParaleanProtocol.failure_step TH RT EN (.desktop forget_desktop)) rfl rfl rfl
  have l2' : HR (state dlDone rgCommitted d18 recForgotten) eFull kFull eT1 := rstep l2 2 true
  have l3 : HR rotS eFull kFull eT1 :=
    qstep l2' (ParaleanProtocol.recovery_step TH RT EN _ recForgotten fRot
        (.recovery (.rotateFence true) (by intro c epoch h; cases h) (by intro v h; cases h)
          recovery_steps.2.1))
      (by regs) rfl
      (ack_same (fun n d h1 h2 _ => absurd (h1.symm.trans h2) (by decide))
        (fun n h => absurd rfl h) rfl)
  have z1 : HR (state dlDone rgCommitted dZ1 fRot) eFull kFull eT1 :=
    zstep l3 (ParaleanProtocol.storage_step TH RT EN dlDone rgCommitted fRot d18 dZ1 (.Put false (.catalog 0))
        (ParaleanCompletionRecovery.Example.put_step d18 false _ rfl) trivial) rfl
      (by intro x; cases x <;> simp [put, ack]) (by simp [put, ack])
  have z2 : HR (state dlDone rgCommitted dZ2 fRot) eFull kFull eT1 :=
    zstep z1 (ParaleanProtocol.storage_step TH RT EN dlDone rgCommitted fRot dZ1 dZ2 (.Put true (.catalog 0))
        (ParaleanCompletionRecovery.Example.put_step dZ1 true _ rfl) trivial) rfl
      (by intro x; cases x <;> simp [dZ1, put, ack]) (by simp [dZ1, put, ack])
  have z3 : HR zS eFull kFull eT1 :=
    zstep z2 (ParaleanProtocol.storage_step TH RT EN dlDone rgCommitted fRot dZ2 dZ3 (.Ack (.catalog 0) ())
        (ParaleanCompletionRecovery.Example.ack_step dZ2 (.catalog 0)
          (by intro r; cases r <;> simp [dZ2, dZ1, disk0, put, ack])) trivial) rfl
      (by intro x; cases x <;> simp [dZ2, dZ1, put, ack]) (by simp [dZ2, dZ1, put, ack])
  have z4 := ccstep z3 (.record false false rfl (by simp [state, dZ3, put, ack, EN, encode])
    (by simp [state, fRot, recCommitted, rec0, tok, RT, recoveryTheory]))
  have z5 : HR zS eFull kZ eT1 :=
    ccstep z4 (.record true false rfl (by simp [state, dZ3, put, ack, EN, encode])
      (by simp [state, fRot, recCommitted, rec0, tok, RT, recoveryTheory]))
  have l1 : HR lostS eLost kLost eT1 := by
    refine hstep z5 (ParaleanProtocol.failure_step TH RT EN (.storage false destroyZ))
      (rguard_of (by regs)) (tguard_of (by regs) (by pubs) (by upd)) ?_ (ack_reg rfl) (cc_lost rfl)
    intro c hn
    exfalso
    rcases hn with ⟨x, h1, h2⟩ | ⟨h1, h2⟩
    · cases x <;> simp [state, lostZ] at h1 h2
      simp_all
    · simp [state, lostZ] at h1 h2; simp_all
  have k1 : HR (state dlC1 rgC1 lostZ fRot) eLost kLost eT1 :=
    qstep l1 (crash_joint false dlDone dlC1 rgCommitted rgC1 lostZ fRot crash_steps.1
        crash_steps.2.2.1) (by regs) rfl
      (ack_same (fun n d h1 _ _ => by simp [state, rgCommitted, rgReceived, rgPublished, rg0] at h1)
        (fun n h => absurd rfl h) rfl)
  have k2 : HR (state dlC2 rgC2 lostZ fRot) eLost kLost eT1 :=
    qstep k1 (crash_joint true dlC1 dlC2 rgC1 rgC2 lostZ fRot crash_steps.2.1
        crash_steps.2.2.2.1) (by regs) rfl
      (ack_same (fun n d _ h2 _ => by simp [state, rgC2] at h2) (fun n h => absurd rfl h) rfl)
  exact qstep k2 (recover_joint dlC2 rgC2 rgR lostZ fRot crash_steps.2.2.2.2) (by regs) rfl
    (ack_same (fun n d h1 h2 _ => absurd (h1.symm.trans h2) (by decide)) (fun n h => absurd rfl h) rfl)

/-- The certificate-guarded receive succeeds from the physical read on replica `true`.
The receiver is the new owner of name `2`, and the group is the head in its record. -/
theorem received_hr : HR receivedS eLost kLost eT1 :=
  qstep erased_hr (receive_base dlC2 rgR rgRecv lostZ fRot true new_group_steps.2.2.2
      (by simp [lostZ, dZ3, dZ2, dZ1, put, ack]) (by simp [lostZ, dZ3, dZ2, dZ1, put, ack]) rfl) (by regs) rfl
    (ack_same (fun n d _ _ _ => ⟨(), true, rfl, rfl, eLost_cert d⟩) (fun n h => absurd rfl h) rfl)

/-- Recovery scan, reconstruction and automatic selection of the fenced record. -/
theorem recovered_hr : HR recoveredS eLost kLost eT1 := by
  have r1 : HR (state dlC2 rgRecv lostZ fScan) eLost kLost eT1 :=
    qstep received_hr (ParaleanProtocol.recovery_step TH RT EN _ fRot fScan
        (.recovery (.enumerate ()) (by intro c epoch h; cases h)
          (ready_on lostZ (by simp [lostZ, dZ3, dZ2, dZ1, put, ack]) (by simp [lostZ, dZ3, dZ2, dZ1, put, ack])
            (by intro g; cases g <;> simp [lostZ, dZ3, dZ2, dZ1, put, ack]))
          recovery_steps.2.2.1))
      (by regs) rfl
      (ack_same (fun n d h1 h2 _ => absurd (h1.symm.trans h2) (by decide))
        (fun n h => absurd rfl h) rfl)
  have r2 : HR (state dlC2 rgRecv lostZ fRebuilt) eLost kLost eT1 :=
    qstep r1 (ParaleanProtocol.recovery_step TH RT EN _ fScan fRebuilt
        (.recovery .reconstruct (by intro c epoch h; cases h) (by intro v h; cases h)
          recovery_steps.2.2.2.1))
      (by regs) rfl
      (ack_same (fun n d h1 h2 _ => absurd (h1.symm.trans h2) (by decide))
        (fun n h => absurd rfl h) rfl)
  exact qstep r2 (ParaleanProtocol.recovery_step TH RT EN _ fRebuilt fAuto
      (.recovery (.automatic true) (by intro c epoch h; cases h) (by intro v h; cases h)
        recovery_steps.2.2.2.2.1))
    (by regs) rfl
    (ack_same (fun n d h1 h2 _ => absurd (h1.symm.trans h2) (by decide))
      (fun n h => absurd rfl h) rfl)

/-- Joint non-vacuity of the hardened protocol. On one trace, every step of which
satisfies all five guards: the current owner of the target name (worker `false`,
epoch 0) prepares the required target holding a verified receipt, and publishes
it, which records it as the name's head; before the committer's own certificate
puts nobody holds a certificate quorum for it; the committer (worker `true`)
collects replies for both groups from both replicas; the catalogue record is
acknowledged, its manifest and payloads are certified and its commit certificate
is written under fence 0 on both replicas; the catalogue is committed (adoption
needs those certificates) and the guarded finish commits a checkpoint containing
the target; the desktop is lost; the controller reassigns the name to worker
`true` (epoch 1), keeping the recorded head; the fence rotates to 1; record
`false` is first written, acknowledged and given a commit certificate under
fence 1; a replica is lost; every worker index is erased; a physical certificate
scan finds exactly the published groups; the new owner receives the recorded
head through a certificate read; and recovery automatically selects the record
whose commit certificate passed the fence check. -/
theorem hardened_nonvacuous :
    -- prepare: current owner, receipt, realized required target
    (∃ eF, ParaleanHardened.Reachable TH RT EN cfg (preparedS, (eF, eC2, k0, eT0))) ∧
    preparedS.admission.protocol.registry.pending false true = true ∧
    ParaleanPublicationReceipts.HeldReceipt TH preparedS.admission.delivery true ∧
    deliveryTheory.required true = true ∧ deliveryTheory.realizes true true = true ∧
    groupTheory.member true (targets.targetName true) = true ∧
    eT0.owner (targets.targetName true) = false ∧
    -- publish, certificates, commit, finish
    (∀ n, ¬CertQuorumBy TH eP2 n true) ∧
    (∃ eF, ParaleanHardened.Reachable TH RT EN cfg (completedS, (eF, eFull, kFull, eTP)) ∧
      eF true = some 0) ∧
    eTP.head (targets.targetName true) = some true ∧
    completedS.admission.protocol.registry.published true = true ∧
    (∀ d x, eFull.certReply true d x = true) ∧ (∀ d, CertQuorumBy TH eFull true d) ∧
    completedS.admission.delivery.done true = true ∧
    completedS.admission.protocol.registry.head true = true ∧
    groupTheory.contents (completedS.admission.protocol.registry.head true) true = true ∧
    completedS.recovery.committed true = true ∧
    CatReady TH RT completedS kFull true ∧ kFull.certFence true = some 0 ∧
    RT.tokenRank (cfg.recordToken true) = completedS.recovery.fence ∧
    -- reassignment, rotation, a fenced catalogue write and commit record at fence 1
    eT1.owner (targets.targetName true) = true ∧ eT1.epoch (targets.targetName true) = 1 ∧
    eT1.head (targets.targetName true) = some true ∧
    (∃ eF, ParaleanHardened.Reachable TH RT EN cfg (zS, (eF, eFull, kZ, eT1)) ∧
      eF false = some 1) ∧
    zS.recovery.fence = 1 ∧ RT.tokenRank (cfg.recordToken false) = 1 ∧
    kZ.certFence false = some 1 ∧ kZ.rcert true false = true ∧
    -- failures, index erasure, physical scan
    (∃ eF, ParaleanHardened.Reachable TH RT EN cfg (erasedS, (eF, eLost, kLost, eT1))) ∧
    erasedS.admission.protocol.storage.live false = false ∧
    erasedS.recovery.fence = 1 ∧ (∀ c, erasedS.recovery.known c = false) ∧
    (∀ n d, erasedS.admission.protocol.registry.known n d = false) ∧
    (∀ d, certScan TH erasedS eLost () d) ∧
    (∀ d, certScan TH erasedS eLost () d → erasedS.admission.protocol.registry.published d = true) ∧
    -- the new owner receives the recorded head; fenced recovery
    (∃ eF, ParaleanHardened.Reachable TH RT EN cfg (receivedS, (eF, eLost, kLost, eT1))) ∧
    receivedS.admission.protocol.registry.known true true = true ∧
    (∃ eF, ParaleanHardened.Reachable TH RT EN cfg (recoveredS, (eF, eLost, kLost, eT1)) ∧
      eF true = some 0) ∧
    recoveredS.recovery.selected = true ∧ recoveredS.recovery.selectedRecord = true ∧
    kLost.certFence recoveredS.recovery.selectedRecord =
      some (RT.tokenRank (cfg.recordToken recoveredS.recovery.selectedRecord)) ∧
    recoveredS.recovery.fence = 1 := by
  obtain ⟨eC, hC⟩ := completed_hr
  obtain ⟨eE, hE⟩ := erased_hr
  obtain ⟨eR, hR⟩ := recovered_hr
  have hZ : HR zS eFull kZ eT1 := by
    -- re-derive the fence-1 prefix of `erased_hr`
    have l2 : HR (state dlDone rgCommitted d18 recForgotten) eFull kFull eTP :=
      pstep completed_hr (ParaleanProtocol.failure_step TH RT EN (.desktop forget_desktop)) rfl rfl rfl
    have l3 : HR rotS eFull kFull eT1 :=
      qstep (rstep l2 2 true) (ParaleanProtocol.recovery_step TH RT EN _ recForgotten fRot
          (.recovery (.rotateFence true) (by intro c epoch h; cases h) (by intro v h; cases h)
            recovery_steps.2.1))
        (by regs) rfl
        (ack_same (fun n d h1 h2 _ => absurd (h1.symm.trans h2) (by decide))
          (fun n h => absurd rfl h) rfl)
    have z1 : HR (state dlDone rgCommitted dZ1 fRot) eFull kFull eT1 :=
      zstep l3 (ParaleanProtocol.storage_step TH RT EN dlDone rgCommitted fRot d18 dZ1 (.Put false (.catalog 0))
          (ParaleanCompletionRecovery.Example.put_step d18 false _ rfl) trivial) rfl
        (by intro x; cases x <;> simp [put, ack]) (by simp [put, ack])
    have z2 : HR (state dlDone rgCommitted dZ2 fRot) eFull kFull eT1 :=
      zstep z1 (ParaleanProtocol.storage_step TH RT EN dlDone rgCommitted fRot dZ1 dZ2 (.Put true (.catalog 0))
          (ParaleanCompletionRecovery.Example.put_step dZ1 true _ rfl) trivial) rfl
        (by intro x; cases x <;> simp [dZ1, put, ack]) (by simp [dZ1, put, ack])
    have z3 : HR zS eFull kFull eT1 :=
      zstep z2 (ParaleanProtocol.storage_step TH RT EN dlDone rgCommitted fRot dZ2 dZ3 (.Ack (.catalog 0) ())
          (ParaleanCompletionRecovery.Example.ack_step dZ2 (.catalog 0)
            (by intro r; cases r <;> simp [dZ2, dZ1, disk0, put, ack])) trivial) rfl
        (by intro x; cases x <;> simp [dZ2, dZ1, put, ack]) (by simp [dZ2, dZ1, put, ack])
    have z4 := ccstep z3 (.record false false rfl (by simp [state, dZ3, put, ack, EN, encode])
      (by simp [state, fRot, recCommitted, rec0, tok, RT, recoveryTheory]))
    exact ccstep z4 (.record true false rfl (by simp [state, dZ3, put, ack, EN, encode])
      (by simp [state, fRot, recCommitted, rec0, tok, RT, recoveryTheory]))
  obtain ⟨eZ, hZ⟩ := hZ
  have fC := (ParaleanCatalogFencing.catalog_objects_fenced TH RT EN tok assumptions
    recovery_assumptions (ParaleanHardened.reachable_fencing TH RT EN cfg hC)).2 true rfl
  have fZ := (ParaleanCatalogFencing.present_fenced TH RT EN tok
    (ParaleanHardened.reachable_fencing TH RT EN cfg hZ)) false
    (Or.inl ⟨true, by simp [zS, state, dZ3, dZ2, dZ1, put, ack, EN, encode]⟩)
  have sR := (ParaleanHardened.hardened_safe TH RT EN cfg assumptions recovery_assumptions hR).2.2.2.1 rfl
  have hb := ParaleanAckCertificates.scan_between TH RT EN assumptions
    (ParaleanHardened.reachable_certificates TH RT EN cfg hE) () (fun x hx => hx)
  refine ⟨target_prepared, rfl, held_target, rfl, rfl, rfl, rfl, eP2_no_quorum,
    ⟨eC, hC, ?_⟩, by simp [targets], rfl, eFull_reply, eFull_quorum, rfl, rfl,
    rfl, rfl, kFull_ready _, by simp [kFull, putRecord], rfl, ?_, ?_, ?_, ⟨eZ, hZ, ?_⟩, rfl,
    by simp [cfg, tok, RT, recoveryTheory], by simp [kZ, putRecord],
    by simp [kZ, kZ1, putRecord], ⟨eE, hE⟩, rfl, rfl, fun _ => rfl, fun _ _ => rfl,
    fun d => (hb d).1 ⟨true, eLost_quorum d⟩, fun d => (hb d).2, received_hr, rfl,
    ⟨eR, hR, ?_⟩, rfl, rfl, ?_, rfl⟩
  · simpa [tok, RT, recoveryTheory] using fC.1
  · simp [ParaleanTargetNames.reassign, targets]
  · simp [ParaleanTargetNames.reassign, ParaleanTargetNames.initExtra, targets]
  · simp [ParaleanTargetNames.reassign, targets]
  · simpa [cfg, tok, RT, recoveryTheory] using fZ.1
  · simpa [tok, RT, recoveryTheory, cfg, fAuto, fRebuilt, fScan, fRot, state] using sR.1
  · simpa [tok, RT, recoveryTheory, cfg, fAuto, fRebuilt, fScan, fRot, state] using sR.2

end
end ParaleanHardened.Example

#print axioms ParaleanHardened.Example.instance_assumptions
#print axioms ParaleanHardened.Example.hardened_nonvacuous
