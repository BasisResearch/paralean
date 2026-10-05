import Paralean.Hardened

/-! Joint non-vacuity of the hardened protocol on the
`ParaleanCompletionRecovery.Example` instance (two workers, two groups, two
replicas with write quorum = both and read quorum = replica `true`, fence tokens
of rank 0/1, record `false` a child of record `true`).

Main trace (`hardened_nonvacuous`), every step a hardened step: worker `false`
owns name `2`; it prepares and publishes a helper and the required target under
held receipts (the target becomes the name's recorded head). Each publication
writes the publisher's certificates for the group on both replicas in the same
step. Worker `true` receives each group through the physical certificate read,
then puts its own certificates for both groups on both replicas. The catalogue writer's reply log records each
acknowledgement; from it the manifest, payload and commit certificates of record
`true` are written (commit certificate under fence 0) and the catalogue commits.
The desktop is lost, the controller reassigns name `2` to worker `true`, the fence
rotates to 1, and record `false` (rank-1 token) is first written and acknowledged
with its manifest, but never certified. A replica is lost, every worker index is
erased, a certificate scan rediscovers the published groups, the new owner
receives the recorded head, and recovery enumerates by an implementation step
(`ParaleanHardened.scan_enumerate_hardened`) whose scan is computed through
`codec` from the answers of the surviving read quorum. The scan decodes both
records and rejects record `false` (no commit certificate); recovery selects
record `true`.

Second trace (`hardened_scan_adoption`), sharing the prefix up to record `false`'s
acknowledgement: record `false`'s manifest and commit certificates (fence 1) are
written, a replica is lost, and the same implementation scan now adopts record
`false` through `enumerate` (the adoption guard holds by certificates) and
recovery selects it automatically as the unique head. The two traces have the same
catalogue bytes; selection differs only by certificates.

`stale_owner_publish_blocked`: after a reassignment, the former owner's
publication of its pending target is a base protocol step but no hardened step. -/
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
  forget_desktop delivery_steps group_steps CState Scan scanBit)
open ParaleanProtocol.Example (state d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17
  d18 lostDisk put_joint ack_joint prepare_joint publish_joint control_joint accept_joint
  catalogue_commit_joint guarded_finish_joint destroy_replica)
open ParaleanAckCertificates.Example (dlC1 dlC2 rgC1 rgC2 rgR crash_steps crash_joint recover_joint)
open ParaleanCatalogFencing.Example (fRot fScan fRebuilt fAuto recovery_steps)
attribute [local instance] Classical.propDecidable

abbrev TH := theory
abbrev RT := recoveryTheory
abbrev EN := encode
abbrev X := ParaleanAckCertificates.Extra Bool Bool Bool
abbrev XT := ParaleanTargetNames.Extra Bool Bool (Fin 3)
abbrev Obj := StoredObject Bool Bool
abbrev XC := ParaleanCatalogCertificates.Extra Bool Bool Obj
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

/-- The instance's scan type carries any decode/readiness pair: a concrete
`ScanCodec`. -/
def codec : ParaleanCatalogCertificates.ScanCodec RT where
  build := fun D R => ((D false, D true), (R false, R true))
  decoded_build := by intro D R c; cases c <;> rfl
  ready_build := by intro D R c; cases c <;> rfl

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

/-- No group is newly published by a concrete step. -/
macro "nopub" : tactic => `(tactic| (rintro d ⟨h1, h2⟩; cases d <;>
  simp [state, rg0, rgPreparedHelper, rgHelper, rgHelperRecv, rgPrepT, rgPublished,
    rgReceivedHelper, rgReceived, rgCommitted, rgC1, rgC2, rgR, rgRecv] at h1 h2))

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

/-! ### The catalogue writer's reply log -/

/-- The reply log after the writer's acknowledgement of `o` reached both replicas. -/
def ackR (e : XC) (o : Obj) : XC :=
  { e with reply := fun o' x => if o' = o then true else e.reply o' x }

/-- A step whose disk acknowledges `o`, held by every (live) replica, records a
reply for `o` from every replica and changes nothing else. -/
theorem advance_ack (dl dl' : ParaleanProtocol.Example.Delivery) (rg rg' : Registry)
    (d : ParaleanProtocol.Example.Disk) (rec rec' : ParaleanProtocol.Example.Recovery) (e : XC) (o : Obj)
    (hlive : ∀ x, d.live x = true) (hst : ∀ x, d.stored x o = true) (hnew : d.acknowledged o = false) :
    ParaleanCatalogCertificates.advance (state dl rg d rec) (state dl' rg' (ack d o) rec') e = ackR e o := by
  rw [ParaleanCatalogCertificates.advance,
    ParaleanCatalogCertificates.clearLost_same _ _ e (by simp [state, ack])]
  cases e with
  | mk rc oc cf rp =>
    simp only [ParaleanCatalogCertificates.logReplies, ackR, ParaleanCatalogCertificates.Extra.mk.injEq,
      true_and]
    funext o' x
    by_cases h : o' = o
    · subst h; simp [state, ack, hnew, hlive, hst]
    · have h' : ¬ o = o' := fun h'' => h h''.symm
      simp [state, ack, h, h']

theorem cc_quiet {s t : CState} {eC : XC}
    (hc : t.recovery.committed = s.recovery.committed)
    (hl : s.admission.protocol.storage.live = t.admission.protocol.storage.live)
    (hk : s.admission.protocol.storage.acknowledged = t.admission.protocol.storage.acknowledged := by rfl) :
    ParaleanCatalogCertificates.Guard TH RT EN tok s eC t eC := by
  refine Or.inl ⟨?_, (ParaleanCatalogCertificates.advance_same s t eC hl hk).symm⟩
  intro c h1 h2; rw [hc, h1] at h2; cases h2

theorem cc_adv {s t : CState} {eC eC' : XC}
    (hc : t.recovery.committed = s.recovery.committed)
    (hadv : ParaleanCatalogCertificates.advance s t eC = eC') :
    ParaleanCatalogCertificates.Guard TH RT EN tok s eC t eC' := by
  refine Or.inl ⟨?_, hadv.symm⟩
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
    (hl : s.admission.protocol.storage.live = t.admission.protocol.storage.live)
    (hp : ∀ d, ¬ParaleanAckCertificates.NewPub s t d := by nopub) :
    ParaleanAckCertificates.Guard TH RT EN s eA t eA := by
  refine Or.inl ⟨hr, hc, ?_⟩
  rw [ParaleanAckCertificates.clearLost_same s t eA hl]
  exact ParaleanAckCertificates.publishWrite_quiet TH s t eA hp

/-- A publication step: the same transaction writes publisher `n`'s certificates
for `d` on both replicas (the write quorum) and records the replies. -/
theorem ack_pub {s t : CState} {eA : X}
    (hr : ParaleanAckCertificates.ReceiveGuard TH s eA t)
    (hc : ParaleanAckCertificates.CommitGuard TH s eA t)
    (hl : s.admission.protocol.storage.live = t.admission.protocol.storage.live)
    (n d : Bool) (hnew : ParaleanAckCertificates.NewPub s t d)
    (hk : t.admission.protocol.registry.known n d = true)
    (hw : ∀ x, t.admission.protocol.storage.live x = true) :
    ParaleanAckCertificates.Guard TH RT EN s eA t (ParaleanAckCertificates.putQuorum TH eA n () d) := by
  refine Or.inl ⟨hr, hc, ?_⟩
  rw [ParaleanAckCertificates.clearLost_same s t eA hl]
  exact Or.inr ⟨n, (), d, hnew, hk, fun x _ => hw x, rfl⟩

theorem ack_reg {s t : CState} {eA : X}
    (hreg : t.admission.protocol.registry = s.admission.protocol.registry) :
    ParaleanAckCertificates.Guard TH RT EN s eA t (ParaleanAckCertificates.clearLost s t eA) := by
  refine Or.inl ⟨?_, ?_, ?_⟩
  · intro n d h1 h2 _; rw [hreg, h1] at h2; cases h2
  · intro n h; rw [hreg] at h; exact absurd rfl h
  · exact ParaleanAckCertificates.publishWrite_quiet TH s t _
      (ParaleanAckCertificates.no_new_pub_of_same s t (by rw [hreg]))

/-- A step creating no pending bit under fence 0. -/
theorem wstep {s t : CState} {eA eA' : X} {eC eC' : XC} {eT : XT} (h : HR s eA eC eT)
    (hb : ParaleanProtocol.Next TH RT EN s t) (hp : NoNewPending s t)
    (hf : s.recovery.fence = 0)
    (ha : ParaleanAckCertificates.Guard TH RT EN s eA t eA')
    (hpub : ParaleanTargetNames.PublishOk TH targets s eT t := by pubs)
    (hu : ParaleanTargetNames.update TH targets s t eT = eT := by upd)
    (h0 : NoCat0 t := by nocat0)
    (hcc : ParaleanCatalogCertificates.Guard TH RT EN tok s eC t eC' := by exact cc_quiet rfl rfl) :
    HR t eA' eC' eT :=
  hstep h hb (rguard_of hp) (tguard_of hp hpub hu) (fenced_writes0 hf h0) ha hcc

/-- A registry-preserving, liveness-preserving step under fence 0. -/
theorem pstep {s t : CState} {eA : X} {eC eC' : XC} {eT : XT} (h : HR s eA eC eT)
    (hb : ParaleanProtocol.Next TH RT EN s t)
    (hreg : t.admission.protocol.registry = s.admission.protocol.registry)
    (hl : s.admission.protocol.storage.live = t.admission.protocol.storage.live)
    (hf : s.recovery.fence = 0)
    (h0 : NoCat0 t := by nocat0)
    (hc : t.recovery.committed = s.recovery.committed := by rfl)
    (hadv : ParaleanCatalogCertificates.advance s t eC = eC' := by
      exact ParaleanCatalogCertificates.advance_same _ _ _ (by rfl) (by rfl)) : HR t eA eC' eT := by
  have ha := ack_reg (eA := eA) hreg
  rw [ParaleanAckCertificates.clearLost_same s t eA hl] at ha
  exact wstep h hb (fun n d h' => by rw [hreg] at h'; exact h') hf ha
    (ParaleanTargetNames.publishOk_of_no_new_published _ _ _ _ _
      (fun d h' => by rw [hreg] at h'; exact h'))
    (ParaleanTargetNames.update_same _ _ _ _ _ (fun n d h' => by rw [hreg] at h'; exact h')
      (fun d h' => by rw [hreg] at h'; exact h')) h0 (cc_adv hc hadv)

/-- A step that writes no catalogue bytes (any fence). -/
theorem qstep {s t : CState} {eA eA' : X} {eC eC' : XC} {eT : XT} (h : HR s eA eC eT)
    (hb : ParaleanProtocol.Next TH RT EN s t) (hp : NoNewPending s t)
    (hst : t.admission.protocol.storage = s.admission.protocol.storage)
    (ha : ParaleanAckCertificates.Guard TH RT EN s eA t eA')
    (hpub : ParaleanTargetNames.PublishOk TH targets s eT t := by pubs)
    (hu : ParaleanTargetNames.update TH targets s t eT = eT := by upd)
    (hcc : ParaleanCatalogCertificates.Guard TH RT EN tok s eC t eC' := by exact cc_quiet rfl rfl) :
    HR t eA' eC' eT :=
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
    (hc : ParaleanCatalogCertificates.CertStep TH RT EN tok s eC eC') : HR s eA eC' eT := by
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

/-- Recovery's implementation enumerate: the scan is computed through `codec` from
the answers of read quorum `()` (replica `true`), all of whose members answered.
No ghost precondition is checked; `scan_enumerate_hardened` derives the step. -/
theorem scanEnum_of {s : CState} {eC : XC}
    (hq : ParaleanCatalogCertificates.Responded TH s ()) (rec' : ParaleanProtocol.Example.Recovery)
    (he : ParaleanRecovery.scanEffect RT (ParaleanCatalogCertificates.certScanValue codec TH EN s eC ())
      s.recovery = rec') :
    ParaleanCatalogCertificates.ScanEnumerate TH RT EN codec (s, eC) (⟨s.admission, rec'⟩, eC) :=
  ⟨(), hq, by rw [he]⟩

theorem sstep {s : CState} {eA : X} {eC : XC} {eT : XT} (h : HR s eA eC eT)
    (hq : ParaleanCatalogCertificates.Responded TH s ()) (rec' : ParaleanProtocol.Example.Recovery)
    (he : ParaleanRecovery.scanEffect RT (ParaleanCatalogCertificates.certScanValue codec TH EN s eC ())
      s.recovery = rec') :
    HR ⟨s.admission, rec'⟩ eA eC eT := by
  obtain ⟨eF, h⟩ := h
  exact ⟨eF, .step h (ParaleanHardened.scan_enumerate_hardened TH RT EN cfg assumptions
    recovery_assumptions codec (e := (eF, eA, eC, eT)) h (scanEnum_of hq rec' he))⟩

/-! ## Publication certificate extras

Each publication by publisher `false` writes its certificates for the group on
both replicas (the write quorum) in the publication step. Committer `true` then
puts each group on both replicas itself, after receiving it: its commit guard
reads only its own replies. -/

open ParaleanAckCertificates (putCert putQuorum clearLost initExtra certScan CertQuorumBy)

def eP1 : X := putQuorum TH initExtra false () false
def eC1 : X := putCert eP1 true false false
def eC2 : X := putCert eC1 true true false
def eP2 : X := putQuorum TH eC2 false () true
def eC3 : X := putCert eP2 true false true
def eFull : X := putCert eC3 true true true

theorem eP1_cert (x : Bool) : eP1.cert x false = true := by
  cases x <;> simp [eP1, putQuorum, initExtra, TH, theory, storageTheory]
theorem eP2_cert (d : Bool) : eP2.cert true d = true := by
  cases d <;> simp [eP2, eC2, eC1, eP1, putQuorum, putCert, initExtra, TH, theory, storageTheory]
theorem eFull_reply (d x : Bool) : eFull.certReply true d x = true := by
  cases d <;> cases x <;> simp [eFull, eC3, eP2, eC2, eC1, eP1, putQuorum, putCert, initExtra]
theorem eFull_quorum (d : Bool) : CertQuorumBy TH eFull true d := ⟨(), fun x _ => eFull_reply d x⟩
/-- The target's publication wrote the publisher's certificate quorum. -/
theorem eP2_publisher_quorum : CertQuorumBy TH eP2 false true :=
  ⟨(), fun x _ => by cases x <;> simp [eP2, putQuorum, TH, theory, storageTheory]⟩
/-- Before its own puts for the target the committer holds no quorum for it. -/
theorem eP2_committer_none : ¬CertQuorumBy TH eP2 true true := by
  rintro ⟨w, hw⟩
  have := hw false rfl
  simp [eP2, eC2, eC1, eP1, putQuorum, putCert, initExtra] at this

/-! ## Catalogue reply log and certificates

Each acknowledgement of an object adds the writer's replies for it (`ackR`). From
those replies the writer puts the certificates of record `true`'s payloads and
manifest, and its commit certificate under fence 0, each as one quorum write. -/

open ParaleanCatalogCertificates (putRecord putObject CatReady)

def kA1 : XC := ackR k0 (.payload false)
def kA2 : XC := ackR kA1 (.publication false)
def kA3 : XC := ackR kA2 (.payload true)
def kA4 : XC := ackR kA3 (.publication true)
def kA5 : XC := ackR kA4 (.manifest true)
def kA6 : XC := ackR kA5 (.catalog 1)
def k1 : XC := putObject TH kA6 () (.payload false)
def k2 : XC := putObject TH k1 () (.payload true)
def k3 : XC := putObject TH k2 () (.manifest true)
def kFull : XC := putRecord TH k3 () true 0
/-- Record `false`'s object and manifest are acknowledged under fence 1. -/
def kZ0 : XC := ackR kFull (.catalog 0)
def kZ : XC := ackR kZ0 (.manifest false)
/-- Second trace only: record `false`'s manifest and commit certificates. -/
def kB1 : XC := putObject TH kZ () (.manifest false)
def kB : XC := putRecord TH kB1 () false 1

attribute [local simp] kA1 kA2 kA3 kA4 kA5 kA6 k1 k2 k3 kFull kZ0 kZ kB1 kB ackR
  ParaleanCatalogCertificates.putRecord ParaleanCatalogCertificates.putObject
  ParaleanCatalogCertificates.initExtra

theorem kFull_ready (s : CState) : CatReady TH RT s kFull true := by
  refine ⟨⟨(), fun x _ _ => ?_⟩, ⟨(), fun x _ _ => ?_⟩, fun d _ => ⟨(), fun x _ _ => ?_⟩⟩ <;>
    (try cases d) <;> cases x <;> simp [TH, theory, storageTheory, RT, recoveryTheory]

theorem reply_quorum (e : XC) (o : Obj) (h : ∀ x, e.reply o x = true) :
    ParaleanCatalogCertificates.ReplyQuorum TH e o := ⟨(), fun x _ => h x⟩

/-! ## States -/

abbrev preparedS : CState := state dlSentTarget rgPrepT d11
abbrev completedS : CState := state dlDone rgCommitted d18 recCommitted

def dZ1 := put d18 false (.catalog 0)
def dZ2 := put dZ1 true (.catalog 0)
def dZ3 := ack dZ2 (.catalog 0)
def dM1 := put dZ3 false (.manifest false)
def dM2 := put dM1 true (.manifest false)
def dM3 := ack dM2 (.manifest false)
def lostZ : ParaleanProtocol.Example.Disk :=
  { dM3 with live := id, stored := fun r o => if r then dM3.stored r o else false }
attribute [local simp] dZ1 dZ2 dZ3 dM1 dM2 dM3 lostZ

abbrev rotS : CState := state dlDone rgCommitted d18 fRot
abbrev zS : CState := state dlDone rgCommitted dM3 fRot
abbrev lostS : CState := state dlDone rgCommitted lostZ fRot
def eLost : X := clearLost zS lostS eFull
def kLost : XC := ParaleanCatalogCertificates.advance zS lostS kZ
def kBLost : XC := ParaleanCatalogCertificates.advance zS lostS kB
abbrev erasedS : CState := state dlC2 rgR lostZ fRot
abbrev receivedS : CState := state dlC2 rgRecv lostZ fRot
abbrev scannedS : CState := state dlC2 rgRecv lostZ fScan
abbrev recoveredS : CState := state dlC2 rgRecv lostZ fAuto

theorem eLost_cert (d : Bool) : eLost.cert true d = true := by
  cases d <;> simp [eLost, clearLost, lostS, zS, state, eFull, eC3, eP2,
    eC2, eC1, eP1, putQuorum, putCert, initExtra, put, ack, TH, theory, storageTheory]
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
  refine Or.inl ⟨?_, (ParaleanCatalogCertificates.advance_same _ _ _ rfl rfl).symm⟩
  intro c h1 h2
  cases c
  · simp [state, recCommitted, rec0] at h2
  · exact kFull_ready _

theorem destroyZ : ParaleanGroupComposition.StorageNext storageTheory dM3 (.Lose false) lostZ := by
  simp only [ParaleanGroupComposition.StorageNext, Durability.Next, Durability.NextAct, Durability.Lose.ext.derived_eq]
  dsimp [Durability.Lose.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanGroupComposition.diskFieldRep,
    Veil.canonicalFieldRepresentation]
  simp [storageTheory, disk0, put, ack, Veil.FieldRepresentation.setSingle,
    Veil.CanonicalField.set, Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry,
    Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]

/-! ## The trace -/

/-- Helper receipt in flight; owner `false` prepares and publishes the helper. -/
theorem helper_published : HR (state dlSentHelper rgHelper d6) eP1 kA2 eT0 := by
  have h0 := hr_initial
  have h1 := pstep h0 (control_joint dl0 dlStartedHelper rg0 d0 (.start true false) trivial
    delivery_steps.2.1) rfl rfl rfl
  have h2 := pstep h1 (control_joint dlStartedHelper dlSentHelper rg0 d0 (.send false) trivial
    delivery_steps.2.2.1) rfl rfl rfl
  have h3 := pstep h2 (put_joint dlSentHelper rg0 d0 false (.payload false) rfl) rfl rfl rfl
  have h4 := pstep h3 (put_joint dlSentHelper rg0 d1 true (.payload false) rfl) rfl rfl rfl
  have h5 : HR (state dlSentHelper rg0 d3) initExtra kA1 eT0 :=
    pstep h4 (ack_joint dlSentHelper rg0 d2 (.payload false)
      (by intro r; cases r <;> simp [disk0, put]) trivial) rfl rfl rfl
      (hadv := advance_ack _ _ _ _ _ _ _ _ _ (fun x => rfl) (by intro x; cases x <;> simp [disk0, put])
        (by simp [disk0, put]))
  have h6 := pstep h5 (put_joint dlSentHelper rg0 d3 false (.publication false) rfl) rfl rfl rfl
  have h7 := pstep h6 (put_joint dlSentHelper rg0 d4 true (.publication false) rfl) rfl rfl rfl
  have held : ParaleanPublicationReceipts.HeldReceipt TH dlSentHelper false := ⟨false, rfl, rfl, rfl, rfl⟩
  have h8 : HR (state dlSentHelper rgPreparedHelper d5) initExtra kA1 eT0 := by
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
    (ack_pub (s := state dlSentHelper rgPreparedHelper d5) (t := state dlSentHelper rgHelper d6)
      (fun n d _ _ h3 => by simp [state, rgPreparedHelper, rg0] at h3)
      (fun n h => absurd rfl h) rfl false false
      ⟨by simp [state, rgPreparedHelper, rg0], by simp [state, rgHelper, rg0]⟩
      (by simp [state, rgHelper, rg0]) (fun x => rfl)) (hu := update_nontarget (by regs) (by
        intro d h1 h2; cases d <;> simp [state, rgPreparedHelper, rgHelper, rg0] at h1 h2 ⊢))
    (hcc := cc_adv rfl (advance_ack _ _ _ _ _ _ _ _ _ (fun x => rfl)
      (by intro x; cases x <;> simp [disk0, put, ack]) (by simp [disk0, put, ack])))

theorem held_target : ParaleanPublicationReceipts.HeldReceipt TH dlSentTarget true :=
  ⟨true, rfl, rfl, rfl, rfl⟩

/-- Worker `true` receives the helper through the physical read of the
publisher's certificate and puts its own helper certificates on both replicas;
the target receipt is sent and owner `false` prepares the target while holding it. -/
theorem target_prepared : HR preparedS eC2 kA3 eT0 := by
  have c1 := helper_published
  have h10 : HR (state dlAcceptedHelper rgHelperRecv d6) eP1 kA2 eT0 :=
    wstep c1 (accept_joint dlSentHelper dlAcceptedHelper rgHelper rgHelperRecv d6 false
        delivery_steps.2.2.2.1 new_group_steps.1 (by simp [put, ack]) (by simp [put, ack]) rfl)
      (by regs) rfl
      (ack_same (fun n d h1 h2 _ => ⟨(), true, rfl, rfl, by
          cases n <;> cases d <;> simp [state, rgHelper, rgHelperRecv, rg0] at h1 h2 ⊢
          exact eP1_cert true⟩)
        (fun n h => absurd rfl h) rfl)
  have c2 : HR (state dlAcceptedHelper rgHelperRecv d6) eC1 kA2 eT0 := cstep h10 (.put true false false rfl rfl)
  have c3 : HR (state dlAcceptedHelper rgHelperRecv d6) eC2 kA2 eT0 := cstep c2 (.put true true false rfl rfl)
  have h11 := pstep c3 (put_joint dlAcceptedHelper rgHelperRecv d6 false (.payload true) rfl) rfl rfl rfl
  have h12 := pstep h11 (put_joint dlAcceptedHelper rgHelperRecv d7 true (.payload true) rfl) rfl rfl rfl
  have h13 : HR (state dlAcceptedHelper rgHelperRecv d9) eC2 kA3 eT0 :=
    pstep h12 (ack_joint dlAcceptedHelper rgHelperRecv d8 (.payload true)
      (by intro r; cases r <;> simp [disk0, put, ack]) trivial) rfl rfl rfl
      (hadv := advance_ack _ _ _ _ _ _ _ _ _ (fun x => rfl)
        (by intro x; cases x <;> simp [disk0, put, ack]) (by simp [disk0, put, ack]))
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

/-- Owner `false` publishes the target under the epoch fence; the same step writes
its publisher certificates on both replicas. -/
theorem target_published : HR (state dlSentTarget rgReceivedHelper d12) eP2 kA4 eTP := by
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
  exact hstep target_prepared (publish_joint dlSentTarget rgPrepT rgReceivedHelper d11 true
        new_group_steps.2.2.1 (by simp [ack, put]) (by intro r; cases r <;> simp [disk0, put, ack]))
      (rguard_of hp) g (fenced_writes0 rfl (by nocat0))
      (ack_pub (s := preparedS) (t := state dlSentTarget rgReceivedHelper d12) (fun n d h1 h2 h3 => by
          cases n <;> cases d <;> simp [state, rgPrepT, rgHelperRecv, rgHelper, rg0,
            rgReceivedHelper, rgPublished] at h1 h2 h3)
        (fun n h => absurd rfl h) rfl false true
        ⟨by simp [state, rgPrepT, rgHelperRecv, rgHelper, rg0],
          by simp [state, rgReceivedHelper, rgPublished, rgHelper, rg0]⟩
        (by simp [state, rgReceivedHelper, rgPublished, rgHelper, rg0]) (fun x => rfl))
      (cc_adv rfl (advance_ack _ _ _ _ _ _ _ _ _ (fun x => rfl)
        (by intro x; cases x <;> simp [disk0, put, ack]) (by simp [disk0, put, ack])))

/-- Guarded accept of the target by worker `true`, its own certificate puts for
the target interleaved with manifest writes, the record's own acknowledgement,
the writer's certificate quorum writes from its reply log (commit certificate
under fence 0), durable catalogue commit, and the guarded finish whose head change
has `true`'s reply quorum. -/
theorem completed_hr : HR completedS eFull kFull eTP := by
  have h20 : HR (state dlAcceptedTarget rgReceived d12) eP2 kA4 eTP :=
    wstep target_published (accept_joint dlSentTarget dlAcceptedTarget rgReceivedHelper rgReceived d12 true
        delivery_steps.2.2.2.2.2.2.1 group_steps.2.2.2.2.2.2.1
        (by simp [ack]) (by simp [put, ack]) rfl)
      (by regs) rfl
      (ack_same (fun n d _ _ _ => ⟨(), true, rfl, rfl, eP2_cert d⟩)
        (fun n h => absurd rfl h) rfl)
  have c5 : HR (state dlAcceptedTarget rgReceived d12) eC3 kA4 eTP := cstep h20 (.put true false true rfl rfl)
  have h21 := pstep c5 (put_joint dlAcceptedTarget rgReceived d12 false (.manifest true) rfl) rfl rfl rfl
  have c6 : HR (state dlAcceptedTarget rgReceived d13) eFull kA4 eTP := cstep h21 (.put true true true rfl rfl)
  have h22 := pstep c6 (put_joint dlAcceptedTarget rgReceived d13 true (.manifest true) rfl) rfl rfl rfl
  have h23 : HR (state dlAcceptedTarget rgReceived d15) eFull kA5 eTP :=
    pstep h22 (ack_joint dlAcceptedTarget rgReceived d14 (.manifest true)
      (by intro r; cases r <;> simp [disk0, put, ack]) trivial) rfl rfl rfl
      (hadv := advance_ack _ _ _ _ _ _ _ _ _ (fun x => rfl)
        (by intro x; cases x <;> simp [disk0, put, ack]) (by simp [disk0, put, ack]))
  have h24 := pstep h23 (put_joint dlAcceptedTarget rgReceived d15 false (.catalog 1) rfl) rfl rfl rfl
  have h25 := pstep h24 (put_joint dlAcceptedTarget rgReceived d16 true (.catalog 1) rfl) rfl rfl rfl
  have h25a : HR (state dlAcceptedTarget rgReceived d18) eFull kA6 eTP :=
    pstep h25 (ack_joint dlAcceptedTarget rgReceived d17 (.catalog 1)
      (by intro r; cases r <;> simp [disk0, put, ack]) trivial) rfl rfl rfl
      (hadv := advance_ack _ _ _ _ _ _ _ _ _ (fun x => rfl)
        (by intro x; cases x <;> simp [disk0, put, ack]) (by simp [disk0, put, ack]))
  have q1 : HR (state dlAcceptedTarget rgReceived d18) eFull k1 eTP :=
    ccstep h25a (.object () (.payload false) (fun x _ => rfl)
      (reply_quorum _ _ (by intro x; simp)))
  have q2 : HR (state dlAcceptedTarget rgReceived d18) eFull k2 eTP :=
    ccstep q1 (.object () (.payload true) (fun x _ => rfl) (reply_quorum _ _ (by intro x; simp)))
  have q3 : HR (state dlAcceptedTarget rgReceived d18) eFull k3 eTP :=
    ccstep q2 (.object () (.manifest true) (fun x _ => rfl) (reply_quorum _ _ (by intro x; simp)))
  have q4 : HR (state dlAcceptedTarget rgReceived d18) eFull kFull eTP :=
    ccstep q3 (.record () true (fun x _ => rfl)
      (reply_quorum _ _ (by intro x; simp [EN, encode]))
      (by simp [state, rec0, tok, RT, recoveryTheory])
      ⟨(), fun x _ => rfl, fun p hp => by simp [RT, recoveryTheory] at hp⟩)
  have h26 : HR (state dlAcceptedTarget rgReceived d18 recCommitted) eFull kFull eTP :=
    wstep q4 recommit_joint (by regs) rfl
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

/-- A storage step at fence 1 that writes only record `false`'s catalogue object
(and other objects): every new catalogue write passes the fence check. -/
theorem zstep {disk disk' : ParaleanProtocol.Example.Disk} {eC eC' : XC}
    (h : HR (state dlDone rgCommitted disk fRot) eFull eC eT1)
    (hb : ParaleanProtocol.Next TH RT EN (state dlDone rgCommitted disk fRot) (state dlDone rgCommitted disk' fRot))
    (hl : disk.live = disk'.live)
    (hold : ∀ x, disk.stored x (.catalog 1) = true) (hack : disk.acknowledged (.catalog 1) = true)
    (hcc : ParaleanCatalogCertificates.Guard TH RT EN tok (state dlDone rgCommitted disk fRot) eC
      (state dlDone rgCommitted disk' fRot) eC') :
    HR (state dlDone rgCommitted disk' fRot) eFull eC' eT1 := by
  refine hstep h hb (rguard_of (by regs)) (tguard_of (by regs) (by pubs) (by upd)) ?_
    (ack_same (fun n d h1 h2 _ => absurd (h1.symm.trans h2) (by decide)) (fun n h => absurd rfl h) hl)
    hcc
  intro c hn
  cases c
  · exact fenced1 rfl
  · exfalso
    rcases hn with ⟨x, _, h2⟩ | ⟨_, h2⟩
    · have := hold x; simp [state, EN, encode] at h2; rw [this] at h2; cases h2
    · simp [state, EN, encode] at h2; rw [hack] at h2; cases h2

/-- The desktop forgets the catalogue IDs, the controller reassigns name `2` to
worker `true`, and the fence rotates to 1. Under fence 1, record `false` (rank-1
token) is first written to both replicas and acknowledged, then its manifest is
written and acknowledged. No certificate for record `false` exists. -/
theorem zS_hr : HR zS eFull kZ eT1 := by
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
      (by intro x; cases x <;> simp [put, ack]) (by simp [put, ack]) (cc_quiet rfl rfl)
  have z2 : HR (state dlDone rgCommitted dZ2 fRot) eFull kFull eT1 :=
    zstep z1 (ParaleanProtocol.storage_step TH RT EN dlDone rgCommitted fRot dZ1 dZ2 (.Put true (.catalog 0))
        (ParaleanCompletionRecovery.Example.put_step dZ1 true _ rfl) trivial) rfl
      (by intro x; cases x <;> simp [put, ack]) (by simp [put, ack]) (cc_quiet rfl rfl)
  have z3 : HR (state dlDone rgCommitted dZ3 fRot) eFull kZ0 eT1 :=
    zstep z2 (ParaleanProtocol.storage_step TH RT EN dlDone rgCommitted fRot dZ2 dZ3 (.Ack (.catalog 0) ())
        (ParaleanCompletionRecovery.Example.ack_step dZ2 (.catalog 0)
          (by intro r; cases r <;> simp [disk0, put, ack])) trivial) rfl
      (by intro x; cases x <;> simp [put, ack]) (by simp [put, ack])
      (cc_adv rfl (advance_ack _ _ _ _ _ _ _ _ _ (fun x => rfl)
        (by intro x; cases x <;> simp [disk0, put, ack]) (by simp [disk0, put, ack])))
  have m1 : HR (state dlDone rgCommitted dM1 fRot) eFull kZ0 eT1 :=
    zstep z3 (ParaleanProtocol.storage_step TH RT EN dlDone rgCommitted fRot dZ3 dM1 (.Put false (.manifest false))
        (ParaleanCompletionRecovery.Example.put_step dZ3 false _ rfl) trivial) rfl
      (by intro x; cases x <;> simp [put, ack]) (by simp [put, ack]) (cc_quiet rfl rfl)
  have m2 : HR (state dlDone rgCommitted dM2 fRot) eFull kZ0 eT1 :=
    zstep m1 (ParaleanProtocol.storage_step TH RT EN dlDone rgCommitted fRot dM1 dM2 (.Put true (.manifest false))
        (ParaleanCompletionRecovery.Example.put_step dM1 true _ rfl) trivial) rfl
      (by intro x; cases x <;> simp [put, ack]) (by simp [put, ack]) (cc_quiet rfl rfl)
  exact zstep m2 (ParaleanProtocol.storage_step TH RT EN dlDone rgCommitted fRot dM2 dM3 (.Ack (.manifest false) ())
        (ParaleanCompletionRecovery.Example.ack_step dM2 (.manifest false)
          (by intro r; cases r <;> simp [disk0, put, ack])) trivial) rfl
      (by intro x; cases x <;> simp [put, ack]) (by simp [put, ack])
      (cc_adv rfl (advance_ack _ _ _ _ _ _ _ _ _ (fun x => rfl)
        (by intro x; cases x <;> simp [disk0, put, ack]) (by simp [disk0, put, ack])))

/-- Replica `false` is lost with its certificates (the writers' replies remain). -/
theorem lost_hr {eC : XC} (h : HR zS eFull eC eT1) :
    HR lostS eLost (ParaleanCatalogCertificates.advance zS lostS eC) eT1 := by
  refine hstep h (ParaleanProtocol.failure_step TH RT EN (.storage false destroyZ))
    (rguard_of (by regs)) (tguard_of (by regs) (by pubs) (by upd)) ?_ (ack_reg rfl) (cc_adv rfl rfl)
  intro c hn
  exfalso
  rcases hn with ⟨x, h1, h2⟩ | ⟨h1, h2⟩
  · cases x <;> simp [state] at h1 h2
    simp_all
  · simp [state] at h1 h2; simp_all

/-- Both workers crash (worker `true` recovers): every worker index is erased. -/
theorem erased_hr : HR erasedS eLost kLost eT1 := by
  have l1 : HR lostS eLost kLost eT1 := lost_hr zS_hr
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
      (by simp [put, ack]) (by simp [put, ack]) rfl) (by regs) rfl
    (ack_same (fun n d _ _ _ => ⟨(), true, rfl, rfl, eLost_cert d⟩) (fun n h => absurd rfl h) rfl)

/-! ## Recovery by certificate scan

The surviving read quorum `()` is replica `true`. Every scan below is computed by
`ParaleanCatalogCertificates.certScanValue codec` from the bytes and certificates
that replica returns. -/

theorem responded (dl : ParaleanProtocol.Example.Delivery) (rg : Registry)
    (rec : ParaleanProtocol.Example.Recovery) :
    ParaleanCatalogCertificates.Responded TH (state dl rg lostZ rec) () := by
  intro x hx
  cases x
  · simp [TH, theory, storageTheory] at hx
  · rfl

theorem quorum_catalog (dl : ParaleanProtocol.Example.Delivery) (rg : Registry)
    (rec : ParaleanProtocol.Example.Recovery) (c : Bool) :
    ParaleanRecovery.QuorumCatalog (ParaleanRecovery.ofAdmission TH RT EN).base
      (state dl rg lostZ rec).admission.protocol.storage ()
      ((ParaleanRecovery.ofAdmission TH RT EN).recordObject c) :=
  ⟨true, rfl, rfl, by cases c <;> simp [ParaleanRecovery.ofAdmission, EN, encode, state, put, ack]⟩

theorem kLost_rcert (x c : Bool) : kLost.rcert x c = (x && c) := by
  cases x <;> cases c <;> simp [kLost, ParaleanCatalogCertificates.advance,
    ParaleanCatalogCertificates.logReplies, ParaleanCatalogCertificates.clearLost, state,
    TH, theory, storageTheory, put, ack, disk0]

theorem kBLost_rcert (x c : Bool) : kBLost.rcert x c = x := by
  cases x <;> cases c <;> simp [kBLost, ParaleanCatalogCertificates.advance,
    ParaleanCatalogCertificates.logReplies, ParaleanCatalogCertificates.clearLost, state,
    TH, theory, storageTheory, put, ack, disk0]

/-- Record `true`'s certificates are on replica `true` in both traces. -/
theorem ready_true (e : XC) (hr : e.rcert true true = true)
    (ho : ∀ o, o = .manifest true ∨ (∃ d, o = .payload d) → e.ocert true o = true) :
    ParaleanCatalogCertificates.ScanReady TH RT e () true := by
  refine ⟨⟨true, rfl, hr⟩, ⟨true, rfl, ho _ (Or.inl rfl)⟩, fun d _ => ⟨true, rfl, ho _ (Or.inr ⟨d, rfl⟩)⟩⟩

/-- Main trace: the scan decodes both records and marks only record `true` ready.
Record `false` is rejected: its bytes are on the surviving replica, but it has no
commit certificate. -/
theorem scanA_value :
    ParaleanCatalogCertificates.certScanValue codec TH EN receivedS kLost () = ((true, true), (false, true)) := by
  have r1 : ParaleanCatalogCertificates.ScanReady TH RT kLost () true := by
    refine ready_true _ (by simp [kLost_rcert]) ?_
    rintro o (rfl | ⟨d, rfl⟩) <;> (try cases d) <;>
      simp [kLost, ParaleanCatalogCertificates.advance, ParaleanCatalogCertificates.logReplies,
        ParaleanCatalogCertificates.clearLost, state, TH, theory, storageTheory]
  have r0 : ¬ ParaleanCatalogCertificates.ScanReady TH RT kLost () false := by
    rintro ⟨⟨x, hm, hx⟩, _⟩
    cases x
    · simp [TH, theory, storageTheory] at hm
    · simp [kLost_rcert] at hx
  unfold ParaleanCatalogCertificates.certScanValue
  simp only [codec, Prod.mk.injEq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact decide_eq_true (quorum_catalog _ _ _ false)
  · exact decide_eq_true (quorum_catalog _ _ _ true)
  · exact decide_eq_false r0
  · exact decide_eq_true r1

/-- Second trace: with record `false`'s certificates written, the same scan marks
both records ready. -/
theorem scanB_value :
    ParaleanCatalogCertificates.certScanValue codec TH EN lostS kBLost () = ((true, true), (true, true)) := by
  have hr : ∀ c, ParaleanCatalogCertificates.ScanReady TH RT kBLost () c := by
    intro c
    refine ⟨⟨true, rfl, by simp [kBLost_rcert]⟩, ⟨true, rfl, ?_⟩, fun d hd => ⟨true, rfl, ?_⟩⟩
    · cases c <;> simp [kBLost, ParaleanCatalogCertificates.advance, ParaleanCatalogCertificates.logReplies,
        ParaleanCatalogCertificates.clearLost, state, TH, theory, storageTheory, RT, recoveryTheory]
    · cases c
      · simp [TH, theory, groupTheory, RT, recoveryTheory] at hd
      · cases d <;> simp [kBLost, ParaleanCatalogCertificates.advance,
          ParaleanCatalogCertificates.logReplies, ParaleanCatalogCertificates.clearLost, state, TH,
          theory, storageTheory, RT, recoveryTheory]
  unfold ParaleanCatalogCertificates.certScanValue
  simp only [codec, Prod.mk.injEq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact decide_eq_true (quorum_catalog _ _ _ false)
  · exact decide_eq_true (quorum_catalog _ _ _ true)
  · exact decide_eq_true (hr false)
  · exact decide_eq_true (hr true)

/-- Both records decoded, record `true` ready: only record `true` is known. -/
theorem scanA_effect : ParaleanRecovery.scanEffect RT ((true, true), (false, true)) fRot = fScan := by
  simp [ParaleanRecovery.scanEffect, ParaleanRecovery.admissible, ParaleanRecovery.buildable,
    fScan, fRot, recCommitted, rec0, RT, recoveryTheory, groupTheory, readFrom, instIsSubReaderOfRefl,
    funext_iff, Bool.forall_bool]

/-- Record `false` after adoption: both records known and committed. -/
def bScan : ParaleanProtocol.Example.Recovery :=
  { fRot with known := (fun _ => true), committed := (fun _ => true), durableAck := (fun _ => true), scanned := true }
/-- Record `false` is the unique head (its ancestor `true` is not a head). -/
def bRebuilt : ParaleanProtocol.Example.Recovery :=
  { bScan with heads := (fun c => !c), reconstructed := true }
def bAuto : ParaleanProtocol.Example.Recovery := { bRebuilt with selected := true, selectedRecord := false }

theorem scanB_effect : ParaleanRecovery.scanEffect RT ((true, true), (true, true)) fRot = bScan := by
  simp [ParaleanRecovery.scanEffect, ParaleanRecovery.admissible, ParaleanRecovery.buildable,
    bScan, fRot, recCommitted, rec0, RT, recoveryTheory, groupTheory, readFrom, instIsSubReaderOfRefl,
    funext_iff, Bool.forall_bool]

local instance : delta% (ParaleanRecovery.reconstruct._veil_dec_type_0
  (record := Bool) (workspace := Unit) (snapshot := Bool)
  (decl := Bool) (name := Fin 3) (token := Bool) (scan := Scan)
  (χ := ParaleanRecovery.CanonicalRep Bool Unit Bool Bool (Fin 3) Bool Scan)) :=
  fun _ _ _ => Classical.propDecidable _
local instance : delta% (ParaleanRecovery.reconstruct._veil_dec_type_1
  (record := Bool) (workspace := Unit) (snapshot := Bool)
  (decl := Bool) (name := Fin 3) (token := Bool) (scan := Scan)
  (χ := ParaleanRecovery.CanonicalRep Bool Unit Bool Bool (Fin 3) Bool Scan)) :=
  fun _ _ => Classical.propDecidable _
local instance : delta% (ParaleanRecovery.automatic._veil_dec_type_0
  (record := Bool) (workspace := Unit) (snapshot := Bool)
  (decl := Bool) (name := Fin 3) (token := Bool) (scan := Scan)
  (χ := ParaleanRecovery.CanonicalRep Bool Unit Bool Bool (Fin 3) Bool Scan)) :=
  fun _ _ => Classical.propDecidable _

theorem adoption_steps :
    ParaleanRecovery.RecoveryNext RT bScan .reconstruct bRebuilt ∧
    ParaleanRecovery.RecoveryNext RT bRebuilt (.automatic false) bAuto := by
  constructor
  all_goals simp [ParaleanRecovery.RecoveryNext, ParaleanRecovery.Next,
    ParaleanRecovery.NextAct, ParaleanRecovery.reconstruct.ext.derived_eq,
    ParaleanRecovery.automatic.ext.derived_eq, ParaleanRecovery.reconstruct.ext.tr,
    ParaleanRecovery.automatic.ext.tr, bScan, bRebuilt, bAuto, fRot, recCommitted, rec0,
    RT, recoveryTheory, groupTheory, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanRecovery.canonicalFieldRep, Veil.canonicalFieldRepresentation,
    Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
    funext_iff, Bool.forall_bool, Bool.exists_bool]

/-- Main trace: implementation scan (record `false` rejected), reconstruction and
automatic selection of record `true`. -/
theorem scanned_hr : HR scannedS eLost kLost eT1 :=
  sstep received_hr (responded _ _ _) fScan (by rw [scanA_value]; exact scanA_effect)

theorem recovered_hr : HR recoveredS eLost kLost eT1 := by
  have r2 : HR (state dlC2 rgRecv lostZ fRebuilt) eLost kLost eT1 :=
    qstep scanned_hr (ParaleanProtocol.recovery_step TH RT EN _ fScan fRebuilt
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

/-- Second trace: record `false`'s manifest and commit certificates are quorum
writes from the writer's reply log, the commit certificate under fence 1. -/
theorem zB_hr : HR zS eFull kB eT1 := by
  have b1 : HR zS eFull kB1 eT1 :=
    ccstep zS_hr (.object () (.manifest false) (fun x _ => rfl) (reply_quorum _ _ (by intro x; simp)))
  exact ccstep b1 (.record () false (fun x _ => rfl) (reply_quorum _ _ (by intro x; simp [EN, encode]))
    (by simp [state, fRot, recCommitted, rec0, tok, RT, recoveryTheory])
    ⟨(), fun x _ => rfl, fun p hp => by
      cases p
      · simp [RT, recoveryTheory] at hp
      · refine ready_true _ (by simp [TH, theory, storageTheory]) ?_
        rintro o (rfl | ⟨d, rfl⟩) <;> (try cases d) <;> simp [TH, theory, storageTheory]⟩)

theorem lostB_hr : HR lostS eLost kBLost eT1 := lost_hr zB_hr

abbrev bScannedS : CState := state dlDone rgCommitted lostZ bScan
abbrev bRebuiltS : CState := state dlDone rgCommitted lostZ bRebuilt
abbrev bAutoS : CState := state dlDone rgCommitted lostZ bAuto

/-- Second trace: the same implementation scan adopts record `false` (newly
committed by `enumerate`), and automatic recovery selects it as the unique head. -/
theorem adopted_hr : HR bScannedS eLost kBLost eT1 :=
  sstep lostB_hr (responded _ _ _) bScan (by rw [scanB_value]; exact scanB_effect)

theorem adopted_selected_hr : HR bAutoS eLost kBLost eT1 := by
  have r2 : HR bRebuiltS eLost kBLost eT1 :=
    qstep adopted_hr (ParaleanProtocol.recovery_step TH RT EN _ bScan bRebuilt
        (.recovery .reconstruct (by intro c epoch h; cases h) (by intro v h; cases h)
          adoption_steps.1))
      (by regs) rfl
      (ack_same (fun n d h1 h2 _ => absurd (h1.symm.trans h2) (by decide))
        (fun n h => absurd rfl h) rfl)
  exact qstep r2 (ParaleanProtocol.recovery_step TH RT EN _ bRebuilt bAuto
      (.recovery (.automatic false) (by intro c epoch h; cases h) (by intro v h; cases h)
        adoption_steps.2))
    (by regs) rfl
    (ack_same (fun n d h1 h2 _ => absurd (h1.symm.trans h2) (by decide))
      (fun n h => absurd rfl h) rfl)

/-! ## Epoch fence -/

/-- After the controller reassigns name `2` to worker `true`, the former owner
`false` still holds its pending target. Publishing it is a base protocol step, but
not a hardened step: it was prepared under epoch `0` and the name is at epoch `1`. -/
theorem stale_owner_publish_blocked :
    HR preparedS eC2 kA3 (ParaleanTargetNames.reassign eT0 2 true) ∧
    preparedS.admission.protocol.registry.pending false true = true ∧
    (ParaleanTargetNames.reassign eT0 2 true).owner 2 = true ∧
    (ParaleanTargetNames.reassign eT0 2 true).preparedEpoch false true 2 = 0 ∧
    (ParaleanTargetNames.reassign eT0 2 true).epoch 2 = 1 ∧
    ParaleanProtocol.Next TH RT EN preparedS (state dlSentTarget rgReceivedHelper d12) ∧
    (state dlSentTarget rgReceivedHelper d12).admission.protocol.registry.published true = true ∧
    ∀ eF e', ¬ ParaleanHardened.Next TH RT EN cfg
      (preparedS, (eF, eC2, kA3, ParaleanTargetNames.reassign eT0 2 true))
      (state dlSentTarget rgReceivedHelper d12, e') := by
  have hb : ParaleanProtocol.Next TH RT EN preparedS (state dlSentTarget rgReceivedHelper d12) :=
    publish_joint dlSentTarget rgPrepT rgReceivedHelper d11 true
      new_group_steps.2.2.1 (by simp [ack, put]) (by intro r; cases r <;> simp [disk0, put, ack])
  refine ⟨rstep target_prepared 2 true, rfl, by simp [ParaleanTargetNames.reassign],
    by simp [ParaleanTargetNames.reassign, ParaleanTargetNames.initExtra],
    by simp [ParaleanTargetNames.reassign, ParaleanTargetNames.initExtra], hb,
    by simp [state, rgReceivedHelper, rgPublished], ?_⟩
  rintro eF e' ⟨_, _, hT, _⟩
  exact ParaleanTargetNames.stale_publication_blocked TH targets RT EN _ _ _ _ false true 2
    (by simp [TH, theory, groupTheory]) ⟨true, rfl, rfl⟩
    (by simp [ParaleanTargetNames.reassign, ParaleanTargetNames.initExtra])
    (by simp [state, rgPrepT, rgHelperRecv, rgHelper, rg0])
    (by simp [state, rgReceivedHelper, rgPublished, rg0]) (by simp [state, rgPrepT])
    (by simp [state, rgReceivedHelper, rgPublished, rgPrepT, rgHelperRecv, rgHelper, rg0]) hT

/-! ## Non-vacuity statements -/

/-- Joint non-vacuity of the hardened protocol. On one trace, every step of which
satisfies all five guards: the current owner of the target name (worker `false`,
epoch 0) prepares the required target holding a verified receipt, and publishes
it, which records it as the name's head and writes the publisher's certificate
quorum in the same step; the committer (worker `true`) holds no quorum for it
before its own puts; the committer
collects replies for both groups from both replicas; the catalogue writer's reply
log holds a write quorum of replies for the record, its manifest and payloads; from
it the certificates and the commit certificate (fence 0) are written as quorum
writes; the catalogue is committed (adoption needs those certificates) and the
guarded finish commits a checkpoint containing the target; the desktop is lost; the
controller reassigns the name to worker `true` (epoch 1), keeping the recorded head;
the fence rotates to 1; record `false` is first written and acknowledged under
fence 1 but gets no commit certificate; a replica is lost; every worker index is
erased; a physical certificate scan finds exactly the published groups; the new
owner receives the recorded head through a certificate read; recovery enumerates
by an implementation scan whose readiness is computed from the surviving replica's
certificates: it decodes both records and rejects record `false`; and recovery
automatically selects the record whose commit certificate passed the fence check. -/
theorem hardened_nonvacuous :
    -- prepare: current owner, receipt, realized required target
    (∃ eF, ParaleanHardened.Reachable TH RT EN cfg (preparedS, (eF, eC2, kA3, eT0))) ∧
    preparedS.admission.protocol.registry.pending false true = true ∧
    ParaleanPublicationReceipts.HeldReceipt TH preparedS.admission.delivery true ∧
    deliveryTheory.required true = true ∧ deliveryTheory.realizes true true = true ∧
    groupTheory.member true (targets.targetName true) = true ∧
    eT0.owner (targets.targetName true) = false ∧
    -- publish, certificates, commit, finish
    CertQuorumBy TH eP2 false true ∧ ¬CertQuorumBy TH eP2 true true ∧
    (∃ eF, ParaleanHardened.Reachable TH RT EN cfg (completedS, (eF, eFull, kFull, eTP)) ∧
      eF true = some 0) ∧
    eTP.head (targets.targetName true) = some true ∧
    completedS.admission.protocol.registry.published true = true ∧
    (∀ d x, eFull.certReply true d x = true) ∧ (∀ d, CertQuorumBy TH eFull true d) ∧
    completedS.admission.delivery.done true = true ∧
    completedS.admission.protocol.registry.head true = true ∧
    groupTheory.contents (completedS.admission.protocol.registry.head true) true = true ∧
    ParaleanCatalogCertificates.ReplyQuorum TH kA6 (.catalog 1) ∧
    completedS.recovery.committed true = true ∧
    CatReady TH RT completedS kFull true ∧ kFull.certFence true = some 0 ∧
    RT.tokenRank (cfg.recordToken true) = completedS.recovery.fence ∧
    -- reassignment, rotation, a fenced first write of an uncertified record at fence 1
    eT1.owner (targets.targetName true) = true ∧ eT1.epoch (targets.targetName true) = 1 ∧
    eT1.head (targets.targetName true) = some true ∧
    (∃ eF, ParaleanHardened.Reachable TH RT EN cfg (zS, (eF, eFull, kZ, eT1)) ∧
      eF false = some 1) ∧
    zS.recovery.fence = 1 ∧ RT.tokenRank (cfg.recordToken false) = 1 ∧
    zS.admission.protocol.storage.acknowledged (.catalog 0) = true ∧ kZ.certFence false = none ∧
    -- failures, index erasure, physical scan
    (∃ eF, ParaleanHardened.Reachable TH RT EN cfg (erasedS, (eF, eLost, kLost, eT1))) ∧
    erasedS.admission.protocol.storage.live false = false ∧
    erasedS.recovery.fence = 1 ∧ (∀ c, erasedS.recovery.known c = false) ∧
    (∀ n d, erasedS.admission.protocol.registry.known n d = false) ∧
    (∀ d, certScan TH erasedS eLost () d) ∧
    (∀ d, certScan TH erasedS eLost () d → erasedS.admission.protocol.registry.published d = true) ∧
    -- the new owner receives the recorded head
    (∃ eF, ParaleanHardened.Reachable TH RT EN cfg (receivedS, (eF, eLost, kLost, eT1))) ∧
    receivedS.admission.protocol.registry.known true true = true ∧
    -- implementation scan: both records decoded, record `false` rejected by certificates
    ParaleanCatalogCertificates.Responded TH receivedS () ∧
    RT.decoded (ParaleanCatalogCertificates.certScanValue codec TH EN receivedS kLost ()) false = true ∧
    RT.ready (ParaleanCatalogCertificates.certScanValue codec TH EN receivedS kLost ()) false = false ∧
    RT.decoded (ParaleanCatalogCertificates.certScanValue codec TH EN receivedS kLost ()) true = true ∧
    RT.ready (ParaleanCatalogCertificates.certScanValue codec TH EN receivedS kLost ()) true = true ∧
    ParaleanCatalogCertificates.ScanEnumerate TH RT EN codec (receivedS, kLost) (scannedS, kLost) ∧
    (∃ eF, ParaleanHardened.Reachable TH RT EN cfg (scannedS, (eF, eLost, kLost, eT1))) ∧
    scannedS.recovery.known true = true ∧ scannedS.recovery.known false = false ∧
    -- fenced recovery
    (∃ eF, ParaleanHardened.Reachable TH RT EN cfg (recoveredS, (eF, eLost, kLost, eT1)) ∧
      eF true = some 0) ∧
    recoveredS.recovery.selected = true ∧ recoveredS.recovery.selectedRecord = true ∧
    kLost.certFence recoveredS.recovery.selectedRecord =
      some (RT.tokenRank (cfg.recordToken recoveredS.recovery.selectedRecord)) ∧
    recoveredS.recovery.fence = 1 := by
  obtain ⟨eC, hC⟩ := completed_hr
  obtain ⟨eE, hE⟩ := erased_hr
  obtain ⟨eR, hR⟩ := recovered_hr
  obtain ⟨eZ, hZ⟩ := zS_hr
  have fC := (ParaleanCatalogFencing.catalog_objects_fenced TH RT EN tok assumptions
    recovery_assumptions (ParaleanHardened.reachable_fencing TH RT EN cfg hC)).2 true rfl
  have fZ := (ParaleanCatalogFencing.present_fenced TH RT EN tok
    (ParaleanHardened.reachable_fencing TH RT EN cfg hZ)) false
    (Or.inl ⟨true, by simp [zS, state, put, ack, EN, encode]⟩)
  have sR := (ParaleanHardened.hardened_safe TH RT EN cfg assumptions recovery_assumptions hR).2.2.2.1 rfl
  have hb := ParaleanAckCertificates.scan_between TH RT EN assumptions
    (ParaleanHardened.reachable_certificates TH RT EN cfg hE) () (fun x hx => hx)
  have hv := scanA_value
  refine ⟨target_prepared, rfl, held_target, rfl, rfl, rfl, rfl, eP2_publisher_quorum, eP2_committer_none,
    ⟨eC, hC, ?_⟩, by simp [targets], rfl, eFull_reply, eFull_quorum, rfl, rfl,
    rfl, reply_quorum _ _ (by intro x; simp), rfl, kFull_ready _, by simp, rfl, ?_, ?_, ?_,
    ⟨eZ, hZ, ?_⟩, rfl, by simp [cfg, tok, RT, recoveryTheory], by simp [zS, state, put, ack],
    by simp, ⟨eE, hE⟩, rfl, rfl, fun _ => rfl, fun _ _ => rfl,
    fun d => (hb d).1 ⟨true, eLost_quorum d⟩, fun d => (hb d).2.1, received_hr, rfl,
    responded _ _ _, by rw [hv]; rfl, by rw [hv]; rfl, by rw [hv]; rfl, by rw [hv]; rfl,
    scanEnum_of (responded _ _ _) fScan (by rw [hv]; exact scanA_effect), scanned_hr, rfl, rfl,
    ⟨eR, hR, ?_⟩, rfl, rfl, ?_, rfl⟩
  · simpa [tok, RT, recoveryTheory] using fC.1
  · simp [ParaleanTargetNames.reassign, targets]
  · simp [ParaleanTargetNames.reassign, ParaleanTargetNames.initExtra, targets]
  · simp [ParaleanTargetNames.reassign, targets]
  · simpa [cfg, tok, RT, recoveryTheory] using fZ.1
  · simpa [tok, RT, recoveryTheory, cfg, fAuto, fRebuilt, fScan, fRot, state] using sR.1
  · simpa [tok, RT, recoveryTheory, cfg, fAuto, fRebuilt, fScan, fRot, state] using sR.2

/-- Adoption through `enumerate`, on a trace sharing the main trace's prefix up to
record `false`'s acknowledgement. The writer writes record `false`'s manifest and
commit certificates (fence 1) as quorum writes from its reply log; a replica is
lost; recovery's implementation scan over the surviving replica marks both
records ready and adopts record `false`, which was not committed: the adoption
guard (`CatReady`) holds by the surviving certificates. Record `false` is then the
unique head and is selected automatically. The catalogue bytes are those of the
main trace, where the same scan rejects record `false`. -/
theorem hardened_scan_adoption :
    (∃ eF, ParaleanHardened.Reachable TH RT EN cfg (zS, (eF, eFull, kB, eT1))) ∧
    kB.certFence false = some 1 ∧ kB.rcert true false = true ∧ kB.rcert false false = true ∧
    (∃ eF, ParaleanHardened.Reachable TH RT EN cfg (lostS, (eF, eLost, kBLost, eT1))) ∧
    lostS.recovery.committed false = false ∧ lostS.admission.protocol.storage.live false = false ∧
    lostS.admission.protocol.storage = receivedS.admission.protocol.storage ∧
    RT.ready (ParaleanCatalogCertificates.certScanValue codec TH EN lostS kBLost ()) false = true ∧
    RT.ready (ParaleanCatalogCertificates.certScanValue codec TH EN receivedS kLost ()) false = false ∧
    ParaleanCatalogCertificates.ScanEnumerate TH RT EN codec (lostS, kBLost) (bScannedS, kBLost) ∧
    (∃ eF, ParaleanHardened.Reachable TH RT EN cfg (bScannedS, (eF, eLost, kBLost, eT1))) ∧
    bScannedS.recovery.committed false = true ∧
    CatReady TH RT lostS kBLost false ∧
    (∃ eF, ParaleanHardened.Reachable TH RT EN cfg (bAutoS, (eF, eLost, kBLost, eT1))) ∧
    bAutoS.recovery.selected = true ∧ bAutoS.recovery.selectedRecord = false ∧
    kBLost.certFence bAutoS.recovery.selectedRecord =
      some (RT.tokenRank (cfg.recordToken bAutoS.recovery.selectedRecord)) ∧
    bAutoS.recovery.fence = 1 := by
  obtain ⟨eB, hB⟩ := lostB_hr
  obtain ⟨eA, hA⟩ := adopted_selected_hr
  have hL := ParaleanHardened.reachable_catalog TH RT EN cfg hB
  have hv := scanB_value
  have hready : ParaleanCatalogCertificates.ScanReady TH RT kBLost () false := by
    have h := congrArg (fun v : Scan => scanBit v.2 false) hv
    simp only [ParaleanCatalogCertificates.certScanValue, codec, scanBit] at h
    simpa using h
  have sA := (ParaleanHardened.hardened_safe TH RT EN cfg assumptions recovery_assumptions hA).2.2.2.1 rfl
  refine ⟨zB_hr, by simp, by simp [TH, theory, storageTheory], by simp [TH, theory, storageTheory], ⟨eB, hB⟩, rfl, rfl, rfl, by rw [hv]; rfl,
    by rw [scanA_value]; rfl, scanEnum_of (responded _ _ _) bScan (by rw [hv]; exact scanB_effect),
    adopted_hr, rfl, ParaleanCatalogCertificates.scanReady_catReady TH RT EN tok assumptions hL hready,
    ⟨eA, hA⟩, rfl, rfl, ?_, rfl⟩
  simpa [tok, RT, recoveryTheory, cfg, bAuto, bRebuilt, bScan, fRot, state] using sA.2

/-! ## Receipt verification

The instance above signs every receipt. In this variant the validator signs only
receipt `true`, so the helper's receipt (`false`) fails verification. The helper
receipt is in flight in a reachable hardened state; staging the helper is a base
protocol step there, but no hardened step stages it. -/

def deliveryV : ParaleanDelivery.Theory Bool Bool Bool Bool Bool (Fin 3) :=
  { deliveryTheory with verified := fun m => m }

def THv : Theory Bool Bool (Fin 3) Bool Bool Bool Bool Unit Unit :=
  ⟨deliveryV, groupTheory, storageTheory⟩

def targetsV : ParaleanTargetNames.TargetAssumptions THv where
  targetName := fun _ => 2
  pinned := by
    intro o q h1 h2
    cases o <;> cases q <;> simp_all [THv, deliveryV, deliveryTheory, groupTheory]

def cfgV : ParaleanHardened.Config THv Bool Bool := ⟨targetsV, tok⟩

theorem v_delivery_steps :
    ParaleanDelivery.Initial deliveryV dl0 ∧
    ParaleanDelivery.Step deliveryV dl0 (.start true false) dlStartedHelper ∧
    ParaleanDelivery.Step deliveryV dlStartedHelper (.send false) dlSentHelper := by
  repeat' apply And.intro
  all_goals simp [ParaleanDelivery.Initial, ParaleanDelivery.Init, ParaleanDelivery.initializer.ext.tr,
    ParaleanDelivery.Step, ParaleanDelivery.Next, ParaleanDelivery.NextAct,
    ParaleanDelivery.start.ext.derived_eq, ParaleanDelivery.send.ext.derived_eq,
    ParaleanDelivery.start.ext.tr, ParaleanDelivery.send.ext.tr, ParaleanDelivery.ready,
    deliveryV, deliveryTheory, groupTheory, dl0, dlStartedHelper, dlSentHelper,
    getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanDelivery.canonicalFieldRep, Veil.canonicalFieldRepresentation,
    Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]

abbrev HXv := ParaleanHardened.Extra Bool Bool Bool Bool (Fin 3) Bool
abbrev eV0 : HXv := (fun _ => none, initExtra, k0, eT0)

/-- A delivery control step (no registry or storage change) is a hardened step of
the variant. -/
theorem v_control {dl dl' : ParaleanProtocol.Example.Delivery}
    (label : ParaleanDelivery.Label Bool Bool Bool Bool Bool (Fin 3))
    (control : ParaleanAdmission.Control label)
    (step : ParaleanDelivery.Step deliveryV dl label dl') :
    ParaleanHardened.Next THv RT EN cfgV (state dl rg0 d0, eV0) (state dl' rg0 d0, eV0) := by
  have hb : ParaleanProtocol.Next THv RT EN (state dl rg0 d0) (state dl' rg0 d0) :=
    .paired (.admission (.control label control step) rfl) .stutter
  refine ⟨hb, fun n d h1 h2 => absurd h1 h2, ?_, ?_, ?_, ?_⟩
  · exact ParaleanTargetNames.guard_of_quiet THv targetsV RT EN _ _ eT0
      (fun n d h => h) (fun d h => h)
  · exact ⟨fun c hn => absurd hn (ParaleanCatalogFencing.same_storage_no_write EN rfl c),
      (ParaleanCatalogFencing.update_quiet EN _ (ParaleanCatalogFencing.same_storage_no_write EN rfl)).symm⟩
  · refine Or.inl ⟨?_, ?_, ?_⟩
    · intro n d h1 h2 _; exact absurd (h1.symm.trans h2) (by decide)
    · intro n h; exact absurd rfl h
    · dsimp only
      rw [ParaleanAckCertificates.clearLost_same _ _ _ (by rfl)]
      exact ParaleanAckCertificates.publishWrite_quiet _ _ _ _
        (ParaleanAckCertificates.no_new_pub_of_same _ _ rfl)
  · refine Or.inl ⟨?_, (ParaleanCatalogCertificates.advance_same _ _ _ rfl rfl).symm⟩
    intro c h1 h2; exact absurd (h1.symm.trans h2) (by decide)

/-- The variant validator rejects the helper's receipt: it is in flight in a
reachable hardened state, the base protocol stages the helper there, and no
hardened step stages it. -/
theorem hardened_receipt_rejected :
    ParaleanHardened.Reachable THv RT EN cfgV (state dlSentHelper rg0 d0, eV0) ∧
    dlSentHelper.flight false = true ∧ deliveryV.verified false = false ∧
    ParaleanProtocol.Next THv RT EN (state dlSentHelper rg0 d0) (state dlSentHelper rgPreparedHelper d0) ∧
    (state dlSentHelper rgPreparedHelper d0).admission.protocol.registry.pending false false = true ∧
    ∀ t e', t.admission.protocol.registry.pending false false = true →
      ¬ ParaleanHardened.Next THv RT EN cfgV (state dlSentHelper rg0 d0, eV0) (t, e') := by
  have h0 : ParaleanHardened.Reachable THv RT EN cfgV (state dl0 rg0 d0, eV0) :=
    .initial ⟨⟨⟨v_delivery_steps.1, group_steps.1, ParaleanCompletionRecovery.Example.initial_valid.2.2⟩,
      ParaleanCompletionRecovery.Example.recovery_initial⟩, rfl, rfl, rfl, rfl⟩
  have h1 := ParaleanHardened.Reachable.step h0 (v_control (.start true false) trivial v_delivery_steps.2.1)
  have h2 := ParaleanHardened.Reachable.step h1 (v_control (.send false) trivial v_delivery_steps.2.2)
  refine ⟨h2, rfl, rfl, ?_, by simp [state, rgPreparedHelper, rg0], ?_⟩
  · exact .paired (.admission (.registry (.prepare false false) trivial group_steps.2.1 trivial) rfl)
      (.registry (.prepare false false) (by intros; simp) group_steps.2.1 trivial (by intros; contradiction))
  · rintro t e' hp ⟨_, hrc, _⟩
    obtain ⟨m, hf, hv, _, ho⟩ := hrc false false hp (by simp [state, rg0])
    cases m
    · simp [THv, deliveryV] at hv
    · simp [THv, deliveryV, deliveryTheory] at ho

end
end ParaleanHardened.Example

#print axioms ParaleanHardened.Example.instance_assumptions
#print axioms ParaleanHardened.Example.hardened_nonvacuous
#print axioms ParaleanHardened.Example.hardened_scan_adoption
#print axioms ParaleanHardened.Example.stale_owner_publish_blocked
#print axioms ParaleanHardened.Example.hardened_receipt_rejected
