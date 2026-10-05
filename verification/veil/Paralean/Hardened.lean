import Paralean.PublicationReceipts
import Paralean.TargetNames
import Paralean.CatalogFencing
import Paralean.AckCertificates
import Paralean.CatalogCertificates

/-! Hardened joint protocol. Every visible step is a `ParaleanProtocol.Next` step that
also satisfies all five strengthenings: receipt-gated publication, target-name
ownership with a recorded head, fenced first catalogue writes, physical
publication certificates, and physical catalogue certificates with fenced commit
records. Fencing history, certificates with their writers' replies, and target
ownership records are the only additional state. Extra-only steps (a certificate
write, a target reassignment) stutter the protocol state and every other guard. Each component
projection is an actual component `Reachable` state, so every component theorem
holds simultaneously. Lean naming (`ParaleanLeanNames`) refines `member` below
this layer and needs no transition guard. -/
set_option linter.unusedSectionVars false
namespace ParaleanHardened
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

abbrev Extra (node record replica group name snapshot : Type) :=
  ParaleanCatalogFencing.Extra record × ParaleanAckCertificates.Extra node replica group ×
    ParaleanCatalogCertificates.Extra replica record (ParaleanAdmission.StoredObject group snapshot) ×
    ParaleanTargetNames.Extra node group name

local notation "XState" => Extra node record replica group name snapshot

/-- Static hardening inputs: the target contracts and the token embedded in each record.
Target ownership is state (`ParaleanTargetNames.Extra`), not configuration. -/
structure Config (a : ATheory) (token record : Type) where
  targets : ParaleanTargetNames.TargetAssumptions a
  recordToken : record → token

def Guard (a : ATheory) (r : RTheory) (encode : record → Nat) (cfg : Config a token record)
    (s : ModelState) (e : XState) (t : ModelState) (e' : XState) : Prop :=
  ParaleanPublicationReceipts.Guard a r encode s () t () ∧
  ParaleanTargetNames.Guard a cfg.targets r encode s e.2.2.2 t e'.2.2.2 ∧
  ParaleanCatalogFencing.Guard a r encode cfg.recordToken s e.1 t e'.1 ∧
  ParaleanAckCertificates.Guard a r encode s e.2.1 t e'.2.1 ∧
  ParaleanCatalogCertificates.Guard a r encode cfg.recordToken s e.2.2.1 t e'.2.2.1

def Next (a : ATheory) (r : RTheory) (encode : record → Nat) (cfg : Config a token record)
    (p q : ModelState × XState) : Prop :=
  ParaleanProtocol.Next a r encode p.1 q.1 ∧ Guard a r encode cfg p.1 p.2 q.1 q.2

/-- Initial ownership is arbitrary and no target head is recorded, as in
`ParaleanTargetNames.Initial`. -/
def Initial (a : ATheory) (r : RTheory) (p : ModelState × XState) : Prop :=
  ParaleanCompletionRecovery.Initial a r p.1 ∧ p.2.1 = (fun _ => none) ∧
    p.2.2.1 = ParaleanAckCertificates.initExtra ∧
    p.2.2.2.1 = ParaleanCatalogCertificates.initExtra ∧ p.2.2.2.2.head = (fun _ => none)

inductive Reachable (a : ATheory) (r : RTheory) (encode : record → Nat) (cfg : Config a token record) :
    ModelState × XState → Prop where
  | initial {p} : Initial a r p → Reachable a r encode cfg p
  | step {p q} : Reachable a r encode cfg p → Next a r encode cfg p q → Reachable a r encode cfg q

theorem reachable_receipts (a : ATheory) (r : RTheory) (encode : record → Nat) (cfg : Config a token record)
    {p} (h : Reachable a r encode cfg p) :
    ParaleanPublicationReceipts.Reachable a r encode (p.1, ()) := by
  induction h with
  | initial hi => exact .initial hi.1
  | step _ ht ih => exact .step ih ⟨ht.1, ht.2.1⟩

theorem reachable_targets (a : ATheory) (r : RTheory) (encode : record → Nat) (cfg : Config a token record)
    {p} (h : Reachable a r encode cfg p) :
    ParaleanTargetNames.Reachable a cfg.targets r encode (p.1, p.2.2.2.2) := by
  induction h with
  | initial hi => exact .initial ⟨hi.1, hi.2.2.2.2⟩
  | step _ ht ih => exact .step ih ⟨ht.1, ht.2.2.1⟩

theorem reachable_fencing (a : ATheory) (r : RTheory) (encode : record → Nat) (cfg : Config a token record)
    {p} (h : Reachable a r encode cfg p) :
    ParaleanCatalogFencing.Reachable a r encode cfg.recordToken (p.1, p.2.1) := by
  induction h with
  | initial hi => exact .initial ⟨hi.1, hi.2.1⟩
  | step _ ht ih => exact .step ih ⟨ht.1, ht.2.2.2.1⟩

theorem reachable_certificates (a : ATheory) (r : RTheory) (encode : record → Nat) (cfg : Config a token record)
    {p} (h : Reachable a r encode cfg p) :
    ParaleanAckCertificates.Reachable a r encode (p.1, p.2.2.1) := by
  induction h with
  | initial hi => exact .initial ⟨hi.1, hi.2.2.1⟩
  | step _ ht ih => exact .step ih ⟨ht.1, ht.2.2.2.2.1⟩

theorem reachable_catalog (a : ATheory) (r : RTheory) (encode : record → Nat) (cfg : Config a token record)
    {p} (h : Reachable a r encode cfg p) :
    ParaleanCatalogCertificates.Reachable a r encode cfg.recordToken (p.1, p.2.2.2.1) := by
  induction h with
  | initial hi => exact .initial ⟨hi.1, hi.2.2.2.1⟩
  | step _ ht ih => exact .step ih ⟨ht.1, ht.2.2.2.2.2⟩

theorem reachable_protocol (a : ATheory) (r : RTheory) (encode : record → Nat) (cfg : Config a token record)
    {p} (h : Reachable a r encode cfg p) : ParaleanProtocol.Reachable a r encode p.1 :=
  ParaleanPublicationReceipts.reachable_protocol a r encode (reachable_receipts a r encode cfg h)

/-- All hardened guarantees hold together in every reachable hardened state. -/
theorem hardened_safe (a : ATheory) (r : RTheory) (encode : record → Nat) (cfg : Config a token record)
    (ha : ParaleanAdmission.Assumptions a)
    (hra : ParaleanRecovery.CoupledAssumptions (ParaleanRecovery.ofAdmission a r encode))
    {p} (h : Reachable a r encode cfg p) :
    -- the original joint invariants
    (ParaleanCompletionRecovery.Safe a r encode p.1 ∧
      ParaleanPublicationDiscovery.Safe (ParaleanAdmission.protocolTheory a) p.1.admission.protocol) ∧
    -- fix 1: publication needs a verified validator receipt
    (∀ d, p.1.admission.protocol.registry.published d = true →
      ParaleanPublicationReceipts.Receipted a d) ∧
    -- fix 2: no target collision at any node, across arbitrary ownership handovers
    (∀ x, ParaleanTargetNames.IsTarget a cfg.targets x → ∀ n,
      ¬∃ g h, g ≠ h ∧ ParaleanGroups.isHead n g x a.registry p.1.admission.protocol.registry ∧
        ParaleanGroups.isHead n h x a.registry p.1.admission.protocol.registry) ∧
    -- fix 3: the selected catalogue record was first written under the then-current
    -- fence, and its commit certificate was written while its token was the fence
    (p.1.recovery.selected = true →
      p.2.1 p.1.recovery.selectedRecord =
        some (r.tokenRank (cfg.recordToken p.1.recovery.selectedRecord)) ∧
      p.2.2.2.1.certFence p.1.recovery.selectedRecord =
        some (r.tokenRank (cfg.recordToken p.1.recovery.selectedRecord))) ∧
    -- fix 4: certificates are sound; every checkpoint group has the committer's own
    -- reply quorum and is found by a scan of any fully live recovery quorum
    (∀ x d, p.2.2.1.cert x d = true → p.1.admission.protocol.registry.published d = true) ∧
    (∀ n d, a.registry.contents (p.1.admission.protocol.registry.head n) d = true →
      ParaleanAckCertificates.CertQuorumBy a p.2.2.1 n d ∧
      ∀ q, (∀ x, a.storage.memberR x q = true → p.1.admission.protocol.storage.live x = true) →
        ParaleanAckCertificates.certScan a p.1 p.2.2.1 q d) ∧
    -- catalogue certificates: every committed record is physically certified
    (∀ c, p.1.recovery.committed c = true →
      ParaleanCatalogCertificates.CatReady a r p.1 p.2.2.2.1 c) := by
  obtain ⟨s, e⟩ := p
  have h4 := reachable_certificates a r encode cfg h
  have h5 := reachable_catalog a r encode cfg h
  refine ⟨ParaleanProtocol.reachable_safe a r encode ha hra (reachable_protocol a r encode cfg h),
    fun d hd => (ParaleanPublicationReceipts.published_receipted a r encode
      (reachable_receipts a r encode cfg h)).1 d hd,
    fun x hx n => ParaleanTargetNames.no_target_collision a cfg.targets r encode ha
      (reachable_targets a r encode cfg h) n x hx,
    fun hsel => ⟨(ParaleanCatalogFencing.selected_not_stale a r encode cfg.recordToken ha hra
      (reachable_fencing a r encode cfg h) hsel).1,
      (ParaleanCatalogCertificates.selected_fenced a r encode cfg.recordToken ha hra h5 hsel).1⟩,
    fun x d hc => (ParaleanAckCertificates.cert_sound a r encode ha h4 x d hc).1,
    fun n d hc => ParaleanAckCertificates.checkpoint_contents_discoverable a r encode ha h4 n d hc,
    fun c hc => ParaleanCatalogCertificates.committed_catReady a r encode cfg.recordToken ha h5 c hc⟩

/-! ## Cross-guard results -/

/-- A step that changes only the recovery component (no registry or storage change)
satisfies the receipt, target, first-write and publication-certificate guards. -/
theorem lift_recovery_only (a : ATheory) (r : RTheory) (encode : record → Nat)
    (cfg : Config a token record) {s t : ModelState} {e : XState}
    {eC' : ParaleanCatalogCertificates.Extra replica record (ParaleanAdmission.StoredObject group snapshot)}
    (hadm : t.admission = s.admission) (hb : ParaleanProtocol.Next a r encode s t)
    (hc : ParaleanCatalogCertificates.Guard a r encode cfg.recordToken s e.2.2.1 t eC') :
    Next a r encode cfg (s, e) (t, (e.1, e.2.1, eC', e.2.2.2)) := by
  have hst : t.admission.protocol.storage = s.admission.protocol.storage := by rw [hadm]
  have hreg : t.admission.protocol.registry = s.admission.protocol.registry := by rw [hadm]
  refine ⟨hb, ?_, ?_, ?_, ?_, hc⟩
  · intro n d h1 h2; rw [hreg] at h1; simp_all
  · exact ParaleanTargetNames.guard_of_quiet a cfg.targets r encode s t e.2.2.2
      (fun n d h' => by rw [hreg] at h'; exact h') (fun d h' => by rw [hreg] at h'; exact h')
  · refine ⟨fun c hf => absurd hf.1 (ParaleanCatalogFencing.same_storage_no_write encode hst c), ?_⟩
    exact (ParaleanCatalogFencing.update_quiet encode e.1
      (ParaleanCatalogFencing.same_storage_no_write encode hst)).symm
  · refine Or.inl ⟨?_, ?_, ?_⟩
    · intro n d h1 h2 _; rw [hreg, h1] at h2; cases h2
    · intro n h; rw [hreg] at h; exact absurd rfl h
    · exact (ParaleanAckCertificates.clearLost_same s t e.2.1 (by rw [hst])).symm

/-- Recovery selection from certificates and the fence, in the joint model. From
any reachable hardened state and any fully live read quorum, recovery reads the
store into the concrete certificate scan and selects any committed record in
three hardened steps (all five guards hold). The selected record's commit
certificate was written while its token was the fence. No scan value or
acknowledgement oracle is assumed. -/
theorem hardened_certified_recovery (a : ATheory) (r : RTheory) (encode : record → Nat)
    (cfg : Config a token record) (ha : ParaleanAdmission.Assumptions a)
    (hra : ParaleanRecovery.CoupledAssumptions (ParaleanRecovery.ofAdmission a r encode))
    (codec : ParaleanCatalogCertificates.ScanCodec r) {s : ModelState} {e : XState}
    (hr : Reachable a r encode cfg (s, e))
    (q : readQuorum) (hq : ∀ x, a.storage.memberR x q = true → s.admission.protocol.storage.live x = true)
    (c : record) (hc : s.recovery.committed c = true) :
    ∃ s₁ s₂ s₃ : ModelState,
      Next a r encode cfg (s, e) (s₁, e) ∧ Next a r encode cfg (s₁, e) (s₂, e) ∧
      Next a r encode cfg (s₂, e) (s₃, e) ∧
      ParaleanRecovery.RecoveryNext r s.recovery
        (.enumerate (ParaleanCatalogCertificates.certScanValue codec a encode s e.2.2.1 q)) s₁.recovery ∧
      s₃.recovery.selected = true ∧ s₃.recovery.selectedRecord = c ∧
      e.2.2.1.certFence c = some (r.tokenRank (cfg.recordToken c)) ∧
      r.tokenRank (cfg.recordToken c) ≤ s.recovery.fence ∧
      s₃.admission = s.admission := by
  have h5 := reachable_catalog a r encode cfg hr
  obtain ⟨s₁, s₂, s₃, ⟨hb₁, hg₁⟩, ⟨hb₂, hg₂⟩, ⟨hb₃, hg₃⟩, label₁, _, selected, exact, _, _, a₁, a₂, a₃⟩ :=
    ParaleanCatalogCertificates.certified_recovery a r encode cfg.recordToken ha hra codec h5 q hq c hc
  have fenced := ParaleanCatalogCertificates.committed_fenced a r encode cfg.recordToken ha h5 c hc
  have l₁ := lift_recovery_only a r encode cfg (e := e) a₁ hb₁ hg₁
  have l₂ := lift_recovery_only a r encode cfg (e := e) (a₂.trans a₁.symm) hb₂ hg₂
  have l₃ := lift_recovery_only a r encode cfg (e := e) (a₃.trans a₂.symm) hb₃ hg₃
  exact ⟨s₁, s₂, s₃, l₁, l₂, l₃, label₁, selected, exact, fenced.1, fenced.2, a₃⟩

theorem receive_registry_effect (th : ParaleanGroups.Theory node group name snapshot)
    (s s' : ParaleanGroups.CanonicalState node group name snapshot) (n : node) (d : group)
    (h : ParaleanGroups.ReceiveStep th s s' n d) :
    s'.pending = s.pending ∧ s'.published = s.published ∧ s'.head = s.head := by
  simp only [ParaleanGroups.ReceiveStep, ParaleanGroups.receive.ext.tr] at h
  dsimp [getFrom, setIn, instIsSubStateOfRefl, Veil.FieldRepresentation.get,
    ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation] at h
  rcases h with ⟨_, _, _, _, hs⟩
  subst s'
  exact ⟨rfl, rfl, rfl⟩

/-- Target chain from the epoch record and certificates. The head recorded in a
target's owner/epoch record is a published proof of that name that tops every
published proof of it. If it has a certificate quorum, every fully live read
quorum's certificate scan finds it, and any live, online node that does not know
it (for example a new owner after reassignment, whose index was erased) can
receive it by a step that passes all five guards. The new owner's prepare must
then revise exactly that recorded head (`ParaleanTargetNames.guard_observable`). -/
theorem recorded_head_receivable (a : ATheory) (r : RTheory) (encode : record → Nat)
    (cfg : Config a token record) (ha : ParaleanAdmission.Assumptions a)
    {s : ModelState} {e : XState} (hr : Reachable a r encode cfg (s, e))
    (x : name) (hx : ParaleanTargetNames.IsTarget a cfg.targets x) (h : group)
    (hh : e.2.2.2.head x = some h) (hcq : ParaleanAckCertificates.CertQuorum a e.2.1 h) :
    s.admission.protocol.registry.published h = true ∧ a.registry.member h x = true ∧
    (∀ g, s.admission.protocol.registry.published g = true → a.registry.member g x = true →
      g = h ∨ a.registry.revisions h g x = true) ∧
    (∀ q, (∀ y, a.storage.memberR y q = true → s.admission.protocol.storage.live y = true) →
      ParaleanAckCertificates.certScan a s e.2.1 q h) ∧
    (∀ n, s.admission.protocol.registry.alive n = true → s.admission.protocol.registry.online n = true →
      s.admission.protocol.registry.known n h = false →
      ∃ rg', rg'.known n h = true ∧
        Next a r encode cfg (s, e)
          (⟨⟨s.admission.delivery, ⟨rg', s.admission.protocol.storage⟩⟩, s.recovery⟩, e)) := by
  have hT := reachable_targets a r encode cfg hr
  have hA := reachable_certificates a r encode cfg hr
  have tops := ParaleanTargetNames.recorded_head_tops_chain a cfg.targets r encode ha hT x hx
  obtain ⟨hpub, hmem⟩ := tops.1 h hh
  have hscan : ∀ q, (∀ y, a.storage.memberR y q = true → s.admission.protocol.storage.live y = true) →
      ParaleanAckCertificates.certScan a s e.2.1 q h :=
    fun q hq => ParaleanAckCertificates.scan_complete a r encode ha hA h hcq q hq
  refine ⟨hpub, hmem, ?_, hscan, ?_⟩
  · intro g hg hm
    obtain ⟨h', hh', hrev⟩ := tops.2 g hg hm
    rw [hh] at hh'; cases hh'
    exact hrev
  · intro n alive online missing
    obtain ⟨q, hq⟩ := ParaleanAckCertificates.live_quorum_exists a r encode ha hA
    obtain ⟨y, hy, hl, hc⟩ := hscan q hq
    obtain ⟨rg', ht, hk, hAN⟩ := ParaleanAckCertificates.receive_guard_physical a r encode ha hA n h
      ⟨q, y, hy, hl, hc⟩ alive online missing
    have heff := receive_registry_effect a.registry _ _ n h ht
    let t : ModelState := ⟨⟨s.admission.delivery, ⟨rg', s.admission.protocol.storage⟩⟩, s.recovery⟩
    refine ⟨rg', hk, hAN.1, ?_, ?_, ?_, hAN.2, ?_⟩
    · intro n' d h1 h2
      have h1' : t.admission.protocol.registry.pending n' d = true := h1
      simp only [t, heff.1] at h1'
      simp_all
    · exact ParaleanTargetNames.guard_of_quiet a cfg.targets r encode s t e.2.2.2
        (fun n' d h' => by simpa [t, heff.1] using h') (fun d h' => by simpa [t, heff.2.1] using h')
    · have hst : t.admission.protocol.storage = s.admission.protocol.storage := rfl
      refine ⟨fun c hf => absurd hf.1 (ParaleanCatalogFencing.same_storage_no_write encode hst c), ?_⟩
      exact (ParaleanCatalogFencing.update_quiet encode e.1
        (ParaleanCatalogFencing.same_storage_no_write encode hst)).symm
    · refine Or.inl ⟨?_, (ParaleanCatalogCertificates.clearLost_same s t e.2.2.1 rfl).symm⟩
      intro c h1 h2
      have h2' : s.recovery.committed c = true := h2
      rw [h1] at h2'; cases h2'

end
end ParaleanHardened

#print axioms ParaleanHardened.hardened_safe
#print axioms ParaleanHardened.hardened_certified_recovery
#print axioms ParaleanHardened.recorded_head_receivable
