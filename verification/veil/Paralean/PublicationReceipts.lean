import Paralean.Protocol
import Paralean.ProtocolExecution

/-! Publication gated by a trusted validator receipt. The base `prepare` reads
the oracle `valid d` at the publishing worker. Here a step may newly stage
`pending n d` only while the pre-state transport holds an intact, verified
receipt whose signed object is exactly `d`. The hardened `Next` still uses base
`prepare` (which keeps `require valid d`); the section "Untrusted workers" adds
a prepare with that requirement removed and shows that, under the guard,
publication rests on `receipt_sound` (trusted validator) alone. -/
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace ParaleanPublicationReceipts
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
local notation "DState" => ParaleanDelivery.CanonicalState node group request packet snapshot name

/-! ## Registry facts used by the guard -/

theorem groups_init_empty (th : ParaleanGroups.Theory node group name snapshot)
    (rg : ParaleanGroups.CanonicalState node group name snapshot)
    (h : ParaleanGroups.GroupsInit th rg) :
    (∀ d, rg.published d = false) ∧ (∀ n d, rg.pending n d = false) := by
  dsimp [ParaleanGroups.GroupsInit, ParaleanGroups.Init,
    ParaleanGroups.initializer.ext.tr, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation] at h
  subst rg
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

/-- Every generated registry action publishes only groups some worker staged. -/
theorem groups_published_source (th : ParaleanGroups.Theory node group name snapshot)
    (rg rg' : ParaleanGroups.CanonicalState node group name snapshot)
    (l : ParaleanGroups.Label node group name snapshot)
    (h : ParaleanGroups.GroupsNext th rg l rg') (d : group) (hp : rg'.published d = true) :
    rg.published d = true ∨ ∃ n, rg.pending n d = true := by
  cases l <;>
    simp only [ParaleanGroups.GroupsNext, ParaleanGroups.Next, ParaleanGroups.NextAct,
      ParaleanGroups.prepare.ext.derived_eq, ParaleanGroups.publish.ext.derived_eq,
      ParaleanGroups.receive.ext.derived_eq, ParaleanGroups.commit.ext.derived_eq,
      ParaleanGroups.crash.ext.derived_eq, ParaleanGroups.recover.ext.derived_eq,
      ParaleanGroups.partition.ext.derived_eq, ParaleanGroups.reconnect.ext.derived_eq,
      ParaleanGroups.heal.ext.derived_eq] at h
  all_goals
    dsimp [ParaleanGroups.prepare.ext.tr, ParaleanGroups.publish.ext.tr,
      ParaleanGroups.receive.ext.tr, ParaleanGroups.commit.ext.tr,
      ParaleanGroups.crash.ext.tr, ParaleanGroups.recover.ext.tr,
      ParaleanGroups.partition.ext.tr, ParaleanGroups.reconnect.ext.tr,
      ParaleanGroups.heal.ext.tr, getFrom, setIn, readFrom,
      Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
      ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation] at h
    simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp] at h
    try split_ifs at h
    all_goals
      repeat' rcases h with ⟨ha, h⟩
      try subst rg'
      simp_all
  all_goals grind

/-- The generated prepare action: exact enabling conditions. -/
theorem groups_prepare_iff (th : ParaleanGroups.Theory node group name snapshot)
    (rg : ParaleanGroups.CanonicalState node group name snapshot) (n : node) (d : group) :
    (∃ rg', ParaleanGroups.GroupsNext th rg (.prepare n d) rg') ↔
      rg.alive n = true ∧ th.valid d = true ∧
      (∀ e, th.deps d e = true → rg.known n e = true) ∧
      (∀ e, th.ancestors d e = true → rg.known n e = true) ∧
      ¬th.deps d d = true ∧ ¬th.ancestors d d = true := by
  simp only [ParaleanGroups.GroupsNext, ParaleanGroups.Next, ParaleanGroups.NextAct,
    ParaleanGroups.prepare.ext.derived_eq]
  dsimp [ParaleanGroups.prepare.ext.tr, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation]
  constructor
  · rintro ⟨rg', h⟩
    repeat' rcases h with ⟨_, h⟩
    grind
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨_, h1, h2, h3, h4, h5, h6, rfl⟩

/-- Prepare stages exactly its own `(n, d)` and nothing else. -/
theorem groups_prepare_pending (th : ParaleanGroups.Theory node group name snapshot)
    (rg rg' : ParaleanGroups.CanonicalState node group name snapshot) (n : node) (d : group)
    (h : ParaleanGroups.GroupsNext th rg (.prepare n d) rg') (n' : node) (d' : group) :
    rg'.pending n' d' = true ↔ rg.pending n' d' = true ∨ (n' = n ∧ d' = d) := by
  simp only [ParaleanGroups.GroupsNext, ParaleanGroups.Next, ParaleanGroups.NextAct,
    ParaleanGroups.prepare.ext.derived_eq] at h
  dsimp [ParaleanGroups.prepare.ext.tr, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation] at h
  repeat' rcases h with ⟨_, h⟩
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]
  grind

/-! ## Hardened model -/

/-- A trusted validator receipt exists for exactly `d` (immutable theory fact). -/
def Receipted (a : ATheory) (d : group) : Prop :=
  ∃ m, a.delivery.verified m = true ∧ a.delivery.intact m = true ∧ a.delivery.receiptObject m = d

/-- The worker observes such a receipt in its transport state. -/
def HeldReceipt (a : ATheory) (dl : DState) (d : group) : Prop :=
  ∃ m, dl.flight m = true ∧ a.delivery.verified m = true ∧ a.delivery.intact m = true ∧
    a.delivery.receiptObject m = d

abbrev Extra := Unit

/-- Newly staging `pending n d` requires a held verified receipt for `d`. -/
def Guard (a : ATheory) (r : RTheory) (encode : record → Nat)
    (s : ModelState) (e : Extra) (t : ModelState) (e' : Extra) : Prop :=
  ∀ n d, t.admission.protocol.registry.pending n d = true →
    ¬s.admission.protocol.registry.pending n d = true → HeldReceipt a s.admission.delivery d

def Next (a : ATheory) (r : RTheory) (encode : record → Nat)
    (p q : ModelState × Extra) : Prop :=
  ParaleanProtocol.Next a r encode p.1 q.1 ∧ Guard a r encode p.1 p.2 q.1 q.2

def Initial (a : ATheory) (r : RTheory) (p : ModelState × Extra) : Prop :=
  ParaleanCompletionRecovery.Initial a r p.1

inductive Reachable (a : ATheory) (r : RTheory) (encode : record → Nat) : ModelState × Extra → Prop where
  | initial {p} : Initial a r p → Reachable a r encode p
  | step {p q} : Reachable a r encode p → Next a r encode p q → Reachable a r encode q

theorem guard_stutter (a : ATheory) (r : RTheory) (encode : record → Nat) (s : ModelState) (e : Extra) :
    Guard a r encode s e s e := fun _ _ h h' => absurd h h'

theorem guard_of_registry_eq (a : ATheory) (r : RTheory) (encode : record → Nat)
    {s t : ModelState} (e e' : Extra)
    (h : t.admission.protocol.registry = s.admission.protocol.registry) :
    Guard a r encode s e t e' := by
  intro n d ht hs; rw [h] at ht; exact absurd ht hs

theorem reachable_protocol (a : ATheory) (r : RTheory) (encode : record → Nat)
    {p} (h : Reachable a r encode p) : ParaleanProtocol.Reachable a r encode p.1 := by
  induction h with
  | initial hi => exact .initial hi
  | step _ ht ih => exact .step ih ht.1

def Inv (a : ATheory) (s : ModelState) : Prop :=
  (∀ d, s.admission.protocol.registry.published d = true → Receipted a d) ∧
  (∀ n d, s.admission.protocol.registry.pending n d = true → Receipted a d)

theorem held_receipted (a : ATheory) {dl : DState} {d : group} (h : HeldReceipt a dl d) :
    Receipted a d := by
  obtain ⟨m, _, hv, hi, ho⟩ := h; exact ⟨m, hv, hi, ho⟩

theorem next_inv (a : ATheory) (r : RTheory) (encode : record → Nat)
    {p q : ModelState × Extra} (hs : Inv a p.1) (ht : Next a r encode p q) : Inv a q.1 := by
  obtain ⟨hn, hg⟩ := ht
  rcases ParaleanPublicationDiscovery.next_registry_projection _ (hn.discovery a r encode) with heq | ⟨l, hl⟩
  · refine ⟨fun d hd => hs.1 d ?_, fun n d hd => hs.2 n d ?_⟩
    · have : q.1.admission.protocol.registry = p.1.admission.protocol.registry := heq
      rw [this] at hd; exact hd
    · have : q.1.admission.protocol.registry = p.1.admission.protocol.registry := heq
      rw [this] at hd; exact hd
  · refine ⟨fun d hd => ?_, fun n d hd => ?_⟩
    · rcases groups_published_source a.registry _ _ l hl d hd with hp | ⟨n, hp⟩
      · exact hs.1 d hp
      · exact hs.2 n d hp
    · by_cases hp : p.1.admission.protocol.registry.pending n d = true
      · exact hs.2 n d hp
      · exact held_receipted a (hg n d hd hp)

/-- Safety: every published or staged group carries a verified, intact receipt. -/
theorem published_receipted (a : ATheory) (r : RTheory) (encode : record → Nat)
    {p} (h : Reachable a r encode p) : Inv a p.1 := by
  induction h with
  | initial hi =>
    have he := groups_init_empty a.registry _ hi.1.2.1
    exact ⟨fun d hd => by simp [he.1 d] at hd, fun n d hd => by simp [he.2 n d] at hd⟩
  | step _ ht ih => exact next_inv a r encode ih ht

/-- Groups with no verified receipt are never published (no assumptions used). -/
theorem unreceipted_never_published (a : ATheory) (r : RTheory) (encode : record → Nat)
    {p} (h : Reachable a r encode p) (d : group) (none : ¬Receipted a d) :
    ¬p.1.admission.protocol.registry.published d = true :=
  fun hp => none ((published_receipted a r encode h).1 d hp)

/-- The trusted receipt plus component compatibility supplies `valid d`. -/
theorem receipt_implies_valid (a : ATheory) (ha : ParaleanAdmission.Assumptions a)
    {d : group} (h : Receipted a d) : a.registry.valid d = true := by
  obtain ⟨m, hv, _, ho⟩ := h
  have hs := ha.1
  simp only [ParaleanAdmission.DeliveryAssumptions, ParaleanDelivery.Assumptions,
    ParaleanDelivery.receipt_sound, readFrom, instIsSubReaderOfRefl] at hs
  have := (hs m hv).1
  simp only [id] at this
  rw [ho, ha.2.2.1] at this
  exact this

/-- Invalid groups are never published; derived from receipts alone. -/
theorem invalid_never_published (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a) {p} (h : Reachable a r encode p) (d : group)
    (invalid : ¬a.registry.valid d = true) :
    ¬p.1.admission.protocol.registry.published d = true :=
  unreceipted_never_published a r encode h d (fun hr => invalid (receipt_implies_valid a ha hr))

/-- Enabledness: in the hardened model a fresh prepare for `(n, d)` is enabled iff
the worker holds a verified receipt for `d` and the non-validity registry guards
hold. `valid d` does not appear on the right because the receipt implies it
(base `prepare` still evaluates it; see `untrusted_step_is_protocol_step`). -/
theorem prepare_enabled_iff (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    (dl : DState) (rg : ParaleanGroups.CanonicalState node group name snapshot)
    (disk : ParaleanGroupComposition.DiskState replica (ParaleanAdmission.StoredObject group snapshot) writeQuorum readQuorum)
    (rec : ParaleanRecovery.CanonicalState record workspace snapshot group name token scan)
    (n : node) (d : group) (fresh : ¬rg.pending n d = true) :
    (∃ rg', ParaleanGroups.GroupsNext a.registry rg (.prepare n d) rg' ∧
      Next a r encode (⟨⟨dl, ⟨rg, disk⟩⟩, rec⟩, ()) (⟨⟨dl, ⟨rg', disk⟩⟩, rec⟩, ())) ↔
      HeldReceipt a dl d ∧ rg.alive n = true ∧
      (∀ e, a.registry.deps d e = true → rg.known n e = true) ∧
      (∀ e, a.registry.ancestors d e = true → rg.known n e = true) ∧
      ¬a.registry.deps d d = true ∧ ¬a.registry.ancestors d d = true := by
  constructor
  · rintro ⟨rg', hp, _, hg⟩
    obtain ⟨alive, _, deps, anc, self⟩ := (groups_prepare_iff a.registry rg n d).1 ⟨rg', hp⟩
    have pend := (groups_prepare_pending a.registry rg rg' n d hp n d).2 (Or.inr ⟨rfl, rfl⟩)
    exact ⟨hg n d pend fresh, alive, deps, anc, self⟩
  · rintro ⟨held, alive, deps, anc, self⟩
    have valid := receipt_implies_valid a ha (held_receipted a held)
    obtain ⟨rg', hp⟩ := (groups_prepare_iff a.registry rg n d).2 ⟨alive, valid, deps, anc, self⟩
    refine ⟨rg', hp, ?_, ?_⟩
    · exact .paired (.admission (.registry (.prepare n d) trivial hp trivial) rfl)
        (.registry (.prepare n d) (by intros; simp) hp trivial (by intros; contradiction))
    · intro n' d' ht hs
      rcases (groups_prepare_pending a.registry rg rg' n d hp n' d').1 ht with h | ⟨_, rfl⟩
      · exact absurd h hs
      · exact held

/-- Under the guard, the base `valid d` requirement of every fresh prepare is redundant. -/
theorem valid_guard_redundant (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a) {p q : ModelState × Extra}
    (ht : Next a r encode p q) (n : node) (d : group)
    (staged : q.1.admission.protocol.registry.pending n d = true)
    (fresh : ¬p.1.admission.protocol.registry.pending n d = true) :
    a.registry.valid d = true :=
  receipt_implies_valid a ha (held_receipted a (ht.2 n d staged fresh))

/-! ## Untrusted workers

The hardened `Next` above is `ParaleanProtocol.Next ∧ Guard`, and base `prepare`
still requires `valid d`, so on its own it cannot express a worker that skips
or lies about validity. Here a worker's prepare is modelled with the validity
requirement removed: `unchecked th` is the registry theory with `valid` replaced
by the constant `true`, so `GroupsNext (unchecked th) rg (.prepare n d) rg'` is
exactly the generated prepare transition minus `require valid d`. -/

/-- The registry theory as seen by a worker that does not check validity. -/
def unchecked (th : ParaleanGroups.Theory node group name snapshot) :
    ParaleanGroups.Theory node group name snapshot :=
  { th with valid := fun _ => true }

/-- An untrusted (buggy or Byzantine) worker stages `d` at `n`: the state change
of `ParaleanGroups.prepare`, lifted through the protocol state, with every
requirement except `valid d`. -/
def UntrustedPrepare (a : ATheory) (n : node) (d : group) (s t : ModelState) : Prop :=
  ∃ rg', ParaleanGroups.GroupsNext (unchecked a.registry) s.admission.protocol.registry (.prepare n d) rg' ∧
    t = ⟨⟨s.admission.delivery, ⟨rg', s.admission.protocol.storage⟩⟩, s.recovery⟩

/-- Enabledness of an untrusted prepare: `valid d` is absent. -/
theorem untrusted_prepare_enabled_iff (th : ParaleanGroups.Theory node group name snapshot)
    (rg : ParaleanGroups.CanonicalState node group name snapshot) (n : node) (d : group) :
    (∃ rg', ParaleanGroups.GroupsNext (unchecked th) rg (.prepare n d) rg') ↔
      rg.alive n = true ∧
      (∀ e, th.deps d e = true → rg.known n e = true) ∧
      (∀ e, th.ancestors d e = true → rg.known n e = true) ∧
      ¬th.deps d d = true ∧ ¬th.ancestors d d = true := by
  rw [groups_prepare_iff]
  simp [unchecked]

/-- An unchecked prepare whose group is in fact valid is a genuine prepare. -/
theorem prepare_of_unchecked (th : ParaleanGroups.Theory node group name snapshot)
    (rg rg' : ParaleanGroups.CanonicalState node group name snapshot) (n : node) (d : group)
    (h : ParaleanGroups.GroupsNext (unchecked th) rg (.prepare n d) rg')
    (hv : th.valid d = true) : ParaleanGroups.GroupsNext th rg (.prepare n d) rg' := by
  simp only [ParaleanGroups.GroupsNext, ParaleanGroups.Next, ParaleanGroups.NextAct,
    ParaleanGroups.prepare.ext.derived_eq] at h ⊢
  dsimp [ParaleanGroups.prepare.ext.tr, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation, unchecked] at h ⊢
  obtain ⟨h1, _, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, hv, h3, h4, h5, h6, h7⟩

/-- Every genuine prepare is also an unchecked one. -/
theorem unchecked_of_prepare (th : ParaleanGroups.Theory node group name snapshot)
    (rg rg' : ParaleanGroups.CanonicalState node group name snapshot) (n : node) (d : group)
    (h : ParaleanGroups.GroupsNext th rg (.prepare n d) rg') :
    ParaleanGroups.GroupsNext (unchecked th) rg (.prepare n d) rg' := by
  simp only [ParaleanGroups.GroupsNext, ParaleanGroups.Next, ParaleanGroups.NextAct,
    ParaleanGroups.prepare.ext.derived_eq] at h ⊢
  dsimp [ParaleanGroups.prepare.ext.tr, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation, unchecked] at h ⊢
  obtain ⟨h1, _, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, rfl, h3, h4, h5, h6, h7⟩

/-- Steps available when workers are untrusted: every protocol step, plus an
unchecked prepare by any worker. -/
def UStep (a : ATheory) (r : RTheory) (encode : record → Nat)
    (p q : ModelState × Extra) : Prop :=
  ParaleanProtocol.Next a r encode p.1 q.1 ∨ ∃ n d, UntrustedPrepare a n d p.1 q.1

/-- Untrusted workers under the receipt guard. -/
def UNext (a : ATheory) (r : RTheory) (encode : record → Nat)
    (p q : ModelState × Extra) : Prop :=
  UStep a r encode p q ∧ Guard a r encode p.1 p.2 q.1 q.2

inductive UReachable (a : ATheory) (r : RTheory) (encode : record → Nat) : ModelState × Extra → Prop where
  | initial {p} : Initial a r p → UReachable a r encode p
  | step {p q} : UReachable a r encode p → UNext a r encode p q → UReachable a r encode q

/-- Untrusted workers with no receipt guard (used only for the necessity check). -/
inductive RawReachable (a : ATheory) (r : RTheory) (encode : record → Nat) : ModelState × Extra → Prop where
  | initial {p} : Initial a r p → RawReachable a r encode p
  | step {p q} : RawReachable a r encode p → UStep a r encode p q → RawReachable a r encode q

/-- An untrusted prepare that passes the receipt guard, from a state satisfying
the receipt invariant, is a genuine `ParaleanProtocol.Next` step: `receipt_sound`
recovers the `valid d` the worker skipped. -/
theorem untrusted_step_is_protocol_step (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a) {s t : ModelState} {e e' : Extra} {n : node} {d : group}
    (hs : Inv a s) (hu : UntrustedPrepare a n d s t) (hg : Guard a r encode s e t e') :
    ParaleanProtocol.Next a r encode s t := by
  obtain ⟨⟨dl, ⟨rg, disk⟩⟩, rec⟩ := s
  obtain ⟨rg', hp, rfl⟩ := hu
  have hpend : rg'.pending n d = true :=
    (groups_prepare_pending (unchecked a.registry) rg rg' n d hp n d).2 (Or.inr ⟨rfl, rfl⟩)
  have hr : Receipted a d := by
    by_cases h : rg.pending n d = true
    · exact hs.2 n d h
    · exact held_receipted a (hg n d hpend h)
  have hp' := prepare_of_unchecked a.registry rg rg' n d hp (receipt_implies_valid a ha hr)
  exact .paired (.admission (.registry (.prepare n d) trivial hp' trivial) rfl)
    (.registry (.prepare n d) (by intros; simp) hp' trivial (by intros; contradiction))

/-- Every state reachable with untrusted workers under the guard is reachable in
the hardened model, so every hardened theorem transfers. -/
theorem ureachable_reachable (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a) {p} (h : UReachable a r encode p) :
    Reachable a r encode p := by
  induction h with
  | initial hi => exact .initial hi
  | step _ ht ih =>
    obtain ⟨hu, hg⟩ := ht
    rcases hu with hn | ⟨n, d, hu⟩
    · exact .step ih ⟨hn, hg⟩
    · exact .step ih ⟨untrusted_step_is_protocol_step a r encode ha
        (published_receipted a r encode ih) hu hg, hg⟩

theorem reachable_ureachable (a : ATheory) (r : RTheory) (encode : record → Nat)
    {p} (h : Reachable a r encode p) : UReachable a r encode p := by
  induction h with
  | initial hi => exact .initial hi
  | step _ ht ih => exact .step ih ⟨Or.inl ht.1, ht.2⟩

theorem ureachable_iff (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a) (p : ModelState × Extra) :
    UReachable a r encode p ↔ Reachable a r encode p :=
  ⟨ureachable_reachable a r encode ha, reachable_ureachable a r encode⟩

/-- With untrusted workers under the guard, every published group is valid and
receipted, and so is every staged group. -/
theorem invalid_never_published_untrusted (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a) {p} (h : UReachable a r encode p) :
    (∀ d, p.1.admission.protocol.registry.published d = true →
      a.registry.valid d = true ∧ Receipted a d) ∧
    (∀ n d, p.1.admission.protocol.registry.pending n d = true →
      a.registry.valid d = true ∧ Receipted a d) := by
  have hi := published_receipted a r encode (ureachable_reachable a r encode ha h)
  exact ⟨fun d hd => ⟨receipt_implies_valid a ha (hi.1 d hd), hi.1 d hd⟩,
    fun n d hd => ⟨receipt_implies_valid a ha (hi.2 n d hd), hi.2 n d hd⟩⟩

theorem groups_init_alive (th : ParaleanGroups.Theory node group name snapshot)
    (rg : ParaleanGroups.CanonicalState node group name snapshot)
    (h : ParaleanGroups.GroupsInit th rg) : ∀ n, rg.alive n = true := by
  dsimp [ParaleanGroups.GroupsInit, ParaleanGroups.Init,
    ParaleanGroups.initializer.ext.tr, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation] at h
  subst rg
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

/-- Guard necessity: without the guard, an untrusted worker stages an invalid
group with no dependencies or ancestors in one step from any initial state,
whereas with the guard no reachable state stages or publishes it. -/
theorem guard_necessary (a : ATheory) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a) {s : ModelState}
    (hi : ParaleanCompletionRecovery.Initial a r s) (n : node) (d : group)
    (invalid : ¬a.registry.valid d = true)
    (nodeps : ∀ e, a.registry.deps d e = false) (noanc : ∀ e, a.registry.ancestors d e = false) :
    (∃ t, RawReachable a r encode (t, ()) ∧ t.admission.protocol.registry.pending n d = true) ∧
    ∀ p, UReachable a r encode p →
      ¬p.1.admission.protocol.registry.pending n d = true ∧
      ¬p.1.admission.protocol.registry.published d = true := by
  refine ⟨?_, fun p hp => ⟨fun h => invalid ((invalid_never_published_untrusted a r encode ha hp).2 n d h).1,
    fun h => invalid ((invalid_never_published_untrusted a r encode ha hp).1 d h).1⟩⟩
  have alive := groups_init_alive a.registry _ hi.1.2.1 n
  obtain ⟨rg', hp⟩ := (untrusted_prepare_enabled_iff a.registry s.admission.protocol.registry n d).2
    ⟨alive, fun e he => by simp [nodeps e] at he, fun e he => by simp [noanc e] at he,
      by simp [nodeps d], by simp [noanc d]⟩
  refine ⟨⟨⟨s.admission.delivery, ⟨rg', s.admission.protocol.storage⟩⟩, s.recovery⟩, ?_, ?_⟩
  · exact .step (p := (s, ())) (.initial hi) (Or.inr ⟨n, d, rg', hp, rfl⟩)
  · exact (groups_prepare_pending (unchecked a.registry) _ rg' n d hp n d).2 (Or.inr ⟨rfl, rfl⟩)

end
end ParaleanPublicationReceipts

/-! ## Concrete instances -/
namespace ParaleanPublicationReceipts.Example
noncomputable section
open ParaleanAdmission
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

abbrev CR := ParaleanCompletionRecovery.Example.theory
abbrev RT := ParaleanCompletionRecovery.Example.recoveryTheory
abbrev EN := ParaleanCompletionRecovery.Example.encode
abbrev st := ParaleanProtocol.Example.state
abbrev dl0 := ParaleanCompletionRecovery.Example.dl0
abbrev dlS := ParaleanCompletionRecovery.Example.dlSentHelper
abbrev dlH := ParaleanCompletionRecovery.Example.dlStartedHelper
abbrev rg0 := ParaleanCompletionRecovery.Example.rg0
abbrev rgP := ParaleanCompletionRecovery.Example.rgPreparedHelper
abbrev rgH := ParaleanCompletionRecovery.Example.rgHelper
open ParaleanProtocol.Example (d0 d1 d2 d3 d4 d5 d6)

theorem same (s t : ParaleanProtocol.Example.ModelState)
    (h : t.admission.protocol.registry = s.admission.protocol.registry) :
    Guard CR RT EN s () t () := guard_of_registry_eq CR RT EN () () h

/-- The run up to the point where the helper group's payload and publication
objects are durable and the worker holds a receipt for it. -/
theorem before_prepare_reachable : Reachable CR RT EN (st dlS rg0 d5, ()) := by
  open ParaleanCompletionRecovery.Example in
  have h0 : Reachable CR RT EN (st dl0 rg0 d0, ()) := .initial ParaleanProtocol.Example.initial_valid
  have h1 : Reachable CR RT EN (st dlH rg0 d0, ()) := .step h0
    ⟨ParaleanProtocol.Example.control_joint dl0 dlH rg0 d0 (.start true false) trivial delivery_steps.2.1,
      same _ _ rfl⟩
  have h2 : Reachable CR RT EN (st dlS rg0 d0, ()) := .step h1
    ⟨ParaleanProtocol.Example.control_joint dlH dlS rg0 d0 (.send false) trivial delivery_steps.2.2.1,
      same _ _ rfl⟩
  have h3 : Reachable CR RT EN (st dlS rg0 d1, ()) := .step h2
    ⟨ParaleanProtocol.Example.put_joint dlS rg0 d0 false (.payload false) rfl, same _ _ rfl⟩
  have h4 : Reachable CR RT EN (st dlS rg0 d2, ()) := .step h3
    ⟨ParaleanProtocol.Example.put_joint dlS rg0 d1 true (.payload false) rfl, same _ _ rfl⟩
  have h5 : Reachable CR RT EN (st dlS rg0 d3, ()) := .step h4
    ⟨ParaleanProtocol.Example.ack_joint dlS rg0 d2 (.payload false)
      (by intro r; cases r <;> simp [d2, d1, d0, disk0, put]) trivial, same _ _ rfl⟩
  have h6 : Reachable CR RT EN (st dlS rg0 d4, ()) := .step h5
    ⟨ParaleanProtocol.Example.put_joint dlS rg0 d3 false (.publication false) rfl, same _ _ rfl⟩
  exact .step h6
    ⟨ParaleanProtocol.Example.put_joint dlS rg0 d4 true (.publication false) rfl, same _ _ rfl⟩

theorem held_helper : HeldReceipt CR dlS false := ⟨false, rfl, rfl, rfl, rfl⟩

theorem guard_helper (s t : ParaleanProtocol.Example.ModelState)
    (ht : t.admission.protocol.registry = rgP) (hs : s.admission.delivery = dlS) :
    Guard CR RT EN s () t () := by
  open ParaleanCompletionRecovery.Example in
  intro n d hp _
  rw [ht] at hp
  simp [rgP, rgPreparedHelper] at hp
  obtain ⟨rfl, rfl⟩ := hp
  rw [hs]; exact held_helper

theorem publish_helper :
    ParaleanProtocol.Next CR RT EN (st dlS rgP d5) (st dlS rgH d6) ∧
      Guard CR RT EN (st dlS rgP d5) () (st dlS rgH d6) () := by
  open ParaleanCompletionRecovery.Example in
  refine ⟨ParaleanProtocol.Example.publish_joint dlS rgP rgH d5 false group_steps.2.2.1
      (by simp [d5, d4, d3, ack, put])
      (by intro r; cases r <;> simp [d5, d4, d3, d2, d1, d0, disk0, put, ack]), ?_⟩
  intro n d ht _
  simp [st, ParaleanProtocol.Example.state, rgH, rgHelper, ParaleanCompletionRecovery.Example.rg0] at ht

/-- Non-vacuity: the worker receives a verified receipt for the helper group,
stages it under the receipt guard and atomically publishes it. -/
theorem receipted_publication_reachable :
    Reachable CR RT EN (st dlS rgH d6, ()) ∧
      rgH.published false = true ∧ HeldReceipt CR dlS false := by
  have h8 : Reachable CR RT EN (st dlS rgP d5, ()) := .step before_prepare_reachable
    ⟨ParaleanProtocol.Example.prepare_joint dlS rg0 rgP d5 false
      ParaleanCompletionRecovery.Example.group_steps.2.1, guard_helper _ _ rfl rfl⟩
  exact ⟨.step h8 publish_helper, rfl, held_helper⟩

/-- Non-vacuity for untrusted workers: the helper group is staged by an
unchecked prepare (no validity evaluation), admitted by the receipt guard, and
published. -/
theorem untrusted_publication_reachable :
    UReachable CR RT EN (st dlS rgH d6, ()) ∧ rgH.published false = true ∧
      UntrustedPrepare CR false false (st dlS rg0 d5) (st dlS rgP d5) := by
  have hu : UntrustedPrepare CR false false (st dlS rg0 d5) (st dlS rgP d5) :=
    ⟨rgP, unchecked_of_prepare _ _ _ false false
      ParaleanCompletionRecovery.Example.group_steps.2.1, rfl⟩
  have h8 : UReachable CR RT EN (st dlS rgP d5, ()) :=
    .step (reachable_ureachable CR RT EN before_prepare_reachable)
      ⟨Or.inr ⟨false, false, hu⟩, guard_helper _ _ rfl rfl⟩
  exact ⟨.step h8 ⟨Or.inl publish_helper.1, publish_helper.2⟩, rfl, hu⟩

/-! Guard necessity: same registry and storage, but the validator never signs. -/

def deliveryBad : ParaleanDelivery.Theory Bool Bool Bool Bool Bool (Fin 3) :=
  { ParaleanCompletionRecovery.Example.deliveryTheory with verified := fun _ => false }

def theoryBad : Theory Bool Bool (Fin 3) Bool Bool Bool Bool Unit Unit :=
  ⟨deliveryBad, ParaleanCompletionRecovery.Example.groupTheory, ParaleanCompletionRecovery.Example.storageTheory⟩

theorem bad_assumptions : Assumptions theoryBad := by
  refine ⟨?_, ParaleanCompletionRecovery.Example.assumptions.2.1, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  simp [DeliveryAssumptions, ParaleanDelivery.Assumptions, ParaleanDelivery.receipt_sound,
    theoryBad, deliveryBad, readFrom, instIsSubReaderOfRefl]

theorem bad_initial : ParaleanCompletionRecovery.Initial theoryBad RT (st dl0 rg0 d0) := by
  refine ⟨⟨?_, ParaleanCompletionRecovery.Example.group_steps.1,
    ParaleanCompletionRecovery.Example.initial_valid.2.2⟩,
    ParaleanCompletionRecovery.Example.recovery_initial⟩
  simp [ParaleanDelivery.Initial, ParaleanDelivery.Init, ParaleanDelivery.initializer.ext.tr,
    st, ParaleanProtocol.Example.state, deliveryBad, ParaleanCompletionRecovery.Example.dl0,
    getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanDelivery.canonicalFieldRep, Veil.canonicalFieldRepresentation,
    Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]

theorem bad_put (rg : ParaleanCompletionRecovery.Example.Registry) (disk : ParaleanProtocol.Example.Disk)
    (r : Bool) (o : StoredObject Bool Bool) (live : disk.live r = true) :
    ParaleanProtocol.Next theoryBad RT EN (st dl0 rg disk) (st dl0 rg (ParaleanCompletionRecovery.Example.put disk r o)) :=
  ParaleanProtocol.storage_step theoryBad RT EN dl0 rg ParaleanCompletionRecovery.Example.rec0 disk _ (.Put r o)
    (ParaleanCompletionRecovery.Example.put_step disk r o live) trivial

/-- The base protocol publishes the valid helper group although no verified
receipt for it (or any group) exists, under all base assumptions. The hardened
model never publishes it. -/
theorem base_publishes_unreceipted :
    Assumptions theoryBad ∧
    ParaleanProtocol.Reachable theoryBad RT EN (st dl0 rgH d6) ∧
    rgH.published false = true ∧
    ParaleanCompletionRecovery.Example.groupTheory.valid false = true ∧
    ¬Receipted theoryBad false ∧
    ∀ p, Reachable theoryBad RT EN p → ¬p.1.admission.protocol.registry.published false = true := by
  open ParaleanCompletionRecovery.Example in
  have h0 : ParaleanProtocol.Reachable theoryBad RT EN (st dl0 rg0 d0) := .initial bad_initial
  have h1 := ParaleanProtocol.Reachable.step h0 (bad_put rg0 d0 false (.payload false) rfl)
  have h2 := ParaleanProtocol.Reachable.step h1 (bad_put rg0 d1 true (.payload false) rfl)
  have h3 := ParaleanProtocol.Reachable.step h2
    (ParaleanProtocol.storage_step theoryBad RT EN dl0 rg0 rec0 d2 _ (.Ack (.payload false) ())
      (ack_step d2 (.payload false) (by intro r; cases r <;> simp [d2, d1, d0, disk0, put])) trivial)
  have h4 := ParaleanProtocol.Reachable.step h3 (bad_put rg0 d3 false (.publication false) rfl)
  have h5 := ParaleanProtocol.Reachable.step h4 (bad_put rg0 d4 true (.publication false) rfl)
  have h6 : ParaleanProtocol.Reachable theoryBad RT EN (st dl0 rgP d5) :=
    ParaleanProtocol.Reachable.step h5
      (.paired (.admission (.registry (.prepare false false) trivial group_steps.2.1 trivial) rfl)
        (.registry (.prepare false false) (by intros; simp) group_steps.2.1 trivial (by intros; contradiction)))
  have h7 : ParaleanProtocol.Reachable theoryBad RT EN (st dl0 rgH d6) :=
    ParaleanProtocol.Reachable.step h6
      (.publish false false () group_steps.2.2.1
        (ack_step d5 (.publication false) (by intro r; cases r <;> simp [d5, d4, d3, d2, d1, d0, disk0, put, ack]))
        (by simp [d5, d4, d3, ack, put]))
  have none : ¬Receipted theoryBad false := by
    rintro ⟨m, hv, _, _⟩; simp [theoryBad, deliveryBad] at hv
  exact ⟨bad_assumptions, h7, rfl, rfl, none,
    fun p hp => unreceipted_never_published theoryBad RT EN hp false none⟩

/-! Untrusted-worker guard necessity: group `false` is invalid and has no
dependencies or ancestors; the validator signs only `true`. -/

def groupInv : ParaleanGroups.Theory Bool Bool (Fin 3) Bool :=
  { ParaleanCompletionRecovery.Example.groupTheory with valid := fun g => g }

def deliveryInv : ParaleanDelivery.Theory Bool Bool Bool Bool Bool (Fin 3) :=
  { ParaleanCompletionRecovery.Example.deliveryTheory with valid := groupInv.valid, verified := fun m => m }

def theoryInv : Theory Bool Bool (Fin 3) Bool Bool Bool Bool Unit Unit :=
  ⟨deliveryInv, groupInv, ParaleanCompletionRecovery.Example.storageTheory⟩

theorem inv_assumptions : Assumptions theoryInv := by
  refine ⟨?_, ⟨?_, ?_⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  · simp [DeliveryAssumptions, ParaleanDelivery.Assumptions, ParaleanDelivery.receipt_sound,
      theoryInv, deliveryInv, groupInv, ParaleanCompletionRecovery.Example.deliveryTheory,
      ParaleanCompletionRecovery.Example.groupTheory, readFrom, instIsSubReaderOfRefl]
  · decide
  · simp [ParaleanGroupComposition.StorageAssumptions, Durability.Assumptions,
      Durability.assumption_0, protocolTheory, theoryInv,
      ParaleanCompletionRecovery.Example.storageTheory, readFrom, instIsSubReaderOfRefl]

theorem inv_initial : ParaleanCompletionRecovery.Initial theoryInv RT (st dl0 rg0 d0) := by
  refine ⟨⟨?_, ?_, ParaleanCompletionRecovery.Example.initial_valid.2.2⟩,
    ParaleanCompletionRecovery.Example.recovery_initial⟩
  · simp [ParaleanDelivery.Initial, ParaleanDelivery.Init, ParaleanDelivery.initializer.ext.tr,
      st, ParaleanProtocol.Example.state, deliveryInv, ParaleanCompletionRecovery.Example.dl0,
      getFrom, setIn, readFrom,
      Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
      ParaleanDelivery.canonicalFieldRep, Veil.canonicalFieldRepresentation,
      Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]
  · simp [ParaleanGroups.GroupsInit, ParaleanGroups.Init, ParaleanGroups.initializer.ext.tr,
      st, ParaleanProtocol.Example.state, groupInv, ParaleanCompletionRecovery.Example.groupTheory,
      ParaleanCompletionRecovery.Example.rg0, protocolTheory, theoryInv, getFrom, setIn, readFrom,
      Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
      ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation,
      Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]

/-- Under all base assumptions, an untrusted worker with no receipt guard stages
the invalid group `false`; with the guard, no reachable state stages or
publishes it. -/
theorem untrusted_invalid_staged_without_guard :
    Assumptions theoryInv ∧ ¬groupInv.valid false = true ∧
    (∃ t, RawReachable theoryInv RT EN (t, ()) ∧ t.admission.protocol.registry.pending false false = true) ∧
    ∀ p, UReachable theoryInv RT EN p →
      ¬p.1.admission.protocol.registry.pending false false = true ∧
      ¬p.1.admission.protocol.registry.published false = true :=
  ⟨inv_assumptions, by simp [groupInv],
    guard_necessary theoryInv RT EN inv_assumptions inv_initial false false (by simp [theoryInv, groupInv])
      (fun e => by simp [theoryInv, groupInv, ParaleanCompletionRecovery.Example.groupTheory])
      (fun e => by simp [theoryInv, groupInv, ParaleanCompletionRecovery.Example.groupTheory])⟩

end
end ParaleanPublicationReceipts.Example

#print axioms ParaleanPublicationReceipts.published_receipted
#print axioms ParaleanPublicationReceipts.unreceipted_never_published
#print axioms ParaleanPublicationReceipts.receipt_implies_valid
#print axioms ParaleanPublicationReceipts.invalid_never_published
#print axioms ParaleanPublicationReceipts.prepare_enabled_iff
#print axioms ParaleanPublicationReceipts.valid_guard_redundant
#print axioms ParaleanPublicationReceipts.guard_stutter
#print axioms ParaleanPublicationReceipts.reachable_protocol
#print axioms ParaleanPublicationReceipts.Example.receipted_publication_reachable
#print axioms ParaleanPublicationReceipts.Example.base_publishes_unreceipted
#print axioms ParaleanPublicationReceipts.untrusted_step_is_protocol_step
#print axioms ParaleanPublicationReceipts.ureachable_iff
#print axioms ParaleanPublicationReceipts.invalid_never_published_untrusted
#print axioms ParaleanPublicationReceipts.guard_necessary
#print axioms ParaleanPublicationReceipts.untrusted_prepare_enabled_iff
#print axioms ParaleanPublicationReceipts.Example.untrusted_publication_reachable
#print axioms ParaleanPublicationReceipts.Example.untrusted_invalid_staged_without_guard
