import Paralean.Groups
import Paralean.Delivery

/-! The receipt and completion actions share a single transition with the
atomic-group/storage protocol. Typed object constructors are the actual payload
and manifest maps used by that protocol. -/
namespace ParaleanAdmission

abbrev StoredObject (group snapshot : Type) := ParaleanArtifacts.Object group snapshot

structure Theory (node group name snapshot request packet replica writeQuorum readQuorum : Type) where
  delivery : ParaleanDelivery.Theory node group request packet snapshot name
  registry : ParaleanGroups.Theory node group name snapshot
  storage : Durability.Theory replica (StoredObject group snapshot) writeQuorum readQuorum

def protocolTheory (th : Theory node group name snapshot request packet replica writeQuorum readQuorum) :
    ParaleanGroupComposition.Theory node group name snapshot replica
      (StoredObject group snapshot) writeQuorum readQuorum where
  registry := th.registry
  storage := th.storage
  payload := ParaleanArtifacts.Object.payload
  manifest := ParaleanArtifacts.Object.manifest

structure State (node group name snapshot request packet replica writeQuorum readQuorum : Type) where
  delivery : ParaleanDelivery.CanonicalState node group request packet snapshot name
  protocol : ParaleanGroupComposition.State node group name snapshot replica
    (StoredObject group snapshot) writeQuorum readQuorum

noncomputable section Proofs
variable {node group name snapshot request packet replica writeQuorum readQuorum : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]
  [DecidableEq request] [Inhabited request] [DecidableEq packet] [Inhabited packet]
  [DecidableEq replica] [Inhabited replica]
  [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum]
attribute [local instance] Classical.propDecidable

instance deliveryStateInhabited : Inhabited
    (ParaleanDelivery.CanonicalState node group request packet snapshot name) :=
  ⟨⟨fun _ => false, fun _ _ => false, fun _ => default, fun _ => 0,
    fun _ => false, fun _ => false, fun _ => default, fun _ => false, fun _ => default⟩⟩

abbrev DeliveryAssumptions := ParaleanDelivery.Assumptions
  (ParaleanDelivery.Theory node group request packet snapshot name)
  node group request packet snapshot name

/-- Both components interpret the same immutable groups and checkpoints. -/
def Compatible (th : Theory node group name snapshot request packet replica writeQuorum readQuorum) : Prop :=
  th.delivery.valid = th.registry.valid ∧ th.delivery.deps = th.registry.deps ∧
  th.delivery.member = th.registry.member ∧ th.delivery.contents = th.registry.contents ∧
  th.delivery.exportable = th.registry.exportable

def Assumptions (th : Theory node group name snapshot request packet replica writeQuorum readQuorum) : Prop :=
  DeliveryAssumptions th.delivery ∧ ParaleanGroupComposition.Assumptions (protocolTheory th) ∧ Compatible th

def Initial (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (s : State node group name snapshot request packet replica writeQuorum readQuorum) : Prop :=
  ParaleanDelivery.Initial th.delivery s.delivery ∧ ParaleanGroupComposition.Init (protocolTheory th) s.protocol

def Safe (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (s : State node group name snapshot request packet replica writeQuorum readQuorum) : Prop :=
  ParaleanDelivery.Safe th.delivery s.delivery ∧ ParaleanGroupComposition.Safe (protocolTheory th) s.protocol

def Control : ParaleanDelivery.Label node group request packet snapshot name → Prop
  | .start _ _ | .cancel _ | .send _ | .drop _ => True
  | .accept _ _ | .finish _ _ => False

/-- Duplicates can acknowledge an already-known group; new receipt uses generated Receive. -/
inductive AcceptProtocol (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) (g : group) :
    ParaleanGroupComposition.State node group name snapshot replica (StoredObject group snapshot) writeQuorum readQuorum →
    ParaleanGroupComposition.State node group name snapshot replica (StoredObject group snapshot) writeQuorum readQuorum → Prop where
  | receive {rg rg' disk} : ParaleanGroups.GroupsNext th.registry rg (.receive n g) rg' →
      AcceptProtocol th n g ⟨rg, disk⟩ ⟨rg', disk⟩
  | duplicate {s} : s.registry.known n g = true → AcceptProtocol th n g s s

def NonCrash : ParaleanGroups.Label node group name snapshot → Prop
  | .crash _ => False
  | _ => True

inductive PassiveProtocol
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum) :
    ParaleanGroupComposition.State node group name snapshot replica (StoredObject group snapshot) writeQuorum readQuorum →
    ParaleanGroupComposition.State node group name snapshot replica (StoredObject group snapshot) writeQuorum readQuorum → Prop where
  | registry {rg rg' disk} (l : ParaleanGroups.Label node group name snapshot) :
      NonCrash l → ParaleanGroups.GroupsNext th.registry rg l rg' →
      ParaleanGroupComposition.Guard (protocolTheory th) disk l → PassiveProtocol th ⟨rg, disk⟩ ⟨rg', disk⟩
  | storage {rg disk disk'} (l : Durability.Label replica (StoredObject group snapshot) writeQuorum readQuorum) :
      ParaleanGroupComposition.StorageNext th.storage disk l disk' → PassiveProtocol th ⟨rg, disk⟩ ⟨rg, disk'⟩
  | stutter {s} : PassiveProtocol th s s

theorem PassiveProtocol.to_next
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (s s') (ht : PassiveProtocol th s s') : ParaleanGroupComposition.Next (protocolTheory th) s s' := by
  cases ht with
  | registry l _ hr hg => exact .registry l hr hg
  | storage l hr => exact .storage l hr
  | stutter => exact .stutter

inductive Next (th : Theory node group name snapshot request packet replica writeQuorum readQuorum) :
    State node group name snapshot request packet replica writeQuorum readQuorum →
    State node group name snapshot request packet replica writeQuorum readQuorum → Prop where
  | control {dl dl' pr} (l : ParaleanDelivery.Label node group request packet snapshot name) :
      Control l → ParaleanDelivery.Step th.delivery dl l dl' → Next th ⟨dl, pr⟩ ⟨dl', pr⟩
  | protocol {dl pr pr'} : PassiveProtocol th pr pr' →
      Next th ⟨dl, pr⟩ ⟨dl, pr'⟩
  | accept {dl dl' pr pr'} (n : node) (m : packet) :
      ParaleanDelivery.Step th.delivery dl (.accept n m) dl' →
      AcceptProtocol th n (th.delivery.packetObject m) pr pr' → Next th ⟨dl, pr⟩ ⟨dl', pr'⟩
  | finish {dl dl' pr pr'} (n : node) (S : snapshot) :
      ParaleanDelivery.Step th.delivery dl (.finish n S) dl' →
      ParaleanGroupComposition.CommitStep (protocolTheory th) n S pr pr' → Next th ⟨dl, pr⟩ ⟨dl', pr'⟩
  | crash {dl dl' rg rg' disk} (n : node) :
      ParaleanDelivery.Step th.delivery dl (.cancel n) dl' →
      ParaleanGroups.GroupsNext th.registry rg (.crash n) rg' →
      Next th ⟨dl, ⟨rg, disk⟩⟩ ⟨dl', ⟨rg', disk⟩⟩
  | stutter {s} : Next th s s

inductive Reachable (th : Theory node group name snapshot request packet replica writeQuorum readQuorum) :
    State node group name snapshot request packet replica writeQuorum readQuorum → Prop where
  | initial {s} : Initial th s → Reachable th s
  | step {s s'} : Reachable th s → Next th s s' → Reachable th s'

theorem AcceptProtocol.to_next
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) (g : group) (s s') (ht : AcceptProtocol th n g s s') :
    ParaleanGroupComposition.Next (protocolTheory th) s s' := by
  cases ht with
  | receive hr => exact .registry (.receive n g) hr trivial
  | duplicate _ => exact .stutter

theorem AcceptProtocol.known
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) (g : group) (s s') (ht : AcceptProtocol th n g s s') :
    s'.registry.known n g = true := by
  cases ht with
  | receive hr =>
    simp only [ParaleanGroups.GroupsNext, ParaleanGroups.Next, ParaleanGroups.NextAct,
      ParaleanGroups.receive.ext.derived_eq] at hr
    exact ParaleanGroups.receive_adds_known th.registry _ _ n g hr
  | duplicate hk => exact hk

theorem initial_safe
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (ha : Assumptions th) (s) (hi : Initial th s) : Safe th s := by
  exact ⟨ParaleanDelivery.Init_preserves _ _ node group request packet snapshot name
    (ParaleanDelivery.CanonicalRep node group request packet snapshot name) th.delivery s.delivery ha.1 hi.1,
    ParaleanGroupComposition.initial_safe (protocolTheory th) ha.2.1 s.protocol hi.2⟩

theorem next_safe
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (ha : Assumptions th) (s s') (hs : Safe th s) (ht : Next th s s') : Safe th s' := by
  cases ht with
  | control l _ hd =>
    exact ⟨ParaleanDelivery.Next_preserves _ _ node group request packet snapshot name
      (ParaleanDelivery.CanonicalRep node group request packet snapshot name)
      th.delivery _ _ l ha.1 hs.1 hd, hs.2⟩
  | protocol hp => exact ⟨hs.1, ParaleanGroupComposition.next_safe (protocolTheory th) ha.2.1 _ _ hs.2 (hp.to_next th _ _)⟩
  | accept n m hd hp =>
    exact ⟨ParaleanDelivery.Next_preserves _ _ node group request packet snapshot name
      (ParaleanDelivery.CanonicalRep node group request packet snapshot name)
      th.delivery _ _ (.accept n m) ha.1 hs.1 hd,
      ParaleanGroupComposition.next_safe (protocolTheory th) ha.2.1 _ _ hs.2 (hp.to_next th n _ _ _)⟩
  | finish n S hd hp =>
    exact ⟨ParaleanDelivery.Next_preserves _ _ node group request packet snapshot name
      (ParaleanDelivery.CanonicalRep node group request packet snapshot name)
      th.delivery _ _ (.finish n S) ha.1 hs.1 hd,
      ParaleanGroupComposition.next_safe (protocolTheory th) ha.2.1 _ _ hs.2 (hp.to_next _ n S _ _)⟩
  | crash n hd hp =>
    exact ⟨ParaleanDelivery.Next_preserves _ _ node group request packet snapshot name
      (ParaleanDelivery.CanonicalRep node group request packet snapshot name)
      th.delivery _ _ (.cancel n) ha.1 hs.1 hd,
      ParaleanGroupComposition.next_safe (protocolTheory th) ha.2.1 _ _ hs.2
        (.registry (.crash n) hp trivial)⟩
  | stutter => exact hs

theorem reachable_safe
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (ha : Assumptions th) {s} (hr : Reachable th s) : Safe th s := by
  induction hr with
  | initial hi => exact initial_safe th ha _ hi
  | step _ ht ih => exact next_safe th ha _ _ ih ht

end Proofs
end ParaleanAdmission

namespace ParaleanAdmission
noncomputable section Events
variable {node group name snapshot request packet replica writeQuorum readQuorum : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]
  [DecidableEq request] [Inhabited request] [DecidableEq packet] [Inhabited packet]
  [DecidableEq replica] [Inhabited replica]
  [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum]
attribute [local instance] Classical.propDecidable

inductive AcceptStep (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) (m : packet) :
    State node group name snapshot request packet replica writeQuorum readQuorum →
    State node group name snapshot request packet replica writeQuorum readQuorum → Prop where
  | paired {dl dl' pr pr'} : ParaleanDelivery.Step th.delivery dl (.accept n m) dl' →
      AcceptProtocol th n (th.delivery.packetObject m) pr pr' → AcceptStep th n m ⟨dl, pr⟩ ⟨dl', pr'⟩

inductive FinishStep (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) (S : snapshot) :
    State node group name snapshot request packet replica writeQuorum readQuorum →
    State node group name snapshot request packet replica writeQuorum readQuorum → Prop where
  | paired {dl dl' pr pr'} : ParaleanDelivery.Step th.delivery dl (.finish n S) dl' →
      ParaleanGroupComposition.CommitStep (protocolTheory th) n S pr pr' → FinishStep th n S ⟨dl, pr⟩ ⟨dl', pr'⟩

theorem AcceptStep.to_next (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) (m : packet) (s s') (ht : AcceptStep th n m s s') : Next th s s' := by
  cases ht with
  | paired hd hp => exact .accept n m hd hp

theorem FinishStep.to_next (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) (S : snapshot) (s s') (ht : FinishStep th n S s s') : Next th s s' := by
  cases ht with
  | paired hd hp => exact .finish n S hd hp

theorem next_protocol_projection
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (s s') (ht : Next th s s') : ParaleanGroupComposition.Next (protocolTheory th) s.protocol s'.protocol := by
  cases ht with
  | control _ _ _ => exact .stutter
  | protocol hp => exact hp.to_next th _ _
  | accept n m _ hp => exact hp.to_next th n _ _ _
  | finish n S _ hp => exact hp.to_next _ n S _ _
  | crash n _ hp => exact .registry (.crash n) hp trivial
  | stutter => exact .stutter

theorem reachable_protocol_projection
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    {s} (hr : Reachable th s) : ParaleanGroupComposition.Reachable (protocolTheory th) s.protocol := by
  induction hr with
  | initial hi => exact .initial hi.2
  | step _ ht ih => exact .step ih (next_protocol_projection th _ _ ht)

theorem AcceptStep.delivery_transition
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) (m : packet) (s s') (ht : AcceptStep th n m s s') :
    ParaleanDelivery.Step th.delivery s.delivery (.accept n m) s'.delivery := by
  cases ht with
  | paired hd _ => exact hd

theorem FinishStep.delivery_transition
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) (S : snapshot) (s s') (ht : FinishStep th n S s s') :
    ParaleanDelivery.Step th.delivery s.delivery (.finish n S) s'.delivery := by
  cases ht with
  | paired hd _ => exact hd

theorem FinishStep.protocol_transition
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) (S : snapshot) (s s') (ht : FinishStep th n S s s') :
    ParaleanGroupComposition.CommitStep (protocolTheory th) n S s.protocol s'.protocol := by
  cases ht with
  | paired _ hp => exact hp

theorem accept_known
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) (m : packet) (s s') (ht : AcceptStep th n m s s') :
    s'.protocol.registry.known n (th.delivery.packetObject m) = true := by
  cases ht with
  | paired _ hp => exact hp.known th n _ _ _

theorem accept_published_durable
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (ha : Assumptions th) {s} (hr : Reachable th s)
    (n : node) (m : packet) (s') (ht : AcceptStep th n m s s') :
    s'.protocol.registry.known n (th.delivery.packetObject m) = true ∧
    s'.protocol.registry.published (th.delivery.packetObject m) = true ∧
    s'.protocol.storage.acknowledged (.payload (th.delivery.packetObject m)) = true ∧
    ∃ r, s'.protocol.storage.live r = true ∧
      s'.protocol.storage.stored r (.payload (th.delivery.packetObject m)) = true := by
  have hn := accept_known th n m s s' ht
  have hs := reachable_safe th ha (Reachable.step hr (ht.to_next th n m s s'))
  have hp := hs.2.1.2.2.1 n (th.delivery.packetObject m) hn
  have hack := hs.2.2.2.1 (th.delivery.packetObject m) hp
  refine ⟨hn, hp, hack, ?_⟩
  exact ParaleanGroupComposition.published_has_copy (protocolTheory th) ha.2.1
    (reachable_protocol_projection th (Reachable.step hr (ht.to_next th n m s s'))) _ hp

theorem finish_complete_current_durable
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (ha : Assumptions th) {s} (hr : Reachable th s)
    (n : node) (S : snapshot) (s') (ht : FinishStep th n S s s') :
    s'.delivery.done n = true ∧ s'.delivery.result n = S ∧
    s'.protocol.registry.head n = S ∧ ParaleanGroups.current n S th.registry s.protocol.registry ∧
    s.protocol.storage.acknowledged (.manifest S) = true ∧
    (∀ r, th.delivery.required r = true → ∃ g, th.delivery.contents S g = true ∧
      s'.delivery.checked g r = true ∧ th.delivery.realizes g r = true) := by
  have hd := ht.delivery_transition th n S s s'
  have he := ParaleanDelivery.finish_effect th.delivery s.delivery s'.delivery n S hd
  have hp := ht.protocol_transition th n S s s'
  have hf := ParaleanGroupComposition.commit_fresh (protocolTheory th) n S s.protocol s'.protocol hp
  have hs := reachable_safe th ha (Reachable.step hr (ht.to_next th n S s s'))
  have hc := (ParaleanDelivery.completion_targets th.delivery s'.delivery hs.1 n he.1).2
  rw [he.2] at hc
  exact ⟨he.1, he.2, hf.2.1, hf.1, hf.2.2, hc⟩

theorem corrupt_rejected
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) (m : packet) (s s') (hc : th.delivery.intact m = false) : ¬AcceptStep th n m s s' := by
  intro ht
  exact ParaleanDelivery.corrupt_rejected th.delivery s.delivery s'.delivery n m hc
    (ht.delivery_transition th n m s s')

theorem stale_rejected
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) (m : packet) (s s') (hc : th.delivery.packetEpoch m ≠ s.delivery.epoch n) :
    ¬AcceptStep th n m s s' := by
  intro ht
  exact ParaleanDelivery.stale_rejected th.delivery s.delivery s'.delivery n m hc
    (ht.delivery_transition th n m s s')

theorem finish_required_groups
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (ha : Assumptions th) {s} (hr : Reachable th s)
    (n : node) (S : snapshot) (s') (ht : FinishStep th n S s s') :
    ∀ r, th.delivery.required r = true →
      ∃ g, th.registry.contents S g = true ∧
      s'.delivery.checked g r = true ∧ th.delivery.realizes g r = true := by
  have hc := (finish_complete_current_durable th ha hr n S s' ht).2.2.2.2.2
  rcases ha.2.2 with ⟨_, _, _, hcontents, _⟩
  rw [hcontents] at hc
  exact hc

theorem finish_enabled_iff
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (s : State node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) (S : snapshot) :
    (∃ s', FinishStep th n S s s') ↔
      (s.delivery.active n = true ∧ ParaleanDelivery.ready S th.delivery s.delivery) ∧
      s.protocol.registry.alive n = true ∧ s.protocol.registry.online n = true ∧
      (∀ g, th.registry.contents S g = true → s.protocol.registry.known n g = true) ∧
      ParaleanGroups.buildable S th.registry s.protocol.registry ∧
      ParaleanGroups.current n S th.registry s.protocol.registry ∧
      s.protocol.storage.acknowledged (.manifest S) = true := by
  constructor
  · rintro ⟨s', ht⟩
    have hd := (ParaleanDelivery.finish_enabled_iff th.delivery s.delivery n S).1
      ⟨s'.delivery, ht.delivery_transition th n S s s'⟩
    have hp := (ParaleanGroupComposition.guarded_commit_enabled_iff (th := protocolTheory th) s.protocol n S).1
      ⟨s'.protocol, ht.protocol_transition th n S s s'⟩
    exact ⟨hd, hp⟩
  · rintro ⟨hd, hp⟩
    obtain ⟨dl', hdl⟩ := (ParaleanDelivery.finish_enabled_iff th.delivery s.delivery n S).2 hd
    obtain ⟨pr', hpr⟩ := (ParaleanGroupComposition.guarded_commit_enabled_iff (th := protocolTheory th) s.protocol n S).2 hp
    cases s
    exact ⟨⟨dl', pr'⟩, FinishStep.paired hdl hpr⟩

theorem accept_checked_realizes
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (ha : Assumptions th) {s} (hr : Reachable th s)
    (n : node) (m : packet) (s') (ht : AcceptStep th n m s s') :
    s'.delivery.checked (th.delivery.packetObject m) (s.delivery.current n) = true ∧
      th.delivery.valid (th.delivery.packetObject m) = true ∧
      th.delivery.realizes (th.delivery.packetObject m) (s.delivery.current n) = true := by
  have hd := ht.delivery_transition th n m s s'
  have he := (ParaleanDelivery.accept_effect th.delivery s.delivery s'.delivery n m hd).1
  have hs := reachable_safe th ha (Reachable.step hr (ht.to_next th n m s s'))
  exact ⟨he, hs.1.1 _ _ he⟩

theorem AcceptProtocol.enabled_iff
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) (g : group)
    (s : ParaleanGroupComposition.State node group name snapshot replica (StoredObject group snapshot) writeQuorum readQuorum) :
    (∃ s', AcceptProtocol th n g s s') ↔
      s.registry.known n g = true ∨
      (s.registry.alive n = true ∧ s.registry.online n = true ∧
       s.registry.published g = true ∧ ¬s.registry.known n g = true) := by
  constructor
  · rintro ⟨s', ht⟩
    cases ht with
    | @receive rg rg' disk hr =>
      apply Or.inr
      apply (ParaleanGroups.receive_enabled_iff th.registry rg n g).1
      refine ⟨rg', ?_⟩
      simpa only [ParaleanGroups.GroupsNext, ParaleanGroups.Next, ParaleanGroups.NextAct,
        ParaleanGroups.receive.ext.derived_eq] using hr
    | duplicate hk => exact Or.inl hk
  · intro h
    rcases h with hk | he
    · exact ⟨s, AcceptProtocol.duplicate hk⟩
    · obtain ⟨rg', ht⟩ := (ParaleanGroups.receive_enabled_iff th.registry s.registry n g).2 he
      have htr : ParaleanGroups.GroupsNext th.registry s.registry (.receive n g) rg' := by
        simpa only [ParaleanGroups.GroupsNext, ParaleanGroups.Next, ParaleanGroups.NextAct,
          ParaleanGroups.receive.ext.derived_eq] using ht
      cases s
      exact ⟨⟨rg', _⟩, AcceptProtocol.receive htr⟩

theorem accept_enabled_iff
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (s : State node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) (m : packet) :
    (∃ s', AcceptStep th n m s s') ↔
      ParaleanDelivery.Admissible th.delivery s.delivery n m ∧
      (s.protocol.registry.known n (th.delivery.packetObject m) = true ∨
       (s.protocol.registry.alive n = true ∧ s.protocol.registry.online n = true ∧
        s.protocol.registry.published (th.delivery.packetObject m) = true ∧
        ¬s.protocol.registry.known n (th.delivery.packetObject m) = true)) := by
  constructor
  · rintro ⟨s', ht⟩
    have hd := ParaleanDelivery.accept_guarded th.delivery s.delivery s'.delivery n m
      (ht.delivery_transition th n m s s')
    have hp : ∃ pr', AcceptProtocol th n (th.delivery.packetObject m) s.protocol pr' := by
      cases ht with
      | paired _ hp => exact ⟨_, hp⟩
    exact ⟨hd, (AcceptProtocol.enabled_iff th n _ s.protocol).1 hp⟩
  · rintro ⟨hd, hp⟩
    obtain ⟨dl', hdl⟩ := (ParaleanDelivery.accept_enabled_iff th.delivery s.delivery n m).2 hd
    obtain ⟨pr', hpr⟩ := (AcceptProtocol.enabled_iff th n _ s.protocol).2 hp
    cases s
    exact ⟨⟨dl', pr'⟩, AcceptStep.paired hdl hpr⟩

theorem payload_mapping_injective
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum) (g h : group) :
    (protocolTheory th).payload g = (protocolTheory th).payload h ↔ g = h := by
  constructor
  · intro heq
    exact ParaleanArtifacts.payload_injective heq
  · intro h; rw [h]

theorem payload_manifest_distinct
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum) (g : group) (S : snapshot) :
    (protocolTheory th).payload g ≠ (protocolTheory th).manifest S :=
  ParaleanArtifacts.kinds_disjoint g S

inductive CrashStep (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) :
    State node group name snapshot request packet replica writeQuorum readQuorum →
    State node group name snapshot request packet replica writeQuorum readQuorum → Prop where
  | paired {dl dl' rg rg' disk} : ParaleanDelivery.Step th.delivery dl (.cancel n) dl' →
      ParaleanGroups.GroupsNext th.registry rg (.crash n) rg' →
      CrashStep th n ⟨dl, ⟨rg, disk⟩⟩ ⟨dl', ⟨rg', disk⟩⟩

theorem CrashStep.to_next
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) (s s') (ht : CrashStep th n s s') : Next th s s' := by
  cases ht with
  | paired hd hp => exact .crash n hd hp

theorem CrashStep.cancel_transition
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) (s s') (ht : CrashStep th n s s') :
    ParaleanDelivery.Step th.delivery s.delivery (.cancel n) s'.delivery := by
  cases ht with
  | paired hd _ => exact hd

theorem crash_epoch
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) (s s') (ht : CrashStep th n s s') : s'.delivery.epoch n = s.delivery.epoch n + 1 := by
  have hd := ht.cancel_transition th n s s'
  simp only [ParaleanDelivery.Step, ParaleanDelivery.Next, ParaleanDelivery.NextAct,
    ParaleanDelivery.cancel.ext.derived_eq] at hd
  dsimp [ParaleanDelivery.cancel.ext.tr, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanDelivery.canonicalFieldRep, Veil.canonicalFieldRepresentation] at hd
  cases s with
  | mk dl pr =>
    cases s' with
    | mk dl' pr' =>
      dsimp at hd ⊢
      subst dl'
      simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
        Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
        Veil.IteratedProd.patCmp]

theorem crash_rejects_old_response
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) (m : packet) (s s' s'') (ht : CrashStep th n s s')
    (old : th.delivery.packetEpoch m = s.delivery.epoch n) : ¬AcceptStep th n m s' s'' := by
  apply stale_rejected th n m s' s''
  rw [old, crash_epoch th n s s' ht]
  exact Nat.ne_of_lt (Nat.lt_succ_self _)

theorem finish_all_groups_durable
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (ha : Assumptions th) {s} (hr : Reachable th s)
    (n : node) (S : snapshot) (s') (ht : FinishStep th n S s s') :
    ∀ g, th.registry.contents S g = true →
      s'.protocol.registry.published g = true ∧
      s'.protocol.storage.acknowledged (.payload g) = true ∧
      ∃ r, s'.protocol.storage.live r = true ∧ s'.protocol.storage.stored r (.payload g) = true := by
  have hnext := ht.to_next th n S s s'
  have hr' := Reachable.step hr hnext
  have hs := reachable_safe th ha hr'
  have hf := ParaleanGroupComposition.commit_fresh (protocolTheory th) n S s.protocol s'.protocol
    (ht.protocol_transition th n S s s')
  intro g hg
  have hcontents : th.registry.contents (s'.protocol.registry.head n) g = true := by
    rw [hf.2.1]
    exact hg
  have hp := hs.2.1.2.2.2.2.2.1 n g hcontents
  exact ⟨hp, hs.2.2.2.1 g hp, ParaleanGroupComposition.published_has_copy (protocolTheory th)
    ha.2.1 (reachable_protocol_projection th hr') g hp⟩

theorem finish_required_targets_durable
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (ha : Assumptions th) {s} (hr : Reachable th s)
    (n : node) (S : snapshot) (s') (ht : FinishStep th n S s s') :
    ∀ r, th.delivery.required r = true →
      ∃ g, th.registry.contents S g = true ∧ s'.delivery.checked g r = true ∧
      th.delivery.realizes g r = true ∧
      s'.protocol.registry.published g = true ∧
      s'.protocol.storage.acknowledged (.payload g) = true ∧
      ∃ replica, s'.protocol.storage.live replica = true ∧
        s'.protocol.storage.stored replica (.payload g) = true := by
  intro r hn
  obtain ⟨g, hc, hchecked, hrealizes⟩ := finish_required_groups th ha hr n S s' ht r hn
  have hd := finish_all_groups_durable th ha hr n S s' ht g hc
  exact ⟨g, hc, hchecked, hrealizes, hd⟩

theorem empty_cannot_finish
    (th : Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (n : node) (S : snapshot) (s s') (r : request)
    (empty : ∀ g, th.delivery.contents S g = false) (needed : th.delivery.required r = true) :
    ¬FinishStep th n S s s' := by
  intro ht
  exact ParaleanDelivery.empty_cannot_complete th.delivery s.delivery s'.delivery n S empty r needed
    (ht.delivery_transition th n S s s')

end Events
end ParaleanAdmission

#print axioms ParaleanAdmission.initial_safe
#print axioms ParaleanAdmission.next_safe
#print axioms ParaleanAdmission.reachable_safe
#print axioms ParaleanAdmission.reachable_protocol_projection
#print axioms ParaleanAdmission.accept_published_durable
#print axioms ParaleanAdmission.finish_complete_current_durable
#print axioms ParaleanAdmission.finish_required_groups
#print axioms ParaleanAdmission.finish_enabled_iff
#print axioms ParaleanAdmission.corrupt_rejected
#print axioms ParaleanAdmission.stale_rejected
#print axioms ParaleanAdmission.accept_checked_realizes
#print axioms ParaleanAdmission.AcceptProtocol.enabled_iff
#print axioms ParaleanAdmission.accept_enabled_iff
#print axioms ParaleanAdmission.payload_mapping_injective
#print axioms ParaleanAdmission.payload_manifest_distinct
#print axioms ParaleanAdmission.PassiveProtocol.to_next
#print axioms ParaleanAdmission.crash_epoch
#print axioms ParaleanAdmission.crash_rejects_old_response
#print axioms ParaleanAdmission.finish_all_groups_durable
#print axioms ParaleanAdmission.finish_required_targets_durable
#print axioms ParaleanAdmission.empty_cannot_finish
