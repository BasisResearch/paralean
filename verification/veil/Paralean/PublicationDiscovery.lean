import Paralean.Delivery

/-! Durable publication discovery. Object roles are disjoint by construction.
`stored` retains Durability's stable, validated-byte contract. Enumeration must
return every publication-marker object on the queried live replicas, decode its
exact immutable group ID, and reject malformed bytes. These are implementation
refinement interfaces, not assumptions about protocol outcomes.

Marker bytes alone are candidates, not proof of successful publication. The
publication operation atomically commits the marker quorum acknowledgement and
the generated group publication. This acknowledgement certificate is the trusted
storage interface for distinguishing committed markers from interrupted staging.
-/
set_option linter.unusedSectionVars false

namespace ParaleanPublicationDiscovery

abbrev Object := ParaleanArtifacts.Object
namespace Object
abbrev payload := @ParaleanArtifacts.Object.payload
abbrev manifest := @ParaleanArtifacts.Object.manifest
abbrev publication := @ParaleanArtifacts.Object.publication
end Object

abbrev Theory (node group name snapshot replica writeQuorum readQuorum : Type) :=
  ParaleanGroupComposition.Theory node group name snapshot replica
    (Object group snapshot) writeQuorum readQuorum
abbrev State (node group name snapshot replica writeQuorum readQuorum : Type) :=
  ParaleanGroupComposition.State node group name snapshot replica
    (Object group snapshot) writeQuorum readQuorum

noncomputable section
variable {node group name snapshot replica writeQuorum readQuorum : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]
  [DecidableEq replica] [Inhabited replica]
  [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum]
attribute [local instance] Classical.propDecidable

abbrev Disk := ParaleanGroupComposition.DiskState replica (Object group snapshot)
  writeQuorum readQuorum

def Roles (th : Theory node group name snapshot replica writeQuorum readQuorum) : Prop :=
  (∀ d, th.payload d = .payload d) ∧ (∀ S, th.manifest S = .manifest S)

def Coupled (s : State node group name snapshot replica writeQuorum readQuorum) : Prop :=
  ∀ d, s.storage.acknowledged (.publication d) = true ↔ s.registry.published d = true

def Safe (th : Theory node group name snapshot replica writeQuorum readQuorum)
    (s : State node group name snapshot replica writeQuorum readQuorum) : Prop :=
  ParaleanGroupComposition.Safe th s ∧ Coupled s

/-- Exact physical enumeration includes staged records. Acceptance is separate. -/
def PhysicalScan (th : Theory node group name snapshot replica writeQuorum readQuorum)
    (disk : Disk (replica := replica) (group := group) (snapshot := snapshot)
      (writeQuorum := writeQuorum) (readQuorum := readQuorum))
    (q : readQuorum) (ids : group → Prop) : Prop :=
  ∀ d, ids d ↔ ∃ r, th.storage.memberR r q = true ∧ disk.live r = true ∧
    disk.stored r (.publication d) = true

def Accepted (s : State node group name snapshot replica writeQuorum readQuorum)
    (ids : group → Prop) (d : group) : Prop :=
  ids d ∧ s.storage.acknowledged (.publication d) = true

/-- The only marker acknowledgement is the successful atomic publish. -/
def StorageGuard : Durability.Label replica (Object group snapshot) writeQuorum readQuorum → Prop
  | .Ack (.publication _) _ => False
  | _ => True

inductive Next (th : Theory node group name snapshot replica writeQuorum readQuorum) :
    State node group name snapshot replica writeQuorum readQuorum →
    State node group name snapshot replica writeQuorum readQuorum → Prop where
  | publish {rg rg' disk disk'} (n : node) (d : group) (w : writeQuorum) :
      ParaleanGroups.GroupsNext th.registry rg (.publish n d) rg' →
      ParaleanGroupComposition.StorageNext th.storage disk (.Ack (.publication d) w) disk' →
      disk.acknowledged (th.payload d) = true →
      Next th ⟨rg, disk⟩ ⟨rg', disk'⟩
  | registry {rg rg' disk} (l : ParaleanGroups.Label node group name snapshot) :
      (∀ n d, l ≠ .publish n d) →
      ParaleanGroups.GroupsNext th.registry rg l rg' →
      ParaleanGroupComposition.Guard th disk l →
      (∀ n d, l = .receive n d → ∃ q ids, PhysicalScan th disk q ids ∧
        ids d ∧ disk.acknowledged (.publication d) = true) →
      Next th ⟨rg, disk⟩ ⟨rg', disk⟩
  | storage {rg disk disk'} (l : Durability.Label replica (Object group snapshot) writeQuorum readQuorum) :
      StorageGuard l → ParaleanGroupComposition.StorageNext th.storage disk l disk' →
      Next th ⟨rg, disk⟩ ⟨rg, disk'⟩
  | stutter {s} : Next th s s

theorem next_registry_projection
    (th : Theory node group name snapshot replica writeQuorum readQuorum)
    {s s' : State node group name snapshot replica writeQuorum readQuorum}
    (h : Next th s s') : s'.registry = s.registry ∨
      ∃ l, ParaleanGroups.GroupsNext th.registry s.registry l s'.registry := by
  cases h with
  | publish n d _ ht _ _ => exact Or.inr ⟨.publish n d, ht⟩
  | registry l _ ht _ _ => exact Or.inr ⟨l, ht⟩
  | storage => exact Or.inl rfl
  | stutter => exact Or.inl rfl

/-- Each extended step projects to one or two actual generated base steps. -/
theorem next_base_safe (th : Theory node group name snapshot replica writeQuorum readQuorum)
    (ha : ParaleanGroupComposition.Assumptions th)
    (s s' : State node group name snapshot replica writeQuorum readQuorum)
    (hs : ParaleanGroupComposition.Safe th s) (h : Next th s s') :
    ParaleanGroupComposition.Safe th s' := by
  cases h with
  | publish n d w hp ha' hd =>
    have hmid := ParaleanGroupComposition.next_safe th ha _ _ hs
      (.registry (.publish n d) hp hd)
    exact ParaleanGroupComposition.next_safe th ha _ _ hmid
      (.storage (.Ack (.publication d) w) ha')
  | registry l _ ht hg _ => exact ParaleanGroupComposition.next_safe th ha _ _ hs (.registry l ht hg)
  | storage l _ ht => exact ParaleanGroupComposition.next_safe th ha _ _ hs (.storage l ht)
  | stutter => exact hs

private theorem ack_marker (th : Theory node group name snapshot replica writeQuorum readQuorum)
    (disk disk' : Disk (replica := replica) (group := group) (snapshot := snapshot)
      (writeQuorum := writeQuorum) (readQuorum := readQuorum))
    (d : group) (w : writeQuorum)
    (h : ParaleanGroupComposition.StorageNext th.storage disk (.Ack (.publication d) w) disk') :
    ∀ e, disk'.acknowledged (.publication e) = true ↔
      e = d ∨ disk.acknowledged (.publication e) = true := by
  simp only [ParaleanGroupComposition.StorageNext, Durability.Next, Durability.NextAct,
    Durability.Ack.ext.derived_eq] at h
  dsimp [Durability.Ack.ext.tr, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanGroupComposition.diskFieldRep, Veil.canonicalFieldRepresentation] at h
  rcases h with ⟨_, rfl⟩
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]
  all_goals grind

private theorem publish_bit (th : Theory node group name snapshot replica writeQuorum readQuorum)
    (rg rg' : ParaleanGroups.CanonicalState node group name snapshot) (n : node) (d : group)
    (h : ParaleanGroups.GroupsNext th.registry rg (.publish n d) rg') :
    ∀ e, rg'.published e = true ↔ e = d ∨ rg.published e = true := by
  simp only [ParaleanGroups.GroupsNext, ParaleanGroups.Next, ParaleanGroups.NextAct,
    ParaleanGroups.publish.ext.derived_eq] at h
  dsimp [ParaleanGroups.publish.ext.tr, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation] at h
  split_ifs at h <;> rcases h with ⟨_, _, _, rfl⟩ <;>
    simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp]
  all_goals grind

private theorem storage_marker_unchanged
    (th : Theory node group name snapshot replica writeQuorum readQuorum)
    (disk disk' : Disk (replica := replica) (group := group) (snapshot := snapshot)
      (writeQuorum := writeQuorum) (readQuorum := readQuorum))
    (l : Durability.Label replica (Object group snapshot) writeQuorum readQuorum)
    (hg : StorageGuard l) (ht : ParaleanGroupComposition.StorageNext th.storage disk l disk') :
    ∀ d, disk'.acknowledged (.publication d) = disk.acknowledged (.publication d) := by
  cases l <;>
    simp only [ParaleanGroupComposition.StorageNext, Durability.Next, Durability.NextAct,
      Durability.Put.ext.derived_eq, Durability.Ack.ext.derived_eq,
      Durability.Lose.ext.derived_eq] at ht
  all_goals
    dsimp [Durability.Put.ext.tr, Durability.Ack.ext.tr, Durability.Lose.ext.tr,
      getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
      instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanGroupComposition.diskFieldRep,
      Veil.canonicalFieldRepresentation] at ht
    repeat' rcases ht with ⟨ha, ht⟩
    try subst disk'
    simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp]
  case Ack o w => cases o <;> simp_all [StorageGuard]

private theorem registry_publication_unchanged
    (th : Theory node group name snapshot replica writeQuorum readQuorum)
    (rg rg' : ParaleanGroups.CanonicalState node group name snapshot)
    (l : ParaleanGroups.Label node group name snapshot)
    (hg : ∀ n d, l ≠ .publish n d)
    (ht : ParaleanGroups.GroupsNext th.registry rg l rg') : rg'.published = rg.published := by
  cases l <;>
    simp only [ParaleanGroups.GroupsNext, ParaleanGroups.Next, ParaleanGroups.NextAct,
      ParaleanGroups.prepare.ext.derived_eq, ParaleanGroups.publish.ext.derived_eq,
      ParaleanGroups.receive.ext.derived_eq, ParaleanGroups.commit.ext.derived_eq,
      ParaleanGroups.crash.ext.derived_eq, ParaleanGroups.recover.ext.derived_eq,
      ParaleanGroups.partition.ext.derived_eq, ParaleanGroups.reconnect.ext.derived_eq,
      ParaleanGroups.heal.ext.derived_eq] at ht
  all_goals
    try exact False.elim (hg _ _ rfl)
  all_goals
    dsimp [ParaleanGroups.prepare.ext.tr, ParaleanGroups.receive.ext.tr,
      ParaleanGroups.commit.ext.tr, ParaleanGroups.crash.ext.tr,
      ParaleanGroups.recover.ext.tr, ParaleanGroups.partition.ext.tr,
      ParaleanGroups.reconnect.ext.tr, ParaleanGroups.heal.ext.tr,
      getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
      instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanGroups.canonicalFieldRep,
      Veil.canonicalFieldRepresentation] at ht
    repeat' rcases ht with ⟨ha, ht⟩
    try subst rg'
    rfl

theorem next_safe (th : Theory node group name snapshot replica writeQuorum readQuorum)
    (ha : ParaleanGroupComposition.Assumptions th)
    (s s' : State node group name snapshot replica writeQuorum readQuorum)
    (hs : Safe th s) (h : Next th s s') : Safe th s' := by
  refine ⟨next_base_safe th ha s s' hs.1 h, ?_⟩
  cases h with
  | publish n d w hp hd _ =>
    intro e
    rw [ack_marker th _ _ d w hd e, publish_bit th _ _ n d hp e, hs.2 e]
  | registry l hg ht _ _ =>
    intro d
    simpa only [registry_publication_unchanged th _ _ l hg ht] using hs.2 d
  | storage l hg ht =>
    intro d
    simpa only [storage_marker_unchanged th _ _ l hg ht d] using hs.2 d
  | stutter => exact hs.2

def Init (th : Theory node group name snapshot replica writeQuorum readQuorum)
    (s : State node group name snapshot replica writeQuorum readQuorum) : Prop :=
  ParaleanGroupComposition.Init th s

theorem initial_safe (th : Theory node group name snapshot replica writeQuorum readQuorum)
    (ha : ParaleanGroupComposition.Assumptions th)
    (s : State node group name snapshot replica writeQuorum readQuorum) (hi : Init th s) :
    Safe th s := by
  refine ⟨ParaleanGroupComposition.initial_safe th ha s hi, ?_⟩
  rcases hi with ⟨hr, hd⟩
  dsimp [ParaleanGroups.GroupsInit, ParaleanGroups.Init,
    ParaleanGroups.initializer.ext.tr, getFrom, setIn, instIsSubStateOfRefl] at hr
  dsimp [ParaleanGroupComposition.StorageInit, Durability.Init,
    Durability.initializer.ext.tr, getFrom, setIn, instIsSubStateOfRefl] at hd
  rcases s with ⟨rg, disk⟩
  dsimp at hr hd
  subst rg
  subst disk
  simp [Coupled, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

inductive Reachable (th : Theory node group name snapshot replica writeQuorum readQuorum) :
    State node group name snapshot replica writeQuorum readQuorum → Prop where
  | initial {s} : Init th s → Reachable th s
  | step {s s'} : Reachable th s → Next th s s' → Reachable th s'

theorem reachable_safe (th : Theory node group name snapshot replica writeQuorum readQuorum)
    (ha : ParaleanGroupComposition.Assumptions th)
    {s : State node group name snapshot replica writeQuorum readQuorum}
    (hr : Reachable th s) : Safe th s := by
  induction hr with
  | initial hi => exact initial_safe th ha _ hi
  | step _ ht ih => exact next_safe th ha _ _ ih ht

theorem reachable_registry_projection
    (th : Theory node group name snapshot replica writeQuorum readQuorum)
    {s : State node group name snapshot replica writeQuorum readQuorum} (hr : Reachable th s) :
    ParaleanGroups.Reachable th.registry s.registry := by
  induction hr with
  | initial hi => exact .initial hi.1
  | step _ ht ih =>
    rcases next_registry_projection th ht with he | ⟨l, hnext⟩
    · exact he.symm ▸ ih
    · exact .step ih hnext

/-- The scan result is computed from physical storage, without published or known. -/
def enumerate (th : Theory node group name snapshot replica writeQuorum readQuorum)
    (disk : Disk (replica := replica) (group := group) (snapshot := snapshot)
      (writeQuorum := writeQuorum) (readQuorum := readQuorum))
    (q : readQuorum) : group → Prop :=
  fun d => ∃ r, th.storage.memberR r q = true ∧ disk.live r = true ∧
    disk.stored r (.publication d) = true

theorem enumerate_physical (th : Theory node group name snapshot replica writeQuorum readQuorum)
    (disk : Disk (replica := replica) (group := group) (snapshot := snapshot)
      (writeQuorum := writeQuorum) (readQuorum := readQuorum)) (q : readQuorum) :
    PhysicalScan th disk q (enumerate th disk q) := fun _ => Iff.rfl

theorem surviving_quorum_coverage
    (th : Theory node group name snapshot replica writeQuorum readQuorum)
    (ha : ParaleanGroupComposition.Assumptions th)
    (s : State node group name snapshot replica writeQuorum readQuorum) (hs : Safe th s)
    (q : readQuorum) (hq : ∀ r, th.storage.memberR r q = true → s.storage.live r = true)
    (ids : group → Prop) (hscan : PhysicalScan th s.storage q ids) :
    ∀ d, s.registry.published d = true → Accepted s ids d := by
  intro d hp
  have hack := (hs.2 d).2 hp
  have hr := ParaleanGroupComposition.acknowledged_recoverable th s.storage ha.2 hs.1.2.1
    (.publication d) q hack hq
  exact ⟨(hscan d).2 ⟨_, (ha.2 (s.storage.witness (.publication d)) q).2, hr⟩, hack⟩

theorem accepted_exact_published
    (th : Theory node group name snapshot replica writeQuorum readQuorum)
    (ha : ParaleanGroupComposition.Assumptions th)
    (s : State node group name snapshot replica writeQuorum readQuorum) (hs : Safe th s)
    (q : readQuorum) (hq : ∀ r, th.storage.memberR r q = true → s.storage.live r = true)
    (ids : group → Prop) (hscan : PhysicalScan th s.storage q ids) :
    ∀ d, Accepted s ids d ↔ s.registry.published d = true := by
  intro d
  exact ⟨fun h => (hs.2 d).1 h.2, surviving_quorum_coverage th ha s hs q hq ids hscan d⟩

theorem staged_unacknowledged_rejected
    (s : State node group name snapshot replica writeQuorum readQuorum)
    (ids : group → Prop) (d : group) (h : s.storage.acknowledged (.publication d) ≠ true) :
    ¬Accepted s ids d := fun accepted => h accepted.2

/-- Every accepted scan entry admits the actual generated receive action.
No peer, remembered ID, worker knowledge, or scheduling premise is required. -/
theorem scan_receive_enabled
    (th : Theory node group name snapshot replica writeQuorum readQuorum)
    (s : State node group name snapshot replica writeQuorum readQuorum) (hs : Safe th s)
    (q : readQuorum) (ids : group → Prop) (hscan : PhysicalScan th s.storage q ids)
    (n : node) (d : group) (hd : Accepted s ids d)
    (ready : s.registry.alive n = true ∧ s.registry.online n = true)
    (missing : s.registry.known n d ≠ true) :
    ∃ rg', ParaleanGroups.ReceiveStep th.registry s.registry rg' n d ∧
      rg'.known n d = true ∧ Next th s ⟨rg', s.storage⟩ := by
  obtain ⟨rg', ht⟩ := (ParaleanGroups.receive_enabled_iff th.registry s.registry n d).2
    ⟨ready.1, ready.2, (hs.2 d).1 hd.2, missing⟩
  refine ⟨rg', ht, ParaleanGroups.receive_adds_known th.registry _ _ n d ht, ?_⟩
  apply Next.registry (.receive n d)
  · intros; simp
  · simpa only [ParaleanGroups.GroupsNext, ParaleanGroups.Next,
      ParaleanGroups.NextAct, ParaleanGroups.receive.ext.derived_eq] using ht
  · trivial
  · intro n' d' he
    cases he
    exact ⟨q, ids, hscan, hd⟩

/-- Losing every worker index does not obstruct reconstruction. -/
theorem all_indexes_erased_rediscovery
    (th : Theory node group name snapshot replica writeQuorum readQuorum)
    (ha : ParaleanGroupComposition.Assumptions th)
    (s : State node group name snapshot replica writeQuorum readQuorum) (hs : Safe th s)
    (q : readQuorum) (hq : ∀ r, th.storage.memberR r q = true → s.storage.live r = true)
    (ids : group → Prop) (hscan : PhysicalScan th s.storage q ids)
    (erased : ∀ n d, s.registry.known n d = false)
    (n : node) (ready : s.registry.alive n = true ∧ s.registry.online n = true)
    (d : group) (hp : s.registry.published d = true) :
    ids d ∧ ∃ rg', ParaleanGroups.ReceiveStep th.registry s.registry rg' n d ∧
      rg'.known n d = true ∧ Next th s ⟨rg', s.storage⟩ := by
  have hd := surviving_quorum_coverage th ha s hs q hq ids hscan d hp
  exact ⟨hd.1, scan_receive_enabled th s hs q ids hscan n d hd ready (by simp [erased n d])⟩

/-- Both exact dependency IDs and all immutable revision ancestors remain
accepted after scanning; discovery cannot substitute a newer group. -/
theorem scan_exact_dependency_closure
    (th : Theory node group name snapshot replica writeQuorum readQuorum)
    (ha : ParaleanGroupComposition.Assumptions th)
    (s : State node group name snapshot replica writeQuorum readQuorum) (hs : Safe th s)
    (q : readQuorum) (hq : ∀ r, th.storage.memberR r q = true → s.storage.live r = true)
    (ids : group → Prop) (hscan : PhysicalScan th s.storage q ids)
    (d e : group) (hd : Accepted s ids d) (dep : th.registry.deps d e = true) :
    Accepted s ids e := by
  apply surviving_quorum_coverage th ha s hs q hq ids hscan e
  exact hs.1.1.2.1 d e ((hs.2 d).1 hd.2) dep

private theorem reachable_base
    (th : Theory node group name snapshot replica writeQuorum readQuorum)
    {s : State node group name snapshot replica writeQuorum readQuorum} (hr : Reachable th s) :
    ParaleanGroupComposition.Reachable th s := by
  induction hr with
  | initial hi => exact .initial hi
  | step _ ht ih =>
    cases ht with
    | publish n d w hp hd hack =>
      exact .step (.step ih (.registry (.publish n d) hp hack))
        (.storage (.Ack (.publication d) w) hd)
    | registry l _ ht hg _ => exact .step ih (.registry l ht hg)
    | storage l _ ht => exact .step ih (.storage l ht)
    | stutter => exact ih

theorem scan_exact_ancestor_closure
    (th : Theory node group name snapshot replica writeQuorum readQuorum)
    (ha : ParaleanGroupComposition.Assumptions th)
    {s : State node group name snapshot replica writeQuorum readQuorum} (hr : Reachable th s)
    (q : readQuorum) (hq : ∀ r, th.storage.memberR r q = true → s.storage.live r = true)
    (ids : group → Prop) (hscan : PhysicalScan th s.storage q ids)
    (d e : group) (hd : Accepted s ids d) (ancestor : th.registry.ancestors d e = true) :
    Accepted s ids e := by
  have hs := reachable_safe th ha hr
  apply surviving_quorum_coverage th ha s hs q hq ids hscan e
  exact ParaleanGroupComposition.published_ancestors_closed ha (reachable_base th hr)
    d e ((hs.2 d).1 hd.2) ancestor

/-- FailureEnvelope supplies a queryable surviving quorum; the scheduler need
not guess an ID or use a live worker as an enumeration source. -/
theorem surviving_scan_exists
    (th : Theory node group name snapshot replica writeQuorum readQuorum)
    (s : State node group name snapshot replica writeQuorum readQuorum) (hs : Safe th s) :
    ∃ q, ∀ r, th.storage.memberR r q = true → s.storage.live r = true := by
  have he := hs.1.2.1.2
  dsimp [Durability.FailureEnvelope, getFrom, readFrom, instIsSubStateOfRefl,
    instIsSubReaderOfRefl, Veil.FieldRepresentation.get,
    ParaleanGroupComposition.diskFieldRep, Veil.canonicalFieldRepresentation] at he
  exact he

structure Trace (th : Theory node group name snapshot replica writeQuorum readQuorum) where
  state : Nat → State node group name snapshot replica writeQuorum readQuorum
  initial : Reachable th (state 0)
  next : ∀ t, Next th (state t) (state (t + 1))

variable {th : Theory node group name snapshot replica writeQuorum readQuorum}

theorem Trace.reachable (tr : Trace th) (t : Nat) : Reachable th (tr.state t) := by
  induction t with
  | zero => exact tr.initial
  | succ t ih => exact .step ih (tr.next t)

def Trace.ScanReceiveFair (tr : Trace th) : Prop :=
  ∀ n d cutoff,
    (∀ t, cutoff ≤ t → (tr.state t).registry.alive n = true ∧
      (tr.state t).registry.online n = true ∧ (tr.state t).registry.known n d ≠ true ∧
      ∃ q ids, PhysicalScan th (tr.state t).storage q ids ∧ Accepted (tr.state t) ids d) →
    ∃ t, cutoff ≤ t ∧ ParaleanGroups.ReceiveStep th.registry
      (tr.state t).registry (tr.state (t + 1)).registry n d

def Trace.toRegistry (tr : Trace th) : ParaleanGroups.Trace th.registry where
  state t := (tr.state t).registry
  initial := reachable_registry_projection th tr.initial
  next t := next_registry_projection th (tr.next t)

/-- Fairness applies to physically enumerated, acknowledged candidates.
Coverage is proved from safety and the failure envelope, not assumed by fairness. -/
theorem Trace.scan_fair_implies_receive_fair
    (tr : Trace th) (ha : ParaleanGroupComposition.Assumptions th)
    (fair : tr.ScanReceiveFair) : tr.toRegistry.ReceiveFair := by
  intro n d cutoff enabled
  apply fair n d cutoff
  intro t ht
  obtain ⟨alive, online, pub, missing⟩ := enabled t ht
  have hs := reachable_safe th ha (tr.reachable t)
  obtain ⟨q, hq⟩ := surviving_scan_exists th (tr.state t) hs
  exact ⟨alive, online, missing, q, enumerate th (tr.state t).storage q,
    enumerate_physical th (tr.state t).storage q,
    surviving_quorum_coverage th ha (tr.state t) hs q hq _
      (enumerate_physical th (tr.state t).storage q) d pub⟩

theorem Trace.eventual_delivery
    (tr : Trace th) (ha : ParaleanGroupComposition.Assumptions th)
    (healFair : tr.toRegistry.HealFair) (fair : tr.ScanReceiveFair)
    (n : node) (d : group) (t : Nat) (hp : (tr.state t).registry.published d = true) :
    ParaleanConvergence.EventuallyAlways (fun t => (tr.state t).registry.known n d = true) :=
  tr.toRegistry.eventual_delivery ha.1 healFair
    (tr.scan_fair_implies_receive_fair ha fair) n d t hp

theorem Trace.index_convergence
    (tr : Trace th) (ha : ParaleanGroupComposition.Assumptions th)
    (healFair : tr.toRegistry.HealFair) (fair : tr.ScanReceiveFair)
    (nodes : List node) (groups : List group)
    (allNodes : ∀ n, n ∈ nodes) (allGroups : ∀ d, d ∈ groups) :
    ParaleanConvergence.EventuallyAlways
      (fun t => ∀ n, (tr.state t).registry.known n = (tr.state t).registry.published) :=
  tr.toRegistry.index_convergence ha.1 healFair
    (tr.scan_fair_implies_receive_fair ha fair) nodes groups allNodes allGroups

#print axioms Trace.scan_fair_implies_receive_fair
#print axioms Trace.eventual_delivery
#print axioms Trace.index_convergence

end

noncomputable section FailureExecution
attribute [local instance] Classical.propDecidable

def failureTheory : Theory Unit Unit Unit Bool Unit Unit Unit where
  registry := ⟨fun _ => true, fun _ _ => false, fun _ _ => false,
    fun _ _ => true, fun _ _ _ => false, fun _ _ => false, fun _ => true, false⟩
  storage := ⟨fun _ _ => true, fun _ _ => true, fun _ _ => ()⟩
  payload := Object.payload
  manifest := Object.manifest

def failureDisk (k : Nat) : ParaleanGroupComposition.DiskState Unit (Object Unit Bool) Unit Unit where
  stored := fun _ o => match o with
    | .payload _ => decide (1 ≤ k)
    | .publication _ => decide (2 ≤ k)
    | _ => false
  live := fun _ => true
  acknowledged := fun o => match o with
    | .payload _ => decide (3 ≤ k)
    | .publication _ => decide (4 ≤ k)
    | _ => false
  witness := fun _ => ()

def failureRegistry (phase : Nat) : ParaleanGroups.CanonicalState Unit Unit Unit Bool where
  published := fun _ => decide (2 ≤ phase)
  known := fun _ _ => decide (phase = 2)
  pending := fun _ _ => decide (phase = 1)
  head := fun _ => false
  alive := fun _ => decide (phase ≠ 3)
  online := fun _ => true
  stable := decide (phase = 4)
  clock := if 2 ≤ phase then 1 else 0
  rank := fun _ => 0

abbrev failureState (phase k : Nat) : State Unit Unit Unit Bool Unit Unit Unit :=
  ⟨failureRegistry phase, failureDisk k⟩

theorem failure_assumptions : ParaleanGroupComposition.Assumptions failureTheory := by
  constructor
  · dsimp [ParaleanGroups.TheoryAssumptions, ParaleanGroups.Assumptions,
      failureTheory, ParaleanGroups.valid_ancestry, ParaleanGroups.empty_contents,
      ParaleanGroups.empty_exportable, readFrom, instIsSubReaderOfRefl]
    simp
  · intros; trivial

theorem failure_initial : Init failureTheory (failureState 0 0) := by
  constructor
  · dsimp [ParaleanGroups.GroupsInit, ParaleanGroups.Init,
      ParaleanGroups.initializer.ext.tr, failureTheory, failureState, failureRegistry,
      getFrom, setIn, readFrom, instIsSubStateOfRefl, instIsSubReaderOfRefl]
    simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp]
  · dsimp [ParaleanGroupComposition.StorageInit, Durability.Init,
      Durability.initializer.ext.tr, failureTheory, failureState, failureDisk,
      getFrom, setIn, readFrom, instIsSubStateOfRefl, instIsSubReaderOfRefl]
    simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp]
    intro o
    cases o <;> simp

private theorem failure_storage_steps :
    ParaleanGroupComposition.StorageNext failureTheory.storage (failureDisk 0)
      (.Put () (.payload ())) (failureDisk 1) ∧
    ParaleanGroupComposition.StorageNext failureTheory.storage (failureDisk 1)
      (.Put () (.publication ())) (failureDisk 2) ∧
    ParaleanGroupComposition.StorageNext failureTheory.storage (failureDisk 2)
      (.Ack (.payload ()) ()) (failureDisk 3) ∧
    ParaleanGroupComposition.StorageNext failureTheory.storage (failureDisk 3)
      (.Ack (.publication ()) ()) (failureDisk 4) := by
  repeat' constructor
  all_goals
    simp only [ParaleanGroupComposition.StorageNext, Durability.Next, Durability.NextAct,
      Durability.Put.ext.derived_eq, Durability.Ack.ext.derived_eq]
    dsimp [Durability.Put.ext.tr, Durability.Ack.ext.tr, failureTheory, failureDisk,
      getFrom, setIn, readFrom, instIsSubStateOfRefl, instIsSubReaderOfRefl,
      Veil.FieldRepresentation.get, ParaleanGroupComposition.diskFieldRep,
      Veil.canonicalFieldRepresentation]
    simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp]
    intro o
    cases o <;> simp [Object.payload, Object.publication]

private theorem failure_registry_steps :
    ParaleanGroups.GroupsNext failureTheory.registry (failureRegistry 0)
      (.prepare () ()) (failureRegistry 1) ∧
    ParaleanGroups.GroupsNext failureTheory.registry (failureRegistry 1)
      (.publish () ()) (failureRegistry 2) ∧
    ParaleanGroups.GroupsNext failureTheory.registry (failureRegistry 2)
      (.crash ()) (failureRegistry 3) ∧
    ParaleanGroups.GroupsNext failureTheory.registry (failureRegistry 3)
      .heal (failureRegistry 4) := by
  repeat' constructor
  all_goals
    simp only [ParaleanGroups.GroupsNext, ParaleanGroups.Next, ParaleanGroups.NextAct,
      ParaleanGroups.prepare.ext.derived_eq, ParaleanGroups.publish.ext.derived_eq,
      ParaleanGroups.crash.ext.derived_eq, ParaleanGroups.heal.ext.derived_eq]
    dsimp [ParaleanGroups.prepare.ext.tr, ParaleanGroups.publish.ext.tr,
      ParaleanGroups.crash.ext.tr, ParaleanGroups.heal.ext.tr, failureTheory, failureRegistry,
      getFrom, setIn, readFrom, instIsSubStateOfRefl, instIsSubReaderOfRefl,
      Veil.FieldRepresentation.get, ParaleanGroups.canonicalFieldRep,
      Veil.canonicalFieldRepresentation]
    simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp]

theorem failure_healed_reachable : Reachable failureTheory (failureState 4 4) := by
  have h0 : Reachable failureTheory (failureState 0 0) := .initial failure_initial
  have h1 : Reachable failureTheory (failureState 0 1) :=
    .step h0 (.storage (.Put () (.payload ())) trivial failure_storage_steps.1)
  have h2 : Reachable failureTheory (failureState 0 2) :=
    .step h1 (.storage (.Put () (.publication ())) trivial failure_storage_steps.2.1)
  have h3 : Reachable failureTheory (failureState 0 3) :=
    .step h2 (.storage (.Ack (.payload ()) ()) trivial failure_storage_steps.2.2.1)
  have h4 : Reachable failureTheory (failureState 1 3) :=
    .step h3 (.registry (.prepare () ()) (by intros; simp) failure_registry_steps.1 trivial
      (by intros; contradiction))
  have h5 : Reachable failureTheory (failureState 2 4) :=
    .step h4 (.publish () () () failure_registry_steps.2.1 failure_storage_steps.2.2.2 rfl)
  have h6 : Reachable failureTheory (failureState 3 4) :=
    .step h5 (.registry (.crash ()) (by intros; simp) failure_registry_steps.2.2.1 trivial
      (by intros; contradiction))
  exact .step h6 (.registry .heal (by intros; simp) failure_registry_steps.2.2.2 trivial
    (by intros; contradiction))

/-- Starts at generated Init, stages bytes, acknowledges the payload, prepares,
atomically publishes its marker, crashes every worker, heals, then scans and
executes generated receive. No remembered ID or live peer supplies discovery. -/
theorem nonempty_failure_rediscovery :
    Reachable failureTheory (failureState 4 4) ∧
    (∀ n d, (failureState 4 4).registry.known n d = false) ∧
    ∃ rg', ParaleanGroups.ReceiveStep failureTheory.registry (failureRegistry 4) rg' () () ∧
      rg'.known () () = true ∧ Next failureTheory (failureState 4 4) ⟨rg', failureDisk 4⟩ := by
  have hs := reachable_safe failureTheory failure_assumptions failure_healed_reachable
  exact ⟨failure_healed_reachable, by intros; rfl,
    (all_indexes_erased_rediscovery failureTheory failure_assumptions (failureState 4 4) hs ()
      (by intros; rfl) (enumerate failureTheory (failureDisk 4) ())
      (enumerate_physical failureTheory (failureDisk 4) ()) (by intros; rfl)
      () ⟨rfl, rfl⟩ () rfl).2⟩

#print axioms failure_healed_reachable
#print axioms nonempty_failure_rediscovery
end FailureExecution

#print axioms next_safe
#print axioms accepted_exact_published
#print axioms staged_unacknowledged_rejected
#print axioms all_indexes_erased_rediscovery
end ParaleanPublicationDiscovery
