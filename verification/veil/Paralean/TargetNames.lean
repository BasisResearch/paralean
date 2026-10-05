import Paralean.Protocol
import Paralean.ProtocolExecution

/-! Alternative proofs of one required target, with fenced ownership epochs.
Each target name has a store record holding its current owning workspace, an
owner epoch and the latest published proof (`head`), all mutable state: the
controller may reassign a name at any time, bumping its epoch. A new pending
group declaring a target name must be prepared by its current owner, must
explicitly revise the head recorded for that name, and is the preparer's only
pending group for it; it records the epoch it was prepared under. Publication
is fenced on that epoch and sets the recorded head in the same step, so a
zombie old owner can never publish after reassignment and a new owner never
needs a complete scan of published proofs. Published target groups then form
a revision chain topped by the recorded head, so a target name never has two
heads. -/
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace ParaleanTargetNames

/-- Ownership state: the store record of each name (current owner, epoch and
latest published proof `head`), and for each pending bit `(n, d)` the epoch of
each name it was prepared under. The recorded epoch is per node because the
same group may be pending at several workspaces. -/
structure Extra (node group name : Type) where
  owner : name → node
  epoch : name → Nat
  preparedEpoch : node → group → name → Nat
  head : name → Option group

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

/-! ## Registry transition facts -/

theorem groups_published_update (th : ParaleanGroups.Theory node group name snapshot)
    (rg rg' : ParaleanGroups.CanonicalState node group name snapshot) (n : node) (d : group)
    (h : ParaleanGroups.GroupsNext th rg (.publish n d) rg') :
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

theorem groups_published_unchanged (th : ParaleanGroups.Theory node group name snapshot)
    (rg rg' : ParaleanGroups.CanonicalState node group name snapshot)
    (l : ParaleanGroups.Label node group name snapshot)
    (hg : ∀ n d, l ≠ .publish n d)
    (ht : ParaleanGroups.GroupsNext th rg l rg') : rg'.published = rg.published := by
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

/-- A group becomes published only by publishing a group that was pending. -/
theorem groups_published_source (th : ParaleanGroups.Theory node group name snapshot)
    (rg rg' : ParaleanGroups.CanonicalState node group name snapshot)
    (l : ParaleanGroups.Label node group name snapshot)
    (ht : ParaleanGroups.GroupsNext th rg l rg') (h : group) (hp : rg'.published h = true) :
    rg.published h = true ∨ ∃ m, rg.pending m h = true := by
  by_cases hl : ∃ n d, l = .publish n d
  · obtain ⟨n, d, rfl⟩ := hl
    have hpend := ((ParaleanGroups.publish_enabled_iff th rg n d).1 ⟨rg', ht⟩).2.2
    rcases (groups_published_update th rg rg' n d ht h).1 hp with he | hold
    · subst he; exact Or.inr ⟨n, hpend⟩
    · exact Or.inl hold
  · have hg : ∀ n d, l ≠ .publish n d := fun n d he => hl ⟨n, d, he⟩
    rw [groups_published_unchanged th rg rg' l hg ht] at hp
    exact Or.inl hp

/-- Preparation changes only the prepared pending bit. -/
theorem groups_prepare_effect (th : ParaleanGroups.Theory node group name snapshot)
    (rg rg' : ParaleanGroups.CanonicalState node group name snapshot) (n : node) (d : group)
    (ht : ParaleanGroups.GroupsNext th rg (.prepare n d) rg') :
    rg'.published = rg.published ∧
      ∀ m h, rg'.pending m h = true ↔ (m = n ∧ h = d) ∨ rg.pending m h = true := by
  refine ⟨groups_published_unchanged th rg rg' _ (by intros; simp) ht, ?_⟩
  simp only [ParaleanGroups.GroupsNext, ParaleanGroups.Next, ParaleanGroups.NextAct,
    ParaleanGroups.prepare.ext.derived_eq] at ht
  dsimp [ParaleanGroups.prepare.ext.tr, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation] at ht
  repeat' rcases ht with ⟨_, ht⟩
  try subst rg'
  intro m h
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]
  grind

theorem groups_init_empty (th : ParaleanGroups.Theory node group name snapshot)
    (rg : ParaleanGroups.CanonicalState node group name snapshot)
    (h : ParaleanGroups.GroupsInit th rg) :
    (∀ d, rg.published d = false) ∧ ∀ n d, rg.pending n d = false := by
  simp only [ParaleanGroups.GroupsInit, ParaleanGroups.Init, ParaleanGroups.initializer.ext.tr] at h
  dsimp [getFrom, setIn, readFrom, Veil.FieldRepresentation.get, instIsSubStateOfRefl,
    instIsSubReaderOfRefl, ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation] at h
  subst h
  refine ⟨fun d => ?_, fun n d => ?_⟩ <;>
    simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp]


/-- Publishing clears the publisher's pending bit. -/
theorem groups_publish_clears (th : ParaleanGroups.Theory node group name snapshot)
    (rg rg' : ParaleanGroups.CanonicalState node group name snapshot) (n : node) (d : group)
    (h : ParaleanGroups.GroupsNext th rg (.publish n d) rg') : rg'.pending n d = false := by
  simp only [ParaleanGroups.GroupsNext, ParaleanGroups.Next, ParaleanGroups.NextAct,
    ParaleanGroups.publish.ext.derived_eq] at h
  dsimp [ParaleanGroups.publish.ext.tr, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation] at h
  split_ifs at h <;> rcases h with ⟨_, _, _, rfl⟩ <;>
    simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp]

/-- Only `prepare n d` newly sets the pending bit `(n, d)`. -/
theorem groups_pending_source (th : ParaleanGroups.Theory node group name snapshot)
    (rg rg' : ParaleanGroups.CanonicalState node group name snapshot)
    (l : ParaleanGroups.Label node group name snapshot)
    (ht : ParaleanGroups.GroupsNext th rg l rg') (m : node) (h : group)
    (hp : rg'.pending m h = true) (hs : rg.pending m h = false) : l = .prepare m h := by
  cases l <;>
    simp only [ParaleanGroups.GroupsNext, ParaleanGroups.Next, ParaleanGroups.NextAct,
      ParaleanGroups.prepare.ext.derived_eq, ParaleanGroups.publish.ext.derived_eq,
      ParaleanGroups.receive.ext.derived_eq, ParaleanGroups.commit.ext.derived_eq,
      ParaleanGroups.crash.ext.derived_eq, ParaleanGroups.recover.ext.derived_eq,
      ParaleanGroups.partition.ext.derived_eq, ParaleanGroups.reconnect.ext.derived_eq,
      ParaleanGroups.heal.ext.derived_eq] at ht
  all_goals
    dsimp [ParaleanGroups.prepare.ext.tr, ParaleanGroups.publish.ext.tr, ParaleanGroups.receive.ext.tr,
      ParaleanGroups.commit.ext.tr, ParaleanGroups.crash.ext.tr,
      ParaleanGroups.recover.ext.tr, ParaleanGroups.partition.ext.tr,
      ParaleanGroups.reconnect.ext.tr, ParaleanGroups.heal.ext.tr,
      getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
      instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanGroups.canonicalFieldRep,
      Veil.canonicalFieldRepresentation] at ht
  all_goals
    try split_ifs at ht
  all_goals
    repeat' rcases ht with ⟨_, ht⟩
    try subst rg'
    simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp] at hp hs ⊢
  all_goals grind

/-! ## Target naming, ownership state and the guard -/

/-- Controller-side naming hypotheses. `targetName` pins each request's declared
name; `pinned` says realizing a required target means declaring its pinned name.
Ownership is not an assumption: it is mutable state in `Extra`. -/
structure TargetAssumptions (a : ATheory) where
  targetName : request → name
  pinned : ∀ o q, a.delivery.realizes o q = true → a.delivery.required q = true →
    a.registry.member o (targetName q) = true

def IsTarget (a : ATheory) (ta : TargetAssumptions a) (x : name) : Prop :=
  ∃ q, a.delivery.required q = true ∧ ta.targetName q = x

local notation "XState" => Extra node group name

/-- The initial ownership state: owner assignment `o`, every epoch `0`, no
recorded head. -/
def initExtra (o : name → node) : XState := ⟨o, fun _ => 0, fun _ _ _ => 0, fun _ => none⟩

/-- Record the current epoch of every name for each newly pending `(n, d)`. -/
def stamp (s t : ModelState) (e : XState) : XState :=
  { e with preparedEpoch := fun n d x =>
      if t.admission.protocol.registry.pending n d = true ∧
          s.admission.protocol.registry.pending n d = false
      then e.epoch x else e.preparedEpoch n d x }

/-- `d` is newly published by the step and declares target name `x`. -/
def NewTarget (a : ATheory) (ta : TargetAssumptions a) (s t : ModelState) (x : name) (d : group) : Prop :=
  IsTarget a ta x ∧ a.registry.member d x = true ∧
    s.admission.protocol.registry.published d = false ∧
    t.admission.protocol.registry.published d = true

/-- The epoch-conditional publication of a target proof also sets the name's
recorded head (one store write). A step publishes at most one group. -/
def advance (a : ATheory) (ta : TargetAssumptions a) (s t : ModelState) (e : XState) : XState :=
  { e with head := fun x =>
      if h : ∃ d, NewTarget a ta s t x d then some (Classical.choose h) else e.head x }

/-- The ownership state after a guarded protocol step. -/
def update (a : ATheory) (ta : TargetAssumptions a) (s t : ModelState) (e : XState) : XState :=
  advance a ta s t (stamp s t e)

/-- Controller reassignment of name `x` to `n`, bumping its epoch. The recorded
head is kept: it is the latest published proof, whoever owns the name. -/
def reassign (e : XState) (x : name) (n : node) : XState :=
  { e with
    owner := fun y => if y = x then n else e.owner y
    epoch := fun y => if y = x then e.epoch x + 1 else e.epoch y }

/-- Preparation check: a newly pending group declaring a target name is prepared
by the name's current owner, revises the head recorded for that name (unless it
is that head), and is the preparer's only pending group for it. It reads the
name's store record, the immutable theory and the preparer's own pending set;
it does not read the global published set. -/
def PrepareOk (a : ATheory) (ta : TargetAssumptions a) (s : ModelState) (e : XState)
    (t : ModelState) : Prop :=
  ∀ n d x, t.admission.protocol.registry.pending n d = true →
    s.admission.protocol.registry.pending n d = false →
    a.registry.member d x = true → IsTarget a ta x →
    n = e.owner x ∧
    (∀ h, e.head x = some h → h ≠ d → a.registry.revisions d h x = true) ∧
    (∀ h, h ≠ d → t.admission.protocol.registry.pending n h = true →
      a.registry.member h x = true → False)

/-- Publication fence: a group newly published from `n`'s pending bit was
prepared there under the current epoch of each target name it declares. -/
def PublishOk (a : ATheory) (ta : TargetAssumptions a) (s : ModelState) (e : XState)
    (t : ModelState) : Prop :=
  ∀ n d x, s.admission.protocol.registry.published d = false →
    t.admission.protocol.registry.published d = true →
    s.admission.protocol.registry.pending n d = true →
    t.admission.protocol.registry.pending n d = false →
    a.registry.member d x = true → IsTarget a ta x →
    e.preparedEpoch n d x = e.epoch x

/-- A protocol step passes the preparation check and the publication fence,
stamps new pending bits and records newly published heads; or the protocol
state is unchanged and the controller reassigns one name. -/
def Guard (a : ATheory) (ta : TargetAssumptions a) (r : RTheory) (encode : record → Nat)
    (s : ModelState) (e : XState) (t : ModelState) (e' : XState) : Prop :=
  (PrepareOk a ta s e t ∧ PublishOk a ta s e t ∧ e' = update a ta s t e) ∨
  (t = s ∧ ∃ x n, e' = reassign e x n)

def Next (a : ATheory) (ta : TargetAssumptions a) (r : RTheory) (encode : record → Nat)
    (p q : ModelState × XState) : Prop :=
  ParaleanProtocol.Next a r encode p.1 q.1 ∧ Guard a ta r encode p.1 p.2 q.1 q.2

/-- Any initial owner and epoch assignment is allowed; no head is recorded. -/
def Initial (a : ATheory) (r : RTheory) (p : ModelState × XState) : Prop :=
  ParaleanCompletionRecovery.Initial a r p.1 ∧ p.2.head = fun _ => none

inductive Reachable (a : ATheory) (ta : TargetAssumptions a) (r : RTheory) (encode : record → Nat) :
    ModelState × XState → Prop where
  | initial {p} : Initial a r p → Reachable a ta r encode p
  | step {p q} : Reachable a ta r encode p → Next a ta r encode p q → Reachable a ta r encode q

theorem protocol_stutter (a : ATheory) (r : RTheory) (encode : record → Nat) (s : ModelState) :
    ParaleanProtocol.Next a r encode s s := by
  cases s with
  | mk ad rec => exact .paired (.admission .stutter rfl) .stutter

theorem stamp_same (s t : ModelState) (e : XState)
    (h : ∀ n d, t.admission.protocol.registry.pending n d = true →
      s.admission.protocol.registry.pending n d = true) : stamp s t e = e := by
  cases e with
  | mk o ep pe hd =>
    simp only [stamp, Extra.mk.injEq, true_and, and_true]
    funext n d x
    rw [if_neg]
    rintro ⟨h1, h2⟩
    rw [h n d h1] at h2
    contradiction

theorem advance_same (a : ATheory) (ta : TargetAssumptions a) (s t : ModelState) (e : XState)
    (h : ∀ d, t.admission.protocol.registry.published d = true →
      s.admission.protocol.registry.published d = true) : advance a ta s t e = e := by
  cases e with
  | mk o ep pe hd =>
    simp only [advance, Extra.mk.injEq, true_and]
    funext x
    rw [dif_neg]
    rintro ⟨d, _, _, h1, h2⟩
    rw [h d h2] at h1
    contradiction

theorem advance_head_none (a : ATheory) (ta : TargetAssumptions a) (s t : ModelState) (e : XState)
    (x : name) (h : ∀ d, ¬NewTarget a ta s t x d) : (advance a ta s t e).head x = e.head x := by
  simp only [advance]
  rw [dif_neg]
  rintro ⟨d, hd⟩
  exact h d hd

theorem advance_head_some (a : ATheory) (ta : TargetAssumptions a) (s t : ModelState) (e : XState)
    (x : name) (d : group) (hd : NewTarget a ta s t x d) (hu : ∀ d', NewTarget a ta s t x d' → d' = d) :
    (advance a ta s t e).head x = some d := by
  have hex : ∃ d, NewTarget a ta s t x d := ⟨d, hd⟩
  simp only [advance, dif_pos hex]
  rw [hu _ (Classical.choose_spec hex)]

/-- The ownership fields are not changed by `advance`; the head is not changed by `stamp`. -/
theorem update_fields (a : ATheory) (ta : TargetAssumptions a) (s t : ModelState) (e : XState) :
    (update a ta s t e).owner = e.owner ∧ (update a ta s t e).epoch = e.epoch ∧
    (update a ta s t e).preparedEpoch = (stamp s t e).preparedEpoch := ⟨rfl, rfl, rfl⟩

theorem update_same (a : ATheory) (ta : TargetAssumptions a) (s t : ModelState) (e : XState)
    (h : ∀ n d, t.admission.protocol.registry.pending n d = true →
      s.admission.protocol.registry.pending n d = true)
    (hp : ∀ d, t.admission.protocol.registry.published d = true →
      s.admission.protocol.registry.published d = true) : update a ta s t e = e := by
  rw [update, stamp_same s t e h, advance_same a ta s t e hp]

/-- `update` as an explicit head assignment `H`. Used to compute concrete traces. -/
theorem update_eq (a : ATheory) (ta : TargetAssumptions a) (s t : ModelState) (e : XState)
    (H : name → Option group)
    (h : ∀ n d, t.admission.protocol.registry.pending n d = true →
      s.admission.protocol.registry.pending n d = true)
    (hH : ∀ x, ((∀ d, ¬NewTarget a ta s t x d) ∧ H x = e.head x) ∨
      ∃ d, NewTarget a ta s t x d ∧ (∀ d', NewTarget a ta s t x d' → d' = d) ∧ H x = some d) :
    update a ta s t e = { e with head := H } := by
  rw [update, stamp_same s t e h]
  cases e with
  | mk o ep pe hd =>
    have : (advance a ta s t ⟨o, ep, pe, hd⟩).head = H := by
      funext x
      rcases hH x with ⟨hn, hx⟩ | ⟨d, hd', hu, hx⟩
      · rw [advance_head_none a ta s t _ x hn, hx]
      · rw [advance_head_some a ta s t _ x d hd' hu, hx]
    simp only [advance, Extra.mk.injEq, true_and] at this ⊢
    exact this

theorem publishOk_initExtra (a : ATheory) (ta : TargetAssumptions a) (s t : ModelState)
    (o : name → node) : PublishOk a ta s (initExtra o) t := by
  intro n d x _ _ _ _ _ _
  rfl

theorem publishOk_of_no_new_published (a : ATheory) (ta : TargetAssumptions a)
    (s t : ModelState) (e : XState)
    (h : ∀ d, t.admission.protocol.registry.published d = true →
      s.admission.protocol.registry.published d = true) : PublishOk a ta s e t := by
  intro n d x hs ht
  rw [h d ht] at hs
  contradiction

/-- A publication fence is trivially met for a pending bit stamped under the
epoch that is still current. -/
theorem publishOk_of_unchanged_epoch (a : ATheory) (ta : TargetAssumptions a) (s t : ModelState)
    (e : XState) (h : ∀ n d x, s.admission.protocol.registry.pending n d = true →
      a.registry.member d x = true → IsTarget a ta x → e.preparedEpoch n d x = e.epoch x) :
    PublishOk a ta s e t :=
  fun n d x _ _ hp _ hm hx => h n d x hp hm hx

theorem guard_stutter (a : ATheory) (ta : TargetAssumptions a) (r : RTheory) (encode : record → Nat)
    (s : ModelState) (e : XState) : Guard a ta r encode s e s e := by
  refine Or.inl ⟨?_, publishOk_of_no_new_published a ta s s e (fun _ h => h),
    (update_same a ta s s e (fun _ _ h => h) (fun _ h => h)).symm⟩
  intro n d x ht hs
  rw [ht] at hs
  contradiction

/-- Steps that create no pending bit and pass the publication fence satisfy the
guard; the ownership state only records newly published heads. -/
theorem guard_of_no_new_pending (a : ATheory) (ta : TargetAssumptions a) (r : RTheory)
    (encode : record → Nat) (s t : ModelState) (e : XState)
    (h : ∀ n d, t.admission.protocol.registry.pending n d = true →
      s.admission.protocol.registry.pending n d = true)
    (hp : PublishOk a ta s e t) : Guard a ta r encode s e t (update a ta s t e) := by
  refine Or.inl ⟨?_, hp, rfl⟩
  intro n d x ht hs
  rw [h n d ht] at hs
  contradiction

/-- Steps that neither create a pending bit nor publish leave the ownership state unchanged. -/
theorem guard_of_quiet (a : ATheory) (ta : TargetAssumptions a) (r : RTheory)
    (encode : record → Nat) (s t : ModelState) (e : XState)
    (h : ∀ n d, t.admission.protocol.registry.pending n d = true →
      s.admission.protocol.registry.pending n d = true)
    (hp : ∀ d, t.admission.protocol.registry.published d = true →
      s.admission.protocol.registry.published d = true) : Guard a ta r encode s e t e := by
  have g := guard_of_no_new_pending a ta r encode s t e h (publishOk_of_no_new_published a ta s t e hp)
  rwa [update_same a ta s t e h hp] at g

/-- `stamp` changes nothing when every recorded epoch is already current. -/
theorem stamp_synced (s t : ModelState) (e : XState)
    (hsync : ∀ n d x, e.preparedEpoch n d x = e.epoch x) : stamp s t e = e := by
  cases e with
  | mk o ep pe hd =>
    simp only [stamp, Extra.mk.injEq, true_and, and_true]
    funext n d x
    have := hsync n d x
    simp only at this
    split <;> simp [this]

/-- A preparation step that publishes nothing, under an ownership state whose
recorded epochs are all current, leaves the ownership state unchanged. -/
theorem guard_of_synced_prepare (a : ATheory) (ta : TargetAssumptions a) (r : RTheory)
    (encode : record → Nat) (s t : ModelState) (e : XState)
    (hsync : ∀ n d x, e.preparedEpoch n d x = e.epoch x)
    (hprep : PrepareOk a ta s e t)
    (hq : ∀ d, t.admission.protocol.registry.published d = true →
      s.admission.protocol.registry.published d = true) : Guard a ta r encode s e t e := by
  refine Or.inl ⟨hprep, publishOk_of_no_new_published a ta s t e hq, ?_⟩
  rw [update, stamp_synced s t e hsync, advance_same a ta s t e hq]

theorem guard_reassign (a : ATheory) (ta : TargetAssumptions a) (r : RTheory) (encode : record → Nat)
    (s : ModelState) (e : XState) (x : name) (n : node) :
    Guard a ta r encode s e s (reassign e x n) :=
  Or.inr ⟨rfl, x, n, rfl⟩

theorem reachable_protocol (a : ATheory) (ta : TargetAssumptions a) (r : RTheory) (encode : record → Nat)
    {p : ModelState × XState} (h : Reachable a ta r encode p) : ParaleanProtocol.Reachable a r encode p.1 := by
  induction h with
  | initial hi => exact .initial hi.1
  | step _ ht ih => exact .step ih ht.1

/-- In the joint protocol, a newly published group was pending at some node
whose pending bit the step cleared. -/
theorem published_source (a : ATheory) (r : RTheory) (encode : record → Nat)
    {s t : ModelState} (ht : ParaleanProtocol.Next a r encode s t) (h : group)
    (hs : s.admission.protocol.registry.published h = false)
    (hp : t.admission.protocol.registry.published h = true) :
    ∃ m, s.admission.protocol.registry.pending m h = true ∧
      t.admission.protocol.registry.pending m h = false := by
  rcases ParaleanPublicationDiscovery.next_registry_projection _ (ht.discovery a r encode) with he | ⟨l, hl⟩
  · rw [he, hs] at hp; contradiction
  · by_cases hlp : ∃ n d, l = .publish n d
    · obtain ⟨n, d, rfl⟩ := hlp
      have hpend := ((ParaleanGroups.publish_enabled_iff a.registry _ n d).1 ⟨_, hl⟩).2.2
      rcases (groups_published_update a.registry _ _ n d hl h).1 hp with he | hold
      · subst he
        exact ⟨n, hpend, groups_publish_clears a.registry _ _ n h hl⟩
      · rw [hs] at hold; contradiction
    · have hg : ∀ n d, l ≠ .publish n d := fun n d he => hlp ⟨n, d, he⟩
      rw [groups_published_unchanged a.registry _ _ l hg hl, hs] at hp
      contradiction

/-- Publication is monotone, a step publishes at most one new group, and a step
that creates a pending bit publishes nothing new. -/
theorem published_step_shape (a : ATheory) (r : RTheory) (encode : record → Nat)
    {s t : ModelState} (ht : ParaleanProtocol.Next a r encode s t) :
    (∀ h, s.admission.protocol.registry.published h = true →
      t.admission.protocol.registry.published h = true) ∧
    (∀ g h, s.admission.protocol.registry.published g = false →
      t.admission.protocol.registry.published g = true →
      s.admission.protocol.registry.published h = false →
      t.admission.protocol.registry.published h = true → g = h) ∧
    (∀ n d, t.admission.protocol.registry.pending n d = true →
      s.admission.protocol.registry.pending n d = false →
      ∀ h, t.admission.protocol.registry.published h = true →
        s.admission.protocol.registry.published h = true) := by
  rcases ParaleanPublicationDiscovery.next_registry_projection _ (ht.discovery a r encode) with he | ⟨l, hl⟩
  · refine ⟨fun h hp => by rw [he]; exact hp, fun g h h1 h2 _ _ => ?_, fun n d h1 h2 => ?_⟩
    · rw [he, h1] at h2; contradiction
    · rw [he, h2] at h1; contradiction
  · by_cases hlp : ∃ n d, l = .publish n d
    · obtain ⟨n, d, rfl⟩ := hlp
      have up := groups_published_update a.registry _ _ n d hl
      refine ⟨fun h hp => (up h).2 (Or.inr hp), fun g h h1 h2 h3 h4 => ?_, fun m e h1 h2 => ?_⟩
      · rcases (up g).1 h2 with rfl | hg
        · rcases (up h).1 h4 with rfl | hh
          · rfl
          · rw [h3] at hh; contradiction
        · rw [h1] at hg; contradiction
      · exact absurd (groups_pending_source a.registry _ _ _ hl m e h1 h2) (by simp)
    · have hg : ∀ n d, l ≠ .publish n d := fun n d he => hlp ⟨n, d, he⟩
      have hu := groups_published_unchanged a.registry _ _ l hg hl
      refine ⟨fun h hp => by rw [hu]; exact hp, fun g h h1 h2 _ _ => ?_, fun _ _ _ _ h hp => by
        rw [hu] at hp; exact hp⟩
      rw [hu, h1] at h2; contradiction

/-! ## Invariant -/

/-- A pending target proof is *current* at `n` if its recorded epoch equals the
name's epoch. Recorded epochs never exceed the current one; every current
pending proof is at the current owner, revises the recorded head of its name
and is the owner's only current pending proof of it. The recorded head is a
published proof of the name, and every published proof of the name is the head
or is revised by it. Published target proofs form a chain. -/
def Inv (a : ATheory) (ta : TargetAssumptions a) (s : ModelState) (e : XState) : Prop :=
  (∀ n d x, s.admission.protocol.registry.pending n d = true → a.registry.member d x = true →
    IsTarget a ta x → e.preparedEpoch n d x ≤ e.epoch x) ∧
  (∀ n d x, s.admission.protocol.registry.pending n d = true → a.registry.member d x = true →
    IsTarget a ta x → e.preparedEpoch n d x = e.epoch x →
    n = e.owner x ∧
    (∀ h, e.head x = some h → h ≠ d → a.registry.revisions d h x = true) ∧
    (∀ h, h ≠ d → s.admission.protocol.registry.pending n h = true →
      a.registry.member h x = true → e.preparedEpoch n h x = e.epoch x → False)) ∧
  (∀ x h, IsTarget a ta x → e.head x = some h →
    s.admission.protocol.registry.published h = true ∧ a.registry.member h x = true) ∧
  (∀ x g, IsTarget a ta x → s.admission.protocol.registry.published g = true →
    a.registry.member g x = true →
    ∃ h, e.head x = some h ∧ (g = h ∨ a.registry.revisions h g x = true)) ∧
  (∀ g h x, IsTarget a ta x →
    s.admission.protocol.registry.published g = true →
    s.admission.protocol.registry.published h = true →
    a.registry.member g x = true → a.registry.member h x = true →
    g = h ∨ a.registry.revisions g h x = true ∨ a.registry.revisions h g x = true)

theorem initial_inv (a : ATheory) (ta : TargetAssumptions a) (r : RTheory)
    {s : ModelState} (e : XState) (hi : ParaleanCompletionRecovery.Initial a r s)
    (he : e.head = fun _ => none) : Inv a ta s e := by
  obtain ⟨hpub, hpend⟩ := groups_init_empty a.registry _ hi.1.2.1
  refine ⟨fun n d x hp => ?_, fun n d x hp => ?_, fun x h _ hh => ?_, fun x g _ hg => ?_,
    fun g h x _ hg => ?_⟩
  · rw [hpend] at hp; contradiction
  · rw [hpend] at hp; contradiction
  · rw [he] at hh; contradiction
  · rw [hpub] at hg; contradiction
  · rw [hpub] at hg; contradiction

theorem stamp_old {s t : ModelState} {e : XState} {n : node} {d : group} (x : name)
    (ht : t.admission.protocol.registry.pending n d = true)
    (hnew : ¬s.admission.protocol.registry.pending n d = false) :
    (stamp s t e).preparedEpoch n d x = e.preparedEpoch n d x := by
  simp [stamp, hnew]

theorem stamp_new {s t : ModelState} {e : XState} {n : node} {d : group} (x : name)
    (ht : t.admission.protocol.registry.pending n d = true)
    (hnew : s.admission.protocol.registry.pending n d = false) :
    (stamp s t e).preparedEpoch n d x = e.epoch x := by
  simp [stamp, ht, hnew]

/-- Preservation by a guarded protocol step (not a reassignment). Pending groups
are valid, and validity makes revision transitive (`valid_ancestry`). -/
theorem step_inv (a : ATheory) (ta : TargetAssumptions a) (r : RTheory) (encode : record → Nat)
    (hga : ParaleanGroups.TheoryAssumptions a.registry)
    {s t : ModelState} {e : XState}
    (hreg : ParaleanGroups.Reachable a.registry s.admission.protocol.registry)
    (hs : Inv a ta s e) (ht : ParaleanProtocol.Next a r encode s t)
    (hprep : PrepareOk a ta s e t) (hpub : PublishOk a ta s e t) : Inv a ta t (update a ta s t e) := by
  obtain ⟨hle, hcur, hhd, hcov, hchain⟩ := hs
  obtain ⟨mono, uniqPub, prepQuiet⟩ := published_step_shape a r encode ht
  have src := published_source a r encode ht
  have oldp : ∀ n d, t.admission.protocol.registry.pending n d = true →
      ¬s.admission.protocol.registry.pending n d = false →
      s.admission.protocol.registry.pending n d = true := fun n d _ h => by simpa using h
  have pendValid : ∀ n d, s.admission.protocol.registry.pending n d = true → a.registry.valid d = true :=
    fun n d hp => ((ParaleanGroups.reachable_safe a.registry hga hreg).2.2.2.1 n d hp).1
  have trans : ∀ g h k x, a.registry.valid g = true → a.registry.revisions g h x = true →
      a.registry.revisions h k x = true → a.registry.revisions g k x = true :=
    fun g h k x hv h1 h2 => (hga.1.2.1 g h x hv h1).2.2 k h2
  -- a newly published target proof was current at the owner before the step
  have pubcur : ∀ g x, IsTarget a ta x → a.registry.member g x = true →
      s.admission.protocol.registry.published g = false →
      t.admission.protocol.registry.published g = true →
      ∃ m, s.admission.protocol.registry.pending m g = true ∧
        e.preparedEpoch m g x = e.epoch x := by
    intro g x hx hm hs' ht'
    obtain ⟨m, h1, h2⟩ := src g hs' ht'
    exact ⟨m, h1, hpub m g x hs' ht' h1 h2 hm hx⟩
  -- a newly published target proof revises every previously published proof of its name
  have newrev : ∀ d x, IsTarget a ta x → a.registry.member d x = true →
      s.admission.protocol.registry.published d = false →
      t.admission.protocol.registry.published d = true →
      ∀ g, s.admission.protocol.registry.published g = true → a.registry.member g x = true →
        a.registry.revisions d g x = true := by
    intro d x hx hm hs' ht' g hg hmg
    obtain ⟨m, hm1, hm2⟩ := pubcur d x hx hm hs' ht'
    obtain ⟨_, rev, _⟩ := hcur m d x hm1 hm hx hm2
    obtain ⟨h, hh, hgh⟩ := hcov x g hx hg hmg
    have hpubh := (hhd x h hx hh).1
    have hne : h ≠ d := by rintro rfl; rw [hpubh] at hs'; contradiction
    have rdh := rev h hh hne
    rcases hgh with rfl | rhg
    · exact rdh
    · exact trans d h g x (pendValid m d hm1) rdh rhg
  have uniqNew : ∀ x d d', NewTarget a ta s t x d → NewTarget a ta s t x d' → d' = d :=
    fun x d d' h1 h2 => uniqPub d' d h2.2.2.1 h2.2.2.2 h1.2.2.1 h1.2.2.2
  -- the recorded head after the step
  have headCase : ∀ x, ((∀ d, ¬NewTarget a ta s t x d) ∧
        (update a ta s t e).head x = e.head x) ∨
      ∃ d, NewTarget a ta s t x d ∧ (update a ta s t e).head x = some d := by
    intro x
    by_cases hx : ∃ d, NewTarget a ta s t x d
    · obtain ⟨d, hd⟩ := hx
      exact Or.inr ⟨d, hd, advance_head_some a ta s t _ x d hd (fun d' h' => uniqNew x d d' hd h')⟩
    · exact Or.inl ⟨fun d hd => hx ⟨d, hd⟩, advance_head_none a ta s t _ x (fun d hd => hx ⟨d, hd⟩)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n d x hp hm hx
    show (stamp s t e).preparedEpoch n d x ≤ e.epoch x
    by_cases hnew : s.admission.protocol.registry.pending n d = false
    · rw [stamp_new x hp hnew]; exact Nat.le_refl _
    · rw [stamp_old x hp hnew]; exact hle n d x (oldp n d hp hnew) hm hx
  · intro n d x hp hm hx hc
    change (stamp s t e).preparedEpoch n d x = e.epoch x at hc
    change n = e.owner x ∧
      (∀ h, (update a ta s t e).head x = some h → h ≠ d → a.registry.revisions d h x = true) ∧
      (∀ h, h ≠ d → t.admission.protocol.registry.pending n h = true →
        a.registry.member h x = true → (stamp s t e).preparedEpoch n h x = e.epoch x → False)
    by_cases hnew : s.admission.protocol.registry.pending n d = false
    · obtain ⟨o, rev, uniq⟩ := hprep n d x hp hnew hm hx
      refine ⟨o, ?_, fun h hne hph hmh _ => uniq h hne hph hmh⟩
      rcases headCase x with ⟨_, hh⟩ | ⟨d', hd', _⟩
      · rw [hh]; exact rev
      · exact absurd (prepQuiet n d hp hnew d' hd'.2.2.2) (by rw [hd'.2.2.1]; simp)
    · rw [stamp_old x hp hnew] at hc
      have hsp := oldp n d hp hnew
      obtain ⟨o, rev, uniq⟩ := hcur n d x hsp hm hx hc
      refine ⟨o, ?_, ?_⟩
      · rcases headCase x with ⟨_, hh⟩ | ⟨d', hd', hh⟩
        · rw [hh]; exact rev
        · intro h hh' hne
          rw [hh] at hh'
          cases hh'
          obtain ⟨m, hm1, hm2⟩ := pubcur d' x hx hd'.2.1 hd'.2.2.1 hd'.2.2.2
          obtain ⟨o', _, _⟩ := hcur m d' x hm1 hd'.2.1 hx hm2
          have hmn : m = n := o'.trans o.symm
          subst hmn
          exact (uniq d' hne hm1 hd'.2.1 hm2).elim
      · intro h hne hph hmh hch
        by_cases hnew' : s.admission.protocol.registry.pending n h = false
        · exact (hprep n h x hph hnew' hmh hx).2.2 d (Ne.symm hne) hp hm
        · rw [stamp_old x hph hnew'] at hch
          exact uniq h hne (oldp n h hph hnew') hmh hch
  · intro x h hx hh
    rcases headCase x with ⟨_, he⟩ | ⟨d', hd', he⟩
    · rw [he] at hh
      obtain ⟨p, m⟩ := hhd x h hx hh
      exact ⟨mono h p, m⟩
    · rw [he] at hh
      cases hh
      exact ⟨hd'.2.2.2, hd'.2.1⟩
  · intro x g hx hg hmg
    rcases headCase x with ⟨hn, he⟩ | ⟨d', hd', he⟩
    · rw [he]
      by_cases og : s.admission.protocol.registry.published g = true
      · exact hcov x g hx og hmg
      · exact (hn g ⟨hx, hmg, by simpa using og, hg⟩).elim
    · refine ⟨d', he, ?_⟩
      by_cases og : s.admission.protocol.registry.published g = true
      · exact Or.inr (newrev d' x hx hd'.2.1 hd'.2.2.1 hd'.2.2.2 g og hmg)
      · exact Or.inl (uniqNew x d' g hd' ⟨hx, hmg, by simpa using og, hg⟩)
  · intro g h x hx hpg hph hmg hmh
    by_cases e' : g = h
    · exact Or.inl e'
    by_cases og : s.admission.protocol.registry.published g = true <;>
      by_cases oh : s.admission.protocol.registry.published h = true
    · exact hchain g h x hx og oh hmg hmh
    · exact Or.inr (Or.inr (newrev h x hx hmh (by simpa using oh) hph g og hmg))
    · exact Or.inr (Or.inl (newrev g x hx hmg (by simpa using og) hpg h oh hmh))
    · exact (e' (uniqPub h g (by simpa using oh) hph (by simpa using og) hpg).symm).elim

/-- Preservation by a reassignment: every pending proof of the reassigned name
becomes stale, the recorded head is kept, and nothing else changes. -/
theorem reassign_inv (a : ATheory) (ta : TargetAssumptions a) {s : ModelState} {e : XState}
    (hs : Inv a ta s e) (y : name) (m : node) : Inv a ta s (reassign e y m) := by
  obtain ⟨hle, hcur, hhd, hcov, hchain⟩ := hs
  refine ⟨?_, ?_, hhd, hcov, hchain⟩
  · intro n d x hp hm hx
    have := hle n d x hp hm hx
    by_cases hxy : x = y
    · subst hxy; simp [reassign]; omega
    · simpa [reassign, hxy] using this
  · intro n d x hp hm hx hc
    by_cases hxy : x = y
    · subst hxy
      have := hle n d x hp hm hx
      simp [reassign] at hc
      omega
    · simp only [reassign, hxy, if_false] at hc ⊢
      exact hcur n d x hp hm hx hc

theorem reachable_inv (a : ATheory) (ta : TargetAssumptions a) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    {p : ModelState × XState} (h : Reachable a ta r encode p) : Inv a ta p.1 p.2 := by
  have hreg : ∀ {q : ModelState × XState}, Reachable a ta r encode q →
      ParaleanGroups.Reachable a.registry q.1.admission.protocol.registry := fun hq =>
    ParaleanPublicationDiscovery.reachable_registry_projection _
      (ParaleanProtocol.reachable_discovery a r encode (reachable_protocol a ta r encode hq))
  induction h with
  | initial hi => exact initial_inv a ta r _ hi.1 hi.2
  | step hp ht ih =>
    rcases ht.2 with ⟨hprep, hpub, he⟩ | ⟨hts, y, m, he⟩
    · rw [he]; exact step_inv a ta r encode ha.2.1.1 (hreg hp) ih ht.1 hprep hpub
    · rw [he, hts]; exact reassign_inv a ta ih y m

/-! ## Headline safety (across arbitrary reassignments) -/

/-- Published groups declaring a target name form a revision chain. -/
theorem target_chain (a : ATheory) (ta : TargetAssumptions a) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    {p : ModelState × XState} (hr : Reachable a ta r encode p) (x : name) (hx : IsTarget a ta x)
    (g h : group) (hg : p.1.admission.protocol.registry.published g = true)
    (hh : p.1.admission.protocol.registry.published h = true)
    (hgx : a.registry.member g x = true) (hhx : a.registry.member h x = true) :
    g = h ∨ a.registry.revisions g h x = true ∨ a.registry.revisions h g x = true :=
  (reachable_inv a ta r encode ha hr).2.2.2.2 g h x hx hg hh hgx hhx

/-- The recorded head of a target name is a published proof of it and tops the
chain: every published proof of the name is the head or is revised by it. -/
theorem recorded_head_tops_chain (a : ATheory) (ta : TargetAssumptions a) (r : RTheory)
    (encode : record → Nat) (ha : ParaleanAdmission.Assumptions a)
    {p : ModelState × XState} (hr : Reachable a ta r encode p) (x : name) (hx : IsTarget a ta x) :
    (∀ h, p.2.head x = some h →
      p.1.admission.protocol.registry.published h = true ∧ a.registry.member h x = true) ∧
    (∀ g, p.1.admission.protocol.registry.published g = true → a.registry.member g x = true →
      ∃ h, p.2.head x = some h ∧ (g = h ∨ a.registry.revisions h g x = true)) :=
  ⟨fun h hh => (reachable_inv a ta r encode ha hr).2.2.1 x h hx hh,
    fun g hg hm => (reachable_inv a ta r encode ha hr).2.2.2.1 x g hx hg hm⟩

/-- Any two published realizations of the same required request are ordered by
revision of its pinned name. -/
theorem realized_chain (a : ATheory) (ta : TargetAssumptions a) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    {p : ModelState × XState} (hr : Reachable a ta r encode p) (q : request)
    (hq : a.delivery.required q = true) (g h : group)
    (hg : p.1.admission.protocol.registry.published g = true)
    (hh : p.1.admission.protocol.registry.published h = true)
    (rg : a.delivery.realizes g q = true) (rh : a.delivery.realizes h q = true) :
    g = h ∨ a.registry.revisions g h (ta.targetName q) = true ∨
      a.registry.revisions h g (ta.targetName q) = true :=
  target_chain a ta r encode ha hr _ ⟨q, hq, rfl⟩ g h hg hh
    (ta.pinned g q rg hq) (ta.pinned h q rh hq)

/-- Every node has at most one registry head for a target name. -/
theorem target_head_unique (a : ATheory) (ta : TargetAssumptions a) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    {p : ModelState × XState} (hr : Reachable a ta r encode p) (n : node) (x : name) (hx : IsTarget a ta x)
    (g h : group)
    (hg : ParaleanGroups.isHead n g x a.registry p.1.admission.protocol.registry)
    (hh : ParaleanGroups.isHead n h x a.registry p.1.admission.protocol.registry) : g = h := by
  have hreg : ParaleanGroups.Reachable a.registry p.1.admission.protocol.registry :=
    ParaleanPublicationDiscovery.reachable_registry_projection _
      (ParaleanProtocol.reachable_discovery a r encode (reachable_protocol a ta r encode hr))
  obtain ⟨hkg, hmg, hng⟩ := hg
  obtain ⟨hkh, hmh, hnh⟩ := hh
  have pg := ParaleanGroups.known_published a.registry ha.2.1.1 hreg n g hkg
  have ph := ParaleanGroups.known_published a.registry ha.2.1.1 hreg n h hkh
  rcases target_chain a ta r encode ha hr x hx g h pg ph hmg hmh with e | rgh | rhg
  · exact e
  · exact (hnh ⟨g, hkg, rgh⟩).elim
  · exact (hng ⟨h, hkh, rhg⟩).elim

/-- The two-head premise of `collision_blocks_current` never holds for a target
name, unlike `ParaleanGroups.Trace.eventual_name_collision`. -/
theorem no_target_collision (a : ATheory) (ta : TargetAssumptions a) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    {p : ModelState × XState} (hr : Reachable a ta r encode p) (n : node) (x : name) (hx : IsTarget a ta x) :
    ¬∃ g h, g ≠ h ∧ ParaleanGroups.isHead n g x a.registry p.1.admission.protocol.registry ∧
      ParaleanGroups.isHead n h x a.registry p.1.admission.protocol.registry := by
  rintro ⟨g, h, hne, hg, hh⟩
  exact hne (target_head_unique a ta r encode ha hr n x hx g h hg hh)

/-- The `unsuperseded` premise of `eventual_name_collision` fails at once for any
two distinct published groups declaring a target name. -/
theorem collision_premise_fails (a : ATheory) (ta : TargetAssumptions a) (r : RTheory) (encode : record → Nat)
    (ha : ParaleanAdmission.Assumptions a)
    {p : ModelState × XState} (hr : Reachable a ta r encode p) (x : name) (hx : IsTarget a ta x)
    (g h : group) (hne : g ≠ h)
    (hg : p.1.admission.protocol.registry.published g = true)
    (hh : p.1.admission.protocol.registry.published h = true)
    (hgx : a.registry.member g x = true) (hhx : a.registry.member h x = true) :
    ∃ e, p.1.admission.protocol.registry.published e = true ∧
      (a.registry.revisions e g x = true ∨ a.registry.revisions e h x = true) := by
  rcases target_chain a ta r encode ha hr x hx g h hg hh hgx hhx with e | rgh | rhg
  · exact (hne e).elim
  · exact ⟨g, hg, Or.inr rgh⟩
  · exact ⟨h, hh, Or.inl rhg⟩

/-- A pending proof prepared under an older epoch of one of its target names
can never be published by its preparer: the fence rejects every such step. -/
theorem stale_publication_blocked (a : ATheory) (ta : TargetAssumptions a) (r : RTheory)
    (encode : record → Nat) (s t : ModelState) (e e' : XState) (n : node) (d : group) (x : name)
    (hm : a.registry.member d x = true) (hx : IsTarget a ta x)
    (hstale : e.preparedEpoch n d x ≠ e.epoch x)
    (hs : s.admission.protocol.registry.published d = false)
    (ht : t.admission.protocol.registry.published d = true)
    (hp : s.admission.protocol.registry.pending n d = true)
    (hc : t.admission.protocol.registry.pending n d = false) :
    ¬Guard a ta r encode s e t e' := by
  rintro (⟨_, hpub, _⟩ | ⟨rfl, _⟩)
  · exact hstale (hpub n d x hs ht hp hc hm hx)
  · rw [hs] at ht; contradiction

/-- A finish step contains an actual registry commit. -/
theorem finish_commits (a : ATheory) (r : RTheory) (n : node) (S : snapshot) (c : record)
    {s t : ModelState} (h : ParaleanCompletionRecovery.FinishStep a r n S c s t) :
    ∃ rg', ParaleanGroups.GroupsNext a.registry s.admission.protocol.registry (.commit n S) rg' := by
  cases h with
  | guarded hA _ _ _ =>
    cases hA with
    | paired _ hp =>
      cases hp with
      | registry hr _ => exact ⟨_, hr⟩

/-! ## Groups declaring several target names -/

/-- Controller constraint: a group declaring target names with different current
owners can never become newly pending under the guard. Targets declared by one
group must therefore be assigned (and reassigned) jointly. -/
theorem split_owner_unpreparable (a : ATheory) (ta : TargetAssumptions a) (r : RTheory)
    (encode : record → Nat) (s t : ModelState) (e e' : XState) (n : node) (d : group) (x y : name)
    (hmx : a.registry.member d x = true) (hx : IsTarget a ta x)
    (hmy : a.registry.member d y = true) (hy : IsTarget a ta y)
    (hxy : e.owner x ≠ e.owner y)
    (ht : t.admission.protocol.registry.pending n d = true)
    (hs : s.admission.protocol.registry.pending n d = false) :
    ¬Guard a ta r encode s e t e' := by
  rintro (⟨hprep, _, _⟩ | ⟨rfl, _⟩)
  · exact hxy ((hprep n d x ht hs hmx hx).1.symm.trans (hprep n d y ht hs hmy hy).1)
  · rw [ht] at hs; contradiction

/-! ## Implementability -/

/-- For a preparation step the guard (with the updated ownership state) is
equivalent to a check of the name's store record (current owner and recorded
head) for each declared target name, the preparer's own pending set and the
immutable theory. No published set, scan or certificate is read: the right-hand
side mentions `s` only through `pending n`. The record read and the preparation
are one atomic step. -/
theorem guard_observable (a : ATheory) (ta : TargetAssumptions a) (r : RTheory) (encode : record → Nat)
    {s : ModelState} (e : XState)
    (n : node) (d : group) (rg' : ParaleanGroups.CanonicalState node group name snapshot)
    (step : ParaleanGroups.GroupsNext a.registry s.admission.protocol.registry (.prepare n d) rg')
    (t : ModelState) (ht : t.admission.protocol.registry = rg') :
    Guard a ta r encode s e t (update a ta s t e) ↔
      (s.admission.protocol.registry.pending n d = false → ∀ x, a.registry.member d x = true →
        IsTarget a ta x →
        n = e.owner x ∧
        (∀ h, e.head x = some h → h ≠ d → a.registry.revisions d h x = true) ∧
        (∀ h, h ≠ d → s.admission.protocol.registry.pending n h = true →
          a.registry.member h x = true → False)) := by
  subst ht
  obtain ⟨hpub, hpend⟩ := groups_prepare_effect a.registry _ _ n d step
  constructor
  · rintro (⟨hg, _, _⟩ | ⟨_, x, m, he⟩)
    · intro hnew x hm hx
      have hp' := (hpend n d).2 (Or.inl ⟨rfl, rfl⟩)
      obtain ⟨o, rev, uniq⟩ := hg n d x hp' hnew hm hx
      exact ⟨o, rev, fun h hne hph hmh => uniq h hne ((hpend n h).2 (Or.inr hph)) hmh⟩
    · have := congrArg (fun e => e.epoch x) he
      simp [update, advance, stamp, reassign] at this
  · intro hl
    refine Or.inl ⟨?_, publishOk_of_no_new_published a ta s t e
      (fun h hp => by rw [hpub] at hp; exact hp), rfl⟩
    intro n' d' x hp' hold hm hx
    rcases (hpend n' d').1 hp' with ⟨rfl, rfl⟩ | hold'
    · obtain ⟨o, rev, uniq⟩ := hl hold x hm hx
      refine ⟨o, rev, fun h hne hph hmh => ?_⟩
      rcases (hpend n' h).1 hph with ⟨_, rfl⟩ | hph'
      · exact hne rfl
      · exact uniq h hne hph' hmh
    · rw [hold'] at hold; contradiction

/-- A group declaring several target names is preparable when they share one
current owner: if the preparer is that owner, the group revises the recorded
head of each declared name and the preparer has no other pending proof of any
of them, the guard admits the preparation step. -/
theorem common_owner_preparable (a : ATheory) (ta : TargetAssumptions a) (r : RTheory)
    (encode : record → Nat) {s : ModelState} (e : XState)
    (n : node) (d : group) (rg' : ParaleanGroups.CanonicalState node group name snapshot)
    (step : ParaleanGroups.GroupsNext a.registry s.admission.protocol.registry (.prepare n d) rg')
    (t : ModelState) (ht : t.admission.protocol.registry = rg')
    (hown : ∀ x, a.registry.member d x = true → IsTarget a ta x → e.owner x = n)
    (hrev : ∀ x, a.registry.member d x = true → IsTarget a ta x →
      ∀ h, e.head x = some h → h ≠ d → a.registry.revisions d h x = true)
    (huniq : ∀ x, a.registry.member d x = true → IsTarget a ta x →
      ∀ h, h ≠ d → s.admission.protocol.registry.pending n h = true →
        a.registry.member h x = false) :
    Guard a ta r encode s e t (update a ta s t e) :=
  (guard_observable a ta r encode e n d rg' step t ht).2
    fun _ x hm hx => ⟨(hown x hm hx).symm, hrev x hm hx,
      fun h hne hph hmh => by rw [huniq x hm hx h hne hph] at hmh; contradiction⟩

/-- The scan-based preparation check this layer replaces: the published set is
replaced by whatever a discovery scan `ids` returned. A certificate scan only
guarantees `CertQuorum ⊆ ids ⊆ published`, so `ids` may miss a published proof
that has no certificate quorum yet. `Example.scan_check_unsafe` shows this check
admits a second, non-revising head. -/
def ScanPrepareOk (a : ATheory) (ta : TargetAssumptions a) (ids : group → Prop)
    (s : ModelState) (e : XState) (t : ModelState) : Prop :=
  ∀ n d x, t.admission.protocol.registry.pending n d = true →
    s.admission.protocol.registry.pending n d = false →
    a.registry.member d x = true → IsTarget a ta x →
    n = e.owner x ∧
    (∀ h, h ≠ d → ids h → a.registry.member h x = true → a.registry.revisions d h x = true) ∧
    (∀ h, h ≠ d → t.admission.protocol.registry.pending n h = true →
      a.registry.member h x = true → False)

end
end ParaleanTargetNames

/-! ## Concrete instance: two proofs of one required target -/
namespace ParaleanTargetNames.Example
noncomputable section
open ParaleanAdmission
open ParaleanCompletionRecovery.Example (storageTheory rg0 rgPreparedHelper rgHelper rgPreparedTarget
  rgPublished rgReceivedHelper rgReceived rgCommitted dl0 disk0 put ack put_step ack_step rec0
  recCommitted encode CState)
open ParaleanProtocol.Example (state d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

abbrev Registry := ParaleanGroups.CanonicalState Bool Bool (Fin 3) Bool
abbrev Delivery := ParaleanDelivery.CanonicalState Bool Bool Bool Bool Bool (Fin 3)
abbrev Disk := ParaleanGroupComposition.DiskState Bool (StoredObject Bool Bool) Unit Unit

/-- Groups `false` and `true` are two proofs of target name `2`. With `rev`,
`true` explicitly revises `false`; without it they are independent. -/
def groupTheory (rev : Bool) : ParaleanGroups.Theory Bool Bool (Fin 3) Bool where
  valid := fun _ => true
  deps := fun _ _ => false
  ancestors := fun g h => rev && g && !h
  member := fun _ x => decide (x = 2)
  revisions := fun g h x => rev && g && !h && decide (x = 2)
  contents := fun S g => S && g
  exportable := fun _ => true
  emptySnapshot := false

/-- Request `true` is the required target; both groups realize it. -/
def deliveryTheory (rev : Bool) : ParaleanDelivery.Theory Bool Bool Bool Bool Bool (Fin 3) where
  packetRequest := fun _ => true
  packetObject := id
  packetEpoch := fun m => if m then 2 else 1
  packetNode := fun _ => true
  receiptRequest := fun _ => true
  receiptObject := id
  receiptEpoch := fun m => if m then 2 else 1
  receiptNode := fun _ => true
  intact := fun _ => true
  verified := fun _ => true
  valid := (groupTheory rev).valid
  realizes := fun _ q => q
  required := id
  deps := (groupTheory rev).deps
  member := (groupTheory rev).member
  contents := (groupTheory rev).contents
  exportable := (groupTheory rev).exportable

def theory (rev : Bool) : Theory Bool Bool (Fin 3) Bool Bool Bool Bool Unit Unit :=
  ⟨deliveryTheory rev, groupTheory rev, storageTheory⟩

def recoveryTheory (rev : Bool) : ParaleanRecovery.Theory Bool Unit Bool Bool (Fin 3) Bool ParaleanCompletionRecovery.Example.Scan where
  tokenRank := fun t => if t then 1 else 0
  identity := ()
  recordWorkspace := fun _ => ()
  image := id
  causalRank := fun _ => 0
  parent := fun _ _ => false
  ancestor := fun _ _ => false
  valid := (groupTheory rev).valid
  deps := (groupTheory rev).deps
  member := (groupTheory rev).member
  contents := (groupTheory rev).contents
  exportable := (groupTheory rev).exportable
  decoded := fun v c => ParaleanCompletionRecovery.Example.scanBit v.1 c
  ready := fun v c => ParaleanCompletionRecovery.Example.scanBit v.2 c

/-- Every request is pinned to name `2`. -/
def targets (rev : Bool) : TargetAssumptions (theory rev) where
  targetName := fun _ => 2
  pinned := by intro o q _ _; simp [theory, groupTheory]

theorem assumptions (rev : Bool) : Assumptions (theory rev) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [DeliveryAssumptions, ParaleanDelivery.Assumptions, ParaleanDelivery.receipt_sound,
      theory, deliveryTheory, groupTheory, readFrom, instIsSubReaderOfRefl]
  · constructor
    · cases rev <;> decide
    · simp [ParaleanGroupComposition.StorageAssumptions, Durability.Assumptions,
        Durability.assumption_0, protocolTheory, theory, storageTheory, readFrom, instIsSubReaderOfRefl]
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def dlS1 : Delivery := { dl0 with current := id, epoch := fun n => if n then 1 else 0, active := id }
def dlF1 : Delivery := { dlS1 with flight := fun m => !m }
def dlA1 : Delivery := { dlS1 with checked := fun g q => !g && q, accepted := id }
def dlS2 : Delivery := { dlA1 with epoch := fun n => if n then 2 else 0, accepted := fun _ => false }
def dlF2 : Delivery := { dlS2 with flight := id }
def dlA2 : Delivery := { dlS2 with checked := fun _ q => q, accepted := id, acceptedObject := id }
def dlD : Delivery := { dlA2 with done := id, result := id }

/-- Independent second proof prepared by worker `true`. -/
def rgN1 : Registry := { rgHelper with pending := fun n g => n && g }
def rgN2 : Registry :=
  { rg0 with
    published := fun _ => true
    known := fun n g => n == g
    clock := 2
    rank := fun g => if g then 1 else 0 }
def rgN3 : Registry := { rgN2 with known := fun n g => n || !g }

theorem group_steps :
    ParaleanGroups.GroupsInit (groupTheory true) rg0 ∧
    ParaleanGroups.GroupsNext (groupTheory true) rg0 (.prepare false false) rgPreparedHelper ∧
    ParaleanGroups.GroupsNext (groupTheory true) rgPreparedHelper (.publish false false) rgHelper ∧
    ParaleanGroups.GroupsNext (groupTheory true) rgHelper (.prepare false true) rgPreparedTarget ∧
    ParaleanGroups.GroupsNext (groupTheory true) rgPreparedTarget (.publish false true) rgPublished ∧
    ParaleanGroups.GroupsNext (groupTheory true) rgPublished (.receive true false) rgReceivedHelper ∧
    ParaleanGroups.GroupsNext (groupTheory true) rgReceivedHelper (.receive true true) rgReceived ∧
    ParaleanGroups.GroupsNext (groupTheory true) rgReceived (.commit true true) rgCommitted := by
  repeat' apply And.intro
  all_goals simp [ParaleanGroups.GroupsInit, ParaleanGroups.Init, ParaleanGroups.initializer.ext.tr,
    ParaleanGroups.GroupsNext, ParaleanGroups.Next, ParaleanGroups.NextAct,
    ParaleanGroups.prepare.ext.derived_eq, ParaleanGroups.publish.ext.derived_eq,
    ParaleanGroups.receive.ext.derived_eq, ParaleanGroups.commit.ext.derived_eq,
    ParaleanGroups.prepare.ext.tr, ParaleanGroups.publish.ext.tr,
    ParaleanGroups.receive.ext.tr, ParaleanGroups.commit.ext.tr,
    ParaleanGroups.buildable, ParaleanGroups.current, ParaleanGroups.isHead,
    groupTheory, rg0, rgPreparedHelper, rgHelper, rgPreparedTarget, rgPublished,
    rgReceivedHelper, rgReceived, rgCommitted, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation,
    Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]

theorem bad_group_steps :
    ParaleanGroups.GroupsInit (groupTheory false) rg0 ∧
    ParaleanGroups.GroupsNext (groupTheory false) rg0 (.prepare false false) rgPreparedHelper ∧
    ParaleanGroups.GroupsNext (groupTheory false) rgPreparedHelper (.publish false false) rgHelper ∧
    ParaleanGroups.GroupsNext (groupTheory false) rgHelper (.prepare true true) rgN1 ∧
    ParaleanGroups.GroupsNext (groupTheory false) rgN1 (.publish true true) rgN2 ∧
    ParaleanGroups.GroupsNext (groupTheory false) rgN2 (.receive true false) rgN3 := by
  repeat' apply And.intro
  all_goals simp [ParaleanGroups.GroupsInit, ParaleanGroups.Init, ParaleanGroups.initializer.ext.tr,
    ParaleanGroups.GroupsNext, ParaleanGroups.Next, ParaleanGroups.NextAct,
    ParaleanGroups.prepare.ext.derived_eq, ParaleanGroups.publish.ext.derived_eq,
    ParaleanGroups.receive.ext.derived_eq,
    ParaleanGroups.prepare.ext.tr, ParaleanGroups.publish.ext.tr,
    ParaleanGroups.receive.ext.tr,
    groupTheory, rg0, rgPreparedHelper, rgHelper, rgN1, rgN2, rgN3, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation,
    Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]

theorem delivery_steps :
    ParaleanDelivery.Initial (deliveryTheory true) dl0 ∧
    ParaleanDelivery.Step (deliveryTheory true) dl0 (.start true true) dlS1 ∧
    ParaleanDelivery.Step (deliveryTheory true) dlS1 (.send false) dlF1 ∧
    ParaleanDelivery.Step (deliveryTheory true) dlF1 (.accept true false) dlA1 ∧
    ParaleanDelivery.Step (deliveryTheory true) dlA1 (.start true true) dlS2 ∧
    ParaleanDelivery.Step (deliveryTheory true) dlS2 (.send true) dlF2 ∧
    ParaleanDelivery.Step (deliveryTheory true) dlF2 (.accept true true) dlA2 ∧
    ParaleanDelivery.Step (deliveryTheory true) dlA2 (.finish true true) dlD := by
  repeat' apply And.intro
  all_goals simp [ParaleanDelivery.Initial, ParaleanDelivery.Init, ParaleanDelivery.initializer.ext.tr,
    ParaleanDelivery.Step, ParaleanDelivery.Next, ParaleanDelivery.NextAct,
    ParaleanDelivery.start.ext.derived_eq, ParaleanDelivery.send.ext.derived_eq,
    ParaleanDelivery.accept.ext.derived_eq, ParaleanDelivery.finish.ext.derived_eq,
    ParaleanDelivery.start.ext.tr, ParaleanDelivery.send.ext.tr,
    ParaleanDelivery.accept.ext.tr, ParaleanDelivery.finish.ext.tr, ParaleanDelivery.ready,
    deliveryTheory, groupTheory, dl0, dlS1, dlF1, dlA1, dlS2, dlF2, dlA2, dlD,
    getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanDelivery.canonicalFieldRep, Veil.canonicalFieldRepresentation,
    Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]

theorem recovery_initial (rev : Bool) : ParaleanRecovery.RecoveryInit (recoveryTheory rev) rec0 := by
  simp [ParaleanRecovery.RecoveryInit, ParaleanRecovery.Init, ParaleanRecovery.initializer.ext.tr,
    rec0, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanRecovery.canonicalFieldRep,
    Veil.canonicalFieldRepresentation, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

theorem recovery_commit : ParaleanRecovery.RecoveryNext (recoveryTheory true) rec0 (.commit true false) recCommitted := by
  simp [ParaleanRecovery.RecoveryNext, ParaleanRecovery.Next, ParaleanRecovery.NextAct,
    ParaleanRecovery.commit.ext.derived_eq, ParaleanRecovery.commit.ext.tr,
    ParaleanRecovery.buildable, recoveryTheory, groupTheory, rec0, recCommitted,
    getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, ParaleanRecovery.canonicalFieldRep,
    Veil.canonicalFieldRepresentation, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]

attribute [local simp] d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18

theorem put_joint (rev : Bool) (dl : Delivery) (rg : Registry) (disk : Disk) (r : Bool)
    (o : StoredObject Bool Bool) (live : disk.live r = true) :
    ParaleanProtocol.Next (theory rev) (recoveryTheory rev) encode (state dl rg disk)
      (state dl rg (put disk r o)) :=
  ParaleanProtocol.storage_step (theory rev) (recoveryTheory rev) encode dl rg rec0 disk
    (put disk r o) (.Put r o) (put_step disk r o live) trivial

theorem ack_joint (rev : Bool) (dl : Delivery) (rg : Registry) (disk : Disk) (o : StoredObject Bool Bool)
    (quorum : ∀ r, disk.live r = true ∧ disk.stored r o = true)
    (guard : ParaleanPublicationDiscovery.StorageGuard
      (Durability.Label.Ack o () : Durability.Label Bool (StoredObject Bool Bool) Unit Unit)) :
    ParaleanProtocol.Next (theory rev) (recoveryTheory rev) encode (state dl rg disk)
      (state dl rg (ack disk o)) :=
  ParaleanProtocol.storage_step (theory rev) (recoveryTheory rev) encode dl rg rec0 disk
    (ack disk o) (.Ack o ()) (ack_step disk o quorum) guard

theorem prepare_joint (rev : Bool) (dl : Delivery) (rg rg' : Registry) (disk : Disk) (n g : Bool)
    (step : ParaleanGroups.GroupsNext (groupTheory rev) rg (.prepare n g) rg') :
    ParaleanProtocol.Next (theory rev) (recoveryTheory rev) encode (state dl rg disk) (state dl rg' disk) :=
  .paired (.admission (.registry (.prepare n g) trivial step trivial) rfl)
    (.registry (.prepare n g) (by intros; simp) step trivial (by intros; contradiction))

theorem publish_joint (rev : Bool) (dl : Delivery) (rg rg' : Registry) (disk : Disk) (n g : Bool)
    (step : ParaleanGroups.GroupsNext (groupTheory rev) rg (.publish n g) rg')
    (payload : disk.acknowledged (.payload g) = true)
    (quorum : ∀ r, disk.live r = true ∧ disk.stored r (.publication g) = true) :
    ParaleanProtocol.Next (theory rev) (recoveryTheory rev) encode (state dl rg disk)
      (state dl rg' (ack disk (.publication g))) :=
  .publish n g () step (ack_step disk (.publication g) quorum) payload

theorem control_joint (dl dl' : Delivery) (rg : Registry) (disk : Disk)
    (label : ParaleanDelivery.Label Bool Bool Bool Bool Bool (Fin 3))
    (control : ParaleanAdmission.Control label)
    (step : ParaleanDelivery.Step (deliveryTheory true) dl label dl') :
    ParaleanProtocol.Next (theory true) (recoveryTheory true) encode (state dl rg disk) (state dl' rg disk) :=
  .paired (.admission (.control label control step) rfl) .stutter

theorem accept_joint (dl dl' : Delivery) (rg rg' : Registry) (disk : Disk) (g : Bool)
    (delivery : ParaleanDelivery.Step (deliveryTheory true) dl (.accept true g) dl')
    (registry : ParaleanGroups.GroupsNext (groupTheory true) rg (.receive true g) rg')
    (marker : disk.acknowledged (.publication g) = true)
    (bytes : disk.stored true (.publication g) = true) (live : disk.live true = true) :
    ParaleanProtocol.Next (theory true) (recoveryTheory true) encode (state dl rg disk) (state dl' rg' disk) := by
  refine .paired (.admission (.accept true g (.paired delivery (.receive registry))) rfl)
    (.registry (.receive true g) (by intros; simp) registry trivial ?_)
  intro n d h
  cases h
  let ids := fun d => ∃ r, storageTheory.memberR r () = true ∧ disk.live r = true ∧
    disk.stored r (.publication d) = true
  exact ⟨(), ids, by intro d; rfl, ⟨true, rfl, live, bytes⟩, marker⟩

theorem receive_joint (rev : Bool) (dl : Delivery) (rg rg' : Registry) (disk : Disk) (g : Bool)
    (registry : ParaleanGroups.GroupsNext (groupTheory rev) rg (.receive true g) rg')
    (marker : disk.acknowledged (.publication g) = true)
    (bytes : disk.stored true (.publication g) = true) (live : disk.live true = true) :
    ParaleanProtocol.Next (theory rev) (recoveryTheory rev) encode (state dl rg disk) (state dl rg' disk) := by
  refine .paired (.admission (.registry (.receive true g) trivial registry trivial) rfl)
    (.registry (.receive true g) (by intros; simp) registry trivial ?_)
  intro n d h
  cases h
  let ids := fun d => ∃ r, storageTheory.memberR r () = true ∧ disk.live r = true ∧
    disk.stored r (.publication d) = true
  exact ⟨(), ids, by intro d; rfl, ⟨true, rfl, live, bytes⟩, marker⟩

theorem initial_valid (rev : Bool) :
    ParaleanCompletionRecovery.Initial (theory rev) (recoveryTheory rev) (state dl0 rg0 d0) := by
  refine ⟨⟨?_, ?_, ?_⟩, recovery_initial rev⟩
  · exact ParaleanCompletionRecovery.Example.delivery_steps.1
  · cases rev
    · exact bad_group_steps.1
    · exact group_steps.1
  · simp [ParaleanGroupComposition.StorageInit, Durability.Init, Durability.initializer.ext.tr,
      state, disk0, ParaleanCompletionRecovery.Example.disk0, getFrom, setIn, readFrom,
      Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
      ParaleanGroupComposition.diskFieldRep, Veil.canonicalFieldRepresentation,
      Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp]


/-- Initially worker `false` owns every name, at epoch `0`, with no recorded head. -/
abbrev e0 : Extra Bool Bool (Fin 3) := initExtra (fun _ => false)

/-- The record of target name `2` holds head `g`; no other name is a target. -/
abbrev withHead (e : Extra Bool Bool (Fin 3)) (g : Bool) : Extra Bool Bool (Fin 3) :=
  { e with head := fun x => if x = 2 then some g else none }

local notation "TReach" => Reachable (theory true) (targets true) (recoveryTheory true) encode
local notation "TGuard" => Guard (theory true) (targets true) (recoveryTheory true) encode

theorem target_two {rev : Bool} {x : Fin 3} (h : IsTarget (theory rev) (targets rev) x) : x = 2 := by
  obtain ⟨_, _, hq⟩ := h; exact hq.symm

theorem tstep {s t : CState} {e e' : Extra Bool Bool (Fin 3)} (h : TReach (s, e))
    (ht : ParaleanProtocol.Next (theory true) (recoveryTheory true) encode s t)
    (hg : TGuard s e t e') : TReach (t, e') :=
  .step h ⟨ht, hg⟩

macro "regs" : tactic => `(tactic| (intro n d hp; revert hp; cases n <;> cases d <;>
  simp [state, rg0, rgPreparedHelper, rgHelper, rgPreparedTarget, rgPublished,
    rgReceivedHelper, rgReceived, rgCommitted]))
macro "pubs" : tactic => `(tactic| (intro d hp; revert hp; cases d <;>
  simp [state, rg0, rgPreparedHelper, rgHelper, rgPreparedTarget, rgPublished,
    rgReceivedHelper, rgReceived, rgCommitted]))

/-- A step that creates no pending bit and publishes nothing new. -/
theorem pstep {s t : CState} {e : Extra Bool Bool (Fin 3)} (h : TReach (s, e))
    (ht : ParaleanProtocol.Next (theory true) (recoveryTheory true) encode s t)
    (hp : ∀ n d, t.admission.protocol.registry.pending n d = true →
      s.admission.protocol.registry.pending n d = true := by regs)
    (hq : ∀ d, t.admission.protocol.registry.published d = true →
      s.admission.protocol.registry.published d = true := by pubs) : TReach (t, e) :=
  tstep h ht (guard_of_quiet _ _ _ _ _ _ _ hp hq)

/-- A preparation step under an ownership state whose stamped epochs are all
current: the ownership state is unchanged. -/
theorem prepstep {s t : CState} {e : Extra Bool Bool (Fin 3)} (h : TReach (s, e))
    (ht : ParaleanProtocol.Next (theory true) (recoveryTheory true) encode s t)
    (hsync : ∀ n d x, e.preparedEpoch n d x = e.epoch x)
    (hprep : PrepareOk (theory true) (targets true) s e t)
    (hq : ∀ d, t.admission.protocol.registry.published d = true →
      s.admission.protocol.registry.published d = true := by pubs) : TReach (t, e) :=
  tstep h ht (guard_of_synced_prepare _ _ _ _ _ _ _ hsync hprep hq)

/-- Publishing target proof `g` sets the record's head to `g`. -/
theorem publish_update (s t : CState) (e : Extra Bool Bool (Fin 3)) (g : Bool)
    (hnone : ∀ x, x ≠ 2 → e.head x = none)
    (hp : ∀ n d, t.admission.protocol.registry.pending n d = true →
      s.admission.protocol.registry.pending n d = true)
    (hs : s.admission.protocol.registry.published g = false)
    (ht : t.admission.protocol.registry.published g = true)
    (hu : ∀ d, s.admission.protocol.registry.published d = false →
      t.admission.protocol.registry.published d = true → d = g) :
    update (theory true) (targets true) s t e = withHead e g := by
  refine update_eq _ _ s t e _ hp ?_
  intro x
  by_cases hx : x = 2
  · subst hx
    exact Or.inr ⟨g, ⟨⟨true, rfl, rfl⟩, by simp [theory, groupTheory], hs, ht⟩,
      fun d' hd' => hu d' hd'.2.2.1 hd'.2.2.2, by simp⟩
  · exact Or.inl ⟨fun d hd => hx (target_two hd.1), by simp [hx, hnone x hx]⟩

/-- A publication step of target proof `g` that passes the fence. -/
theorem pubstep {s t : CState} {e : Extra Bool Bool (Fin 3)} (h : TReach (s, e)) (g : Bool)
    (ht : ParaleanProtocol.Next (theory true) (recoveryTheory true) encode s t)
    (hpub : PublishOk (theory true) (targets true) s e t)
    (hnone : ∀ x, x ≠ 2 → e.head x = none)
    (hs : s.admission.protocol.registry.published g = false)
    (ht' : t.admission.protocol.registry.published g = true)
    (hu : ∀ d, s.admission.protocol.registry.published d = false →
      t.admission.protocol.registry.published d = true → d = g)
    (hp : ∀ n d, t.admission.protocol.registry.pending n d = true →
      s.admission.protocol.registry.pending n d = true := by regs) : TReach (t, withHead e g) := by
  have g' : TGuard s e t (update (theory true) (targets true) s t e) :=
    guard_of_no_new_pending _ _ _ _ _ _ _ hp hpub
  rw [publish_update s t e g hnone hp hs ht' hu] at g'
  exact tstep h ht g'

/-- Owner `false` prepares the first proof: nothing is published yet. -/
theorem first_prepare_ok :
    PrepareOk (theory true) (targets true) (state dl0 rg0 d5) e0 (state dl0 rgPreparedHelper d5) := by
  intro n d x hp hs hm hx
  have hx2 := target_two hx
  subst hx2
  cases n <;> cases d <;>
    simp [state, rg0, rgPreparedHelper, initExtra, theory, groupTheory, Bool.forall_bool] at hp hs ⊢

/-- After the first publication the record of name `2` holds head `false`. -/
abbrev eF : Extra Bool Bool (Fin 3) := withHead e0 false
/-- After the second publication it holds head `true`. -/
abbrev eT : Extra Bool Bool (Fin 3) := withHead e0 true

/-- Owner `false` prepares the second proof, which revises the recorded head `false`. -/
theorem second_prepare_ok :
    PrepareOk (theory true) (targets true) (state dl0 rgHelper d11) eF (state dl0 rgPreparedTarget d11) := by
  intro n d x hp hs hm hx
  have hx2 := target_two hx
  subst hx2
  cases n <;> cases d <;>
    simp [state, rg0, rgHelper, rgPreparedTarget, initExtra, theory, groupTheory, Bool.forall_bool] at hp hs ⊢

theorem synced0 (g : Bool) : ∀ n d x, (withHead e0 g).preparedEpoch n d x = (withHead e0 g).epoch x := by
  intro n d x; rfl

/-- Both proofs prepared by owner `false`; the second is still pending. -/
theorem second_prepared_reachable : TReach (state dl0 rgPreparedTarget d11, eF) := by
  obtain ⟨_, gp1, gu1, gp2, _⟩ := group_steps
  have h0 : TReach (state dl0 rg0 d0, e0) := .initial ⟨initial_valid true, rfl⟩
  have h1 := pstep h0 (put_joint true dl0 rg0 d0 false (.payload false) rfl)
  have h2 := pstep h1 (put_joint true dl0 rg0 d1 true (.payload false) rfl)
  have h3 := pstep h2 (ack_joint true dl0 rg0 d2 (.payload false)
    (by intro r; cases r <;> simp [disk0, put]) trivial)
  have h4 := pstep h3 (put_joint true dl0 rg0 d3 false (.publication false) rfl)
  have h5 := pstep h4 (put_joint true dl0 rg0 d4 true (.publication false) rfl)
  have h6 := prepstep h5 (prepare_joint true dl0 rg0 rgPreparedHelper d5 false false gp1)
    (fun _ _ _ => rfl) first_prepare_ok
  have h7 :=
    pubstep h6 false (publish_joint true dl0 rgPreparedHelper rgHelper d5 false false gu1
      (by simp [ack, put]) (by intro r; cases r <;> simp [disk0, put, ack]))
      (publishOk_initExtra _ _ _ _ _) (fun x hx => rfl)
      (by simp [state, rgPreparedHelper, rg0]) (by simp [state, rgHelper])
      (by intro d; cases d <;> simp [state, rgPreparedHelper, rgHelper, rg0])
  have h8 := pstep h7 (put_joint true dl0 rgHelper d6 false (.payload true) rfl)
  have h9 := pstep h8 (put_joint true dl0 rgHelper d7 true (.payload true) rfl)
  have h10 := pstep h9 (ack_joint true dl0 rgHelper d8 (.payload true)
    (by intro r; cases r <;> simp [disk0, put, ack]) trivial)
  have h11 := pstep h10 (put_joint true dl0 rgHelper d9 false (.publication true) rfl)
  have h12 := pstep h11 (put_joint true dl0 rgHelper d10 true (.publication true) rfl)
  exact prepstep h12 (prepare_joint true dl0 rgHelper rgPreparedTarget d11 false true gp2)
    (synced0 false) second_prepare_ok

theorem before_catalog_reachable : TReach (state dlA2 rgReceived d17, eT) := by
  obtain ⟨_, _, _, _, gu2, gr1, gr2, _⟩ := group_steps
  obtain ⟨_, ds1, df1, da1, ds2, df2, da2, _⟩ := delivery_steps
  have h14 :=
    pubstep second_prepared_reachable true (publish_joint true dl0 rgPreparedTarget rgPublished d11 false true gu2
      (by simp [ack, put]) (by intro r; cases r <;> simp [disk0, put, ack]))
      (publishOk_of_unchanged_epoch _ _ _ _ _ (fun _ _ _ _ _ _ => rfl)) (fun x hx => by simp [hx])
      (by simp [state, rgPreparedTarget, rgHelper, rg0]) (by simp [state, rgPublished])
      (by intro d; cases d <;> simp [state, rgPreparedTarget, rgPublished, rgHelper, rg0])
  have h15 := pstep h14 (control_joint dl0 dlS1 rgPublished d12 (.start true true) trivial ds1)
  have h16 := pstep h15 (control_joint dlS1 dlF1 rgPublished d12 (.send false) trivial df1)
  have h17 := pstep h16 (accept_joint dlF1 dlA1 rgPublished rgReceivedHelper d12 false da1 gr1
    (by simp [put, ack]) (by simp [put, ack]) rfl)
  have h18 := pstep h17 (control_joint dlA1 dlS2 rgReceivedHelper d12 (.start true true) trivial ds2)
  have h19 := pstep h18 (control_joint dlS2 dlF2 rgReceivedHelper d12 (.send true) trivial df2)
  have h20 := pstep h19 (accept_joint dlF2 dlA2 rgReceivedHelper rgReceived d12 true da2 gr2
    (by simp [ack]) (by simp [put, ack]) rfl)
  have h21 := pstep h20 (put_joint true dlA2 rgReceived d12 false (.manifest true) rfl)
  have h22 := pstep h21 (put_joint true dlA2 rgReceived d13 true (.manifest true) rfl)
  have h23 := pstep h22 (ack_joint true dlA2 rgReceived d14 (.manifest true)
    (by intro r; cases r <;> simp [disk0, put, ack]) trivial)
  have h24 := pstep h23 (put_joint true dlA2 rgReceived d15 false (.catalog 1) rfl)
  exact pstep h24 (put_joint true dlA2 rgReceived d16 true (.catalog 1) rfl)
theorem catalogue_commit_joint : ParaleanProtocol.Next (theory true) (recoveryTheory true) encode
    (state dlA2 rgReceived d17) (state dlA2 rgReceived d18 recCommitted) := by
  have hd := ack_step d17 (.catalog 1) (by intro r; cases r <;> simp [disk0, put, ack])
  refine .paired (.coupled (.protocol (.storage (.Ack (.catalog 1) ()) hd)) rfl rfl
    (.commit true false () recovery_commit hd ?_ ?_)) (.storage (.Ack (.catalog 1) ()) trivial hd)
  · simp [state, ParaleanRecovery.ofAdmission, protocolTheory, theory, recoveryTheory, put, ack]
  · intro g hg
    cases g <;> simp [state, ParaleanRecovery.ofAdmission, protocolTheory, theory, recoveryTheory, put, ack]

theorem guarded_finish_joint : ParaleanCompletionRecovery.FinishStep (theory true) (recoveryTheory true) true true true
    (state dlA2 rgReceived d18 recCommitted) (state dlD rgCommitted d18 recCommitted) := by
  refine .guarded (.paired delivery_steps.2.2.2.2.2.2.2
    (.registry group_steps.2.2.2.2.2.2.2 ?_)) rfl rfl rfl
  simp [ParaleanGroupComposition.Guard, protocolTheory, theory, put, ack]

abbrev completed : CState := state dlD rgCommitted d18 recCommitted

theorem completed_reachable : TReach (completed, eT) := by
  have h := pstep before_catalog_reachable catalogue_commit_joint
  exact pstep h (ParaleanProtocol.finish_step _ _ _ true true true guarded_finish_joint)

/-- Two distinct proofs of one required target are both published, the second
explicitly revising the first. Both receive accepted checked receipts, and the
guarded joint finish/commit completes with the second proof. -/
theorem alternatives_complete :
    TReach (completed, eT) ∧ eT.head 2 = some true ∧ Assumptions (theory true) ∧
    (false : Bool) ≠ true ∧
    (deliveryTheory true).required true = true ∧
    (deliveryTheory true).realizes false true = true ∧ (deliveryTheory true).realizes true true = true ∧
    (groupTheory true).member false ((targets true).targetName true) = true ∧
    (groupTheory true).member true ((targets true).targetName true) = true ∧
    (groupTheory true).revisions true false 2 = true ∧
    completed.admission.protocol.registry.published false = true ∧
    completed.admission.protocol.registry.published true = true ∧
    completed.admission.delivery.checked false true = true ∧
    completed.admission.delivery.checked true true = true ∧
    completed.admission.delivery.done true = true ∧ completed.admission.delivery.result true = true ∧
    (groupTheory true).contents true true = true ∧ (groupTheory true).contents true false = false ∧
    completed.admission.protocol.registry.head true = true ∧
    completed.recovery.committed true = true ∧
    ParaleanGroups.isHead true true 2 (groupTheory true) completed.admission.protocol.registry ∧
    ¬ParaleanGroups.isHead true false 2 (groupTheory true) completed.admission.protocol.registry := by
  refine ⟨completed_reachable, rfl, assumptions true, by decide, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  all_goals simp [ParaleanGroups.isHead, state, rgCommitted, rgReceived, rgPublished, rg0, groupTheory,
    getFrom, readFrom, Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation, Bool.exists_bool]


/-! ## Handover to a new owner while the old owner holds a pending proof -/

/-- The controller reassigns name `2` to worker `true` (epoch `1`). The record
keeps head `false`, the published first proof. -/
abbrev e1 : Extra Bool Bool (Fin 3) := reassign eF 2 true

/-- New owner `true` has received the published first proof. -/
def rgH1 : Registry := { rgPreparedTarget with known := fun _ g => !g }
/-- New owner `true` prepares proof `true`; the zombie still holds it pending too. -/
def rgH2 : Registry := { rgH1 with pending := fun _ g => g }
/-- New owner `true` publishes proof `true`; the zombie's pending bit survives. -/
def rgH3 : Registry :=
  { rgH2 with
    published := fun _ => true
    known := fun n g => n || !g
    pending := fun n g => !n && g
    clock := 2
    rank := fun g => if g then 1 else 0 }

theorem handover_group_steps :
    ParaleanGroups.GroupsNext (groupTheory true) rgPreparedTarget (.receive true false) rgH1 ∧
    ParaleanGroups.GroupsNext (groupTheory true) rgH1 (.prepare true true) rgH2 ∧
    ParaleanGroups.GroupsNext (groupTheory true) rgH2 (.publish true true) rgH3 := by
  repeat' apply And.intro
  all_goals simp [ParaleanGroups.GroupsNext, ParaleanGroups.Next, ParaleanGroups.NextAct,
    ParaleanGroups.prepare.ext.derived_eq, ParaleanGroups.publish.ext.derived_eq,
    ParaleanGroups.receive.ext.derived_eq,
    ParaleanGroups.prepare.ext.tr, ParaleanGroups.publish.ext.tr,
    ParaleanGroups.receive.ext.tr,
    groupTheory, rg0, rgHelper, rgPreparedTarget, rgH1, rgH2, rgH3, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation,
    Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp, funext_iff, Bool.forall_bool, Bool.exists_bool]

abbrev zombie : CState := state dl0 rgPreparedTarget d11
abbrev zombiePublished : CState := state dl0 rgPublished d12
abbrev handed : CState := state dl0 rgH3 d12

theorem zombie_reachable : TReach (zombie, e1) :=
  tstep second_prepared_reachable (protocol_stutter _ _ _ _) (guard_reassign _ _ _ _ _ _ 2 true)

/-- The zombie's publication of proof `true` is a base joint step. -/
theorem zombie_publish_joint :
    ParaleanProtocol.Next (theory true) (recoveryTheory true) encode zombie zombiePublished :=
  publish_joint true dl0 rgPreparedTarget rgPublished d11 false true group_steps.2.2.2.2.1
    (by simp [ack, put]) (by intro r; cases r <;> simp [disk0, put, ack])

/-- The new owner reads the record (owner `true`, head `false`) and prepares
proof `true`, which revises the recorded head. -/
theorem new_owner_prepare_guard :
    TGuard (state dl0 rgH1 d11) e1 (state dl0 rgH2 d11) (stamp (state dl0 rgH1 d11) (state dl0 rgH2 d11) e1) := by
  have hq : ∀ d, (state dl0 rgH2 d11).admission.protocol.registry.published d = true →
      (state dl0 rgH1 d11).admission.protocol.registry.published d = true := by
    intro d; cases d <;> simp [state, rg0, rgHelper, rgPreparedTarget, rgH1, rgH2]
  refine Or.inl ⟨?_, publishOk_of_no_new_published _ _ _ _ _ hq, ?_⟩
  · intro n d x hp hs hm hx
    have hx2 : x = 2 := by simpa [theory, groupTheory] using hm
    subst hx2
    cases n <;> cases d <;>
      simp [state, rg0, rgHelper, rgPreparedTarget, rgH1, rgH2, reassign, initExtra, theory,
        groupTheory, Bool.forall_bool] at hp hs ⊢
  · rw [update, advance_same _ _ _ _ _ hq]

abbrev e2 : Extra Bool Bool (Fin 3) := stamp (state dl0 rgH1 d11) (state dl0 rgH2 d11) e1
/-- The new owner's publication records head `true`. -/
abbrev e3 : Extra Bool Bool (Fin 3) := withHead e2 true

theorem handed_reachable : TReach (handed, e3) := by
  obtain ⟨gr, gp, gu⟩ := handover_group_steps
  have h1 : TReach (state dl0 rgH1 d11, e1) := pstep zombie_reachable
    (receive_joint true dl0 rgPreparedTarget rgH1 d11 false gr (by simp [put, ack]) (by simp [put, ack]) rfl)
    (by intro n d; cases n <;> cases d <;> simp [state, rg0, rgHelper, rgPreparedTarget, rgH1])
    (by intro d; cases d <;> simp [state, rg0, rgHelper, rgPreparedTarget, rgH1])
  have h2 := tstep h1 (prepare_joint true dl0 rgH1 rgH2 d11 true true gp) new_owner_prepare_guard
  refine pubstep h2 true (publish_joint true dl0 rgH2 rgH3 d11 true true gu
    (by simp [ack, put]) (by intro r; cases r <;> simp [disk0, put, ack])) ?_
    (fun x hx => by simp [e2, stamp, reassign, hx])
    (by simp [state, rgH2, rgH1, rgPreparedTarget, rgHelper, rg0]) (by simp [state, rgH3])
    (by intro d; cases d <;> simp [state, rgH2, rgH3, rgH1, rgPreparedTarget, rgHelper, rg0])
    (by intro n d; cases n <;> cases d <;> simp [state, rg0, rgHelper, rgPreparedTarget, rgH1, rgH2, rgH3])
  intro n d x hs ht hp hc hm hx
  have hx2 : x = 2 := by simpa [theory, groupTheory] using hm
  subst hx2
  cases n <;> cases d <;>
    simp [state, rg0, rgHelper, rgPreparedTarget, rgH1, rgH2, rgH3, stamp, reassign, initExtra] at hs ht hp hc ⊢

/-- Non-vacuity of the fence and of the head record. Owner `false` prepares
proof `true` (revising the recorded head `false`) at epoch `0`; the controller
then reassigns name `2` to worker `true` (epoch `1`) without the old owner's
cooperation; the record keeps head `false`. The old owner's publication of its
pending proof is a base joint step, but the guard rejects it. The new owner
reads the record, receives proof `false`, prepares proof `true`, which revises
the recorded head (an existing published proof), and publishes it, setting the
head to `true`, while the zombie still holds its stale pending bit. Both
published proofs form a chain and worker `true` has the unique head `true`. -/
theorem handover_witness :
    TReach (zombie, e1) ∧
    e0.owner 2 = false ∧ e1.owner 2 = true ∧ e1.epoch 2 = 1 ∧
    zombie.admission.protocol.registry.pending false true = true ∧
    e1.preparedEpoch false true 2 = 0 ∧
    ParaleanProtocol.Next (theory true) (recoveryTheory true) encode zombie zombiePublished ∧
    (∀ e', ¬TGuard zombie e1 zombiePublished e') ∧
    e1.head 2 = some false ∧
    PrepareOk (theory true) (targets true) (state dl0 rgH1 d11) e1 (state dl0 rgH2 d11) ∧
    TReach (handed, e3) ∧ e3.head 2 = some true ∧
    handed.admission.protocol.registry.published false = true ∧
    handed.admission.protocol.registry.published true = true ∧
    (groupTheory true).revisions true false 2 = true ∧
    handed.admission.protocol.registry.pending false true = true ∧
    e2.preparedEpoch false true 2 < e2.epoch 2 ∧
    e2.preparedEpoch true true 2 = 1 ∧
    ParaleanGroups.isHead true true 2 (groupTheory true) handed.admission.protocol.registry ∧
    ¬ParaleanGroups.isHead true false 2 (groupTheory true) handed.admission.protocol.registry := by
  refine ⟨zombie_reachable, rfl, ?_, ?_, rfl, ?_, zombie_publish_joint, ?_, rfl,
    ?_, handed_reachable, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [reassign]
  · simp [reassign, initExtra]
  · simp [reassign, initExtra]
  · intro e'
    exact stale_publication_blocked _ _ _ _ _ _ _ _ false true 2 rfl ⟨true, rfl, rfl⟩
      (by simp [reassign, initExtra]) rfl rfl rfl rfl
  · rcases new_owner_prepare_guard with ⟨hp, _⟩ | ⟨h, _⟩
    · exact hp
    · have := congrArg (fun s : CState => s.admission.protocol.registry.pending true true) h
      simp [state, rgH2, rgH1, rgPreparedTarget, rgHelper, rg0] at this
  · simp [stamp, reassign, initExtra, state, rgPreparedTarget, rgHelper, rg0, rgH2, rgH1]
  · simp [stamp, reassign, initExtra, state, rgPreparedTarget, rgHelper, rg0, rgH2, rgH1]
  all_goals simp [ParaleanGroups.isHead, state, rgH3, rgH2, rgH1, rgPreparedTarget, rgHelper, rg0,
    groupTheory, getFrom, readFrom, Veil.FieldRepresentation.get, instIsSubStateOfRefl,
    instIsSubReaderOfRefl, ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation,
    Bool.exists_bool]

/-! ## Guard necessity (base protocol, no guard) -/

local notation "BReach" => ParaleanProtocol.Reachable (theory false) (recoveryTheory false) encode


abbrev conflicted : CState := state dl0 rgN3 d12

/-- Without the guard, worker `true` independently proves the target: the base
joint protocol publishes two non-revising groups declaring name `2`. -/
theorem conflicted_reachable : BReach conflicted := by
  obtain ⟨_, gp1, gu1, gp2, gu2, gr⟩ := bad_group_steps
  have h0 : BReach (state dl0 rg0 d0) := .initial (initial_valid false)
  have h1 := ParaleanProtocol.Reachable.step h0 (put_joint false dl0 rg0 d0 false (.payload false) rfl)
  have h2 := ParaleanProtocol.Reachable.step h1 (put_joint false dl0 rg0 d1 true (.payload false) rfl)
  have h3 := ParaleanProtocol.Reachable.step h2 (ack_joint false dl0 rg0 d2 (.payload false)
    (by intro r; cases r <;> simp [disk0, put]) trivial)
  have h4 := ParaleanProtocol.Reachable.step h3 (put_joint false dl0 rg0 d3 false (.publication false) rfl)
  have h5 := ParaleanProtocol.Reachable.step h4 (put_joint false dl0 rg0 d4 true (.publication false) rfl)
  have h6 := ParaleanProtocol.Reachable.step h5 (prepare_joint false dl0 rg0 rgPreparedHelper d5 false false gp1)
  have h7 := ParaleanProtocol.Reachable.step h6 (publish_joint false dl0 rgPreparedHelper rgHelper d5 false false gu1
    (by simp [ack, put]) (by intro r; cases r <;> simp [disk0, put, ack]))
  have h8 := ParaleanProtocol.Reachable.step h7 (put_joint false dl0 rgHelper d6 false (.payload true) rfl)
  have h9 := ParaleanProtocol.Reachable.step h8 (put_joint false dl0 rgHelper d7 true (.payload true) rfl)
  have h10 := ParaleanProtocol.Reachable.step h9 (ack_joint false dl0 rgHelper d8 (.payload true)
    (by intro r; cases r <;> simp [disk0, put, ack]) trivial)
  have h11 := ParaleanProtocol.Reachable.step h10 (put_joint false dl0 rgHelper d9 false (.publication true) rfl)
  have h12 := ParaleanProtocol.Reachable.step h11 (put_joint false dl0 rgHelper d10 true (.publication true) rfl)
  have h13 := ParaleanProtocol.Reachable.step h12 (prepare_joint false dl0 rgHelper rgN1 d11 true true gp2)
  have h14 := ParaleanProtocol.Reachable.step h13 (publish_joint false dl0 rgN1 rgN2 d11 true true gu2
    (by simp [ack, put]) (by intro r; cases r <;> simp [disk0, put, ack]))
  exact ParaleanProtocol.Reachable.step h14 (receive_joint false dl0 rgN2 rgN3 d12 false gr
    (by simp [put, ack]) (by simp [put, ack]) rfl)

/-- The base joint protocol reaches two incomparable published proofs of the
required target's name. Worker `true` then has two heads, so `current` fails and
no commit or guarded finish of a snapshot containing either proof is enabled.
The target guard rejects, under every ownership state recording the published
proof as head, the step that created the second pending proof: it does not
revise the recorded head. -/
theorem guard_necessity :
    BReach conflicted ∧ Assumptions (theory false) ∧
    IsTarget (theory false) (targets false) 2 ∧
    conflicted.admission.protocol.registry.published false = true ∧
    conflicted.admission.protocol.registry.published true = true ∧
    (groupTheory false).member false 2 = true ∧ (groupTheory false).member true 2 = true ∧
    ¬((false : Bool) = true ∨ (groupTheory false).revisions false true 2 = true ∨
      (groupTheory false).revisions true false 2 = true) ∧
    ParaleanGroups.isHead true false 2 (groupTheory false) conflicted.admission.protocol.registry ∧
    ParaleanGroups.isHead true true 2 (groupTheory false) conflicted.admission.protocol.registry ∧
    (∀ S g, (groupTheory false).contents S g = true → (groupTheory false).member g 2 = true →
      ¬ParaleanGroups.current true S (groupTheory false) conflicted.admission.protocol.registry ∧
      (¬∃ rg', ParaleanGroups.GroupsNext (groupTheory false) conflicted.admission.protocol.registry
        (.commit true S) rg') ∧
      ∀ c t, ¬ParaleanCompletionRecovery.FinishStep (theory false) (recoveryTheory false) true S c conflicted t) ∧
    ParaleanProtocol.Next (theory false) (recoveryTheory false) encode
      (state dl0 rgHelper d11) (state dl0 rgN1 d11) ∧
    ∀ e e', e.head 2 = some false → ¬Guard (theory false) (targets false) (recoveryTheory false) encode
      (state dl0 rgHelper d11) e (state dl0 rgN1 d11) e' := by
  have hsimp : ∀ g, ParaleanGroups.isHead true g 2 (groupTheory false) conflicted.admission.protocol.registry := by
    intro g
    cases g <;> simp [ParaleanGroups.isHead, state, rgN3, rgN2, rg0, groupTheory,
      getFrom, readFrom, Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
      ParaleanGroups.canonicalFieldRep, Veil.canonicalFieldRepresentation, Bool.exists_bool]
  have nocur : ∀ S g, (groupTheory false).contents S g = true → (groupTheory false).member g 2 = true →
      ¬ParaleanGroups.current true S (groupTheory false) conflicted.admission.protocol.registry :=
    fun S g hg hm => ParaleanGroups.collision_blocks_current _ _ true S false true g 2
      (hsimp false) (hsimp true) (by decide) hg hm
  refine ⟨conflicted_reachable, assumptions false, ⟨true, rfl, rfl⟩, rfl, rfl, rfl, rfl,
    by simp [groupTheory], hsimp false, hsimp true, ?_,
    prepare_joint false dl0 rgHelper rgN1 d11 true true bad_group_steps.2.2.2.1, ?_⟩
  · intro S g hg hm
    have nocommit : ¬∃ rg', ParaleanGroups.GroupsNext (groupTheory false)
        conflicted.admission.protocol.registry (.commit true S) rg' := by
      rintro ⟨rg', hstep⟩
      exact nocur S g hg hm (ParaleanGroups.commit_fresh _ _ _ true S hstep).1
    refine ⟨nocur S g hg hm, nocommit, ?_⟩
    intro c t hf
    exact nocommit (finish_commits (theory false) (recoveryTheory false) true S c hf)
  · rintro e e' he (⟨hprep, _, _⟩ | ⟨heq, _⟩)
    · have h := (hprep true true 2 (by simp [state, rgN1]) (by simp [state, rgHelper, rg0])
        (by simp [theory, groupTheory]) ⟨true, rfl, rfl⟩).2.1 false he (by decide)
      simp [theory, groupTheory] at h
    · have := congrArg (fun s : CState => s.admission.protocol.registry.pending true true) heq
      simp [state, rgN1, rgHelper, rg0] at this


/-- The scan-blind counter-scenario. Worker `false` (owner A) publishes proof
`false`; no certificate quorum exists yet, so a certificate scan of the new
owner may return nothing (`ids = ∅`, allowed by `CertQuorum ⊆ ids ⊆ published`).
The controller reassigns name `2` to worker `true` (owner B). The scan-based
check `ScanPrepareOk` admits B's preparation of the non-revising proof `true`,
and the base protocol then publishes it: two heads for a required target. In
every target-reachable state of this instance in which `false` is published the
record holds head `false`, and the guard rejects B's preparation for every such
record. -/
theorem scan_check_unsafe :
    ScanPrepareOk (theory false) (targets false) (fun _ => False) (state dl0 rgHelper d11)
      (reassign e0 2 true) (state dl0 rgN1 d11) ∧
    ParaleanProtocol.Next (theory false) (recoveryTheory false) encode
      (state dl0 rgHelper d11) (state dl0 rgN1 d11) ∧
    BReach conflicted ∧
    (∃ g h, g ≠ h ∧ ParaleanGroups.isHead true g 2 (groupTheory false) conflicted.admission.protocol.registry ∧
      ParaleanGroups.isHead true h 2 (groupTheory false) conflicted.admission.protocol.registry) ∧
    (∀ p : CState × Extra Bool Bool (Fin 3),
      Reachable (theory false) (targets false) (recoveryTheory false) encode p →
      p.1.admission.protocol.registry.published false = true → p.2.head 2 = some false) ∧
    ∀ e e', e.head 2 = some false → ¬Guard (theory false) (targets false) (recoveryTheory false) encode
      (state dl0 rgHelper d11) e (state dl0 rgN1 d11) e' := by
  obtain ⟨hreach, _, _, _, _, _, _, _, hg, hh, _, hstep, hrej⟩ := guard_necessity
  refine ⟨?_, hstep, hreach, ⟨false, true, by decide, hg, hh⟩, ?_, hrej⟩
  · intro n d x hp hs hm hx
    have hx2 := target_two hx
    subst hx2
    cases n <;> cases d <;>
      simp [state, rgN1, rgHelper, rg0, reassign, initExtra, theory, groupTheory] at hp hs ⊢
  · intro p hr hp
    obtain ⟨h, hh, hgh⟩ := (recorded_head_tops_chain _ _ _ _ (assumptions false) hr 2 ⟨true, rfl, rfl⟩).2
      false hp (by simp [theory, groupTheory])
    rcases hgh with rfl | hrev
    · exact hh
    · simp [theory, groupTheory] at hrev

end
end ParaleanTargetNames.Example
#print axioms ParaleanTargetNames.guard_stutter
#print axioms ParaleanTargetNames.guard_of_synced_prepare
#print axioms ParaleanTargetNames.reachable_protocol
#print axioms ParaleanTargetNames.reachable_inv
#print axioms ParaleanTargetNames.target_chain
#print axioms ParaleanTargetNames.realized_chain
#print axioms ParaleanTargetNames.target_head_unique
#print axioms ParaleanTargetNames.no_target_collision
#print axioms ParaleanTargetNames.collision_premise_fails
#print axioms ParaleanTargetNames.stale_publication_blocked
#print axioms ParaleanTargetNames.split_owner_unpreparable
#print axioms ParaleanTargetNames.guard_observable
#print axioms ParaleanTargetNames.common_owner_preparable
#print axioms ParaleanTargetNames.Example.alternatives_complete
#print axioms ParaleanTargetNames.Example.handover_witness
#print axioms ParaleanTargetNames.Example.guard_necessity
#print axioms ParaleanTargetNames.Example.scan_check_unsafe
#print axioms ParaleanTargetNames.recorded_head_tops_chain
