import Paralean.Registry

/-! Temporal arguments over the anti-entropy projection. The action bridge below
    supplies these laws from Veil's generated transition semantics. -/
namespace ParaleanConvergence

def EventuallyAlways (P : Nat → Prop) : Prop :=
  ∃ cutoff, ∀ t, cutoff ≤ t → P t

structure DeliveryTrace (Node Decl : Type) where
  published : Nat → Decl → Prop
  known : Nat → Node → Decl → Prop
  ready : Nat → Node → Prop
  receive : Nat → Node → Decl → Prop
  published_step : ∀ t d, published t d → published (t + 1) d
  recovery : Nat
  ready_after : ∀ t, recovery ≤ t → ∀ n, ready t n
  known_step : ∀ t, recovery ≤ t → ∀ n d, known t n d → known (t + 1) n d
  receive_adds : ∀ t n d, receive t n d → known (t + 1) n d
  known_published : ∀ t n d, known t n d → published t d

def DeliveryTrace.Enabled (tr : DeliveryTrace Node Decl) (t : Nat) (n : Node) (d : Decl) : Prop :=
  tr.ready t n ∧ tr.published t d ∧ ¬tr.known t n d

/-- Weak fairness of the receive action. It quantifies execution of a
    continuously enabled transition, rather than assuming delivery. -/
def DeliveryTrace.WeakFair (tr : DeliveryTrace Node Decl) : Prop :=
  ∀ n d cutoff, (∀ t, cutoff ≤ t → tr.Enabled t n d) →
    ∃ t, cutoff ≤ t ∧ tr.receive t n d

theorem DeliveryTrace.published_mono (tr : DeliveryTrace Node Decl)
    {a b : Nat} (hab : a ≤ b) {d : Decl} (h : tr.published a d) : tr.published b d := by
  induction hab with
  | refl => exact h
  | @step b _ ih => exact tr.published_step b d ih

theorem DeliveryTrace.known_mono (tr : DeliveryTrace Node Decl)
    {a b : Nat} (ha : tr.recovery ≤ a) (hab : a ≤ b)
    {n : Node} {d : Decl} (h : tr.known a n d) : tr.known b n d := by
  induction hab with
  | refl => exact h
  | @step b hab ih => exact tr.known_step b (Nat.le_trans ha hab) n d ih

/-- Every durable publication reaches each recovered node and stays known. -/
theorem eventual_delivery (tr : DeliveryTrace Node Decl) (fair : tr.WeakFair)
    (n : Node) (d : Decl) (t₀ : Nat) (pub : tr.published t₀ d) :
    EventuallyAlways (fun t => tr.known t n d) := by
  classical
  let cutoff := max tr.recovery t₀
  have hr : tr.recovery ≤ cutoff := Nat.le_max_left _ _
  have hp : t₀ ≤ cutoff := Nat.le_max_right _ _
  have reached : ∃ t, cutoff ≤ t ∧ tr.known t n d := by
    by_contra absent
    have enabled : ∀ t, cutoff ≤ t → tr.Enabled t n d := by
      intro t ht
      exact ⟨tr.ready_after t (Nat.le_trans hr ht) n,
        tr.published_mono (Nat.le_trans hp ht) pub,
        fun hk => absent ⟨t, ht, hk⟩⟩
    obtain ⟨t, ht, recv⟩ := fair n d cutoff enabled
    exact absent ⟨t + 1, Nat.le_trans ht (Nat.le_succ t), tr.receive_adds t n d recv⟩
  obtain ⟨t, ht, hk⟩ := reached
  exact ⟨t, fun u hu => tr.known_mono (Nat.le_trans hr ht) hu hk⟩

theorem finite_eventuallyAlways (xs : List α) (P : α → Nat → Prop)
    (each : ∀ x ∈ xs, EventuallyAlways (P x)) :
    EventuallyAlways (fun t => ∀ x ∈ xs, P x t) := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons x xs ih =>
    obtain ⟨a, ha⟩ := each x (by simp)
    obtain ⟨b, hb⟩ := ih (fun y hy => each y (by simp [hy]))
    refine ⟨max a b, ?_⟩
    intro t ht y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ha t (Nat.le_trans (Nat.le_max_left _ _) ht)
    · exact hb t (Nat.le_trans (Nat.le_max_right _ _) ht) y hy

/-- A finite declaration universe gives one cutoff for the entire growing
    index. No publication-quiescence premise is needed. -/
theorem convergence (tr : DeliveryTrace Node Decl) (fair : tr.WeakFair)
    (nodes : List Node) (decls : List Decl)
    (allNodes : ∀ n, n ∈ nodes) (allDecls : ∀ d, d ∈ decls) :
    EventuallyAlways (fun t => ∀ n d, tr.known t n d ↔ tr.published t d) := by
  classical
  have each : ∀ d ∈ decls, EventuallyAlways (fun t => ∀ n, tr.known t n d ↔ tr.published t d) := by
    intro d _
    by_cases published : ∃ t, tr.published t d
    · obtain ⟨t₀, hp⟩ := published
      obtain ⟨cutoff, hc⟩ := finite_eventuallyAlways nodes (fun n t => tr.known t n d)
        (fun n _ => eventual_delivery tr fair n d t₀ hp)
      exact ⟨cutoff, fun t ht n => ⟨tr.known_published t n d, fun _ => hc t ht n (allNodes n)⟩⟩
    · exact ⟨0, fun t _ n => ⟨tr.known_published t n d,
        fun hp => False.elim (published ⟨t, hp⟩)⟩⟩
  obtain ⟨cutoff, hc⟩ := finite_eventuallyAlways decls _ each
  exact ⟨cutoff, fun t ht n d => hc t ht d (allDecls d) n⟩

def IsHead (known : Decl → Prop) (ancestors : Decl → Decl → Prop) (d : Decl) : Prop :=
  known d ∧ ¬∃ e, known e ∧ ancestors e d

def Conflict (known : Decl → Prop) (ancestors : Decl → Decl → Prop)
    (name : Decl → Name) (key : Name) : Prop :=
  ∃ a b, a ≠ b ∧ name a = key ∧ name b = key ∧
    IsHead known ancestors a ∧ IsHead known ancestors b

def Current (known : Decl → Prop) (ancestors : Decl → Decl → Prop)
    (name : Decl → Name) (d : Decl) : Prop :=
  ∀ e, name e = name d → (IsHead known ancestors e ↔ e = d)

theorem conflict_no_silent_winner (known : Decl → Prop) (ancestors : Decl → Decl → Prop)
    (name : Decl → Name) (key : Name) (conflict : Conflict known ancestors name key) :
    ¬∃ d, name d = key ∧ Current known ancestors name d := by
  obtain ⟨a, b, different, na, nb, ha, hb⟩ := conflict
  rintro ⟨d, nd, current⟩
  have ad : a = d := (current a (na.trans nd.symm)).mp ha
  have bd : b = d := (current b (nb.trans nd.symm)).mp hb
  exact different (ad.trans bd.symm)

/-- Immutable same-name heads become a visible collision at every finite
    collection of nodes. No published descendant may supersede either head. -/
theorem eventual_collision (tr : DeliveryTrace Node Decl) (fair : tr.WeakFair)
    (nodes : List Node) (allNodes : ∀ n, n ∈ nodes)
    (ancestors : Decl → Decl → Prop) (name : Decl → Name)
    (a b : Decl) (different : a ≠ b) (sameName : name a = name b)
    (t₀ : Nat) (pa : tr.published t₀ a) (pb : tr.published t₀ b)
    (unsuperseded : ∀ t e, tr.published t e → ¬ancestors e a ∧ ¬ancestors e b) :
    EventuallyAlways (fun t => ∀ n, Conflict (tr.known t n) ancestors name (name a)) := by
  have each : ∀ n ∈ nodes, EventuallyAlways (fun t => tr.known t n a ∧ tr.known t n b) := by
    intro n _
    obtain ⟨u, hu⟩ := eventual_delivery tr fair n a t₀ pa
    obtain ⟨v, hv⟩ := eventual_delivery tr fair n b t₀ pb
    exact ⟨max u v, fun t ht => ⟨hu t (Nat.le_trans (Nat.le_max_left _ _) ht),
      hv t (Nat.le_trans (Nat.le_max_right _ _) ht)⟩⟩
  obtain ⟨cutoff, hc⟩ := finite_eventuallyAlways nodes _ each
  refine ⟨cutoff, ?_⟩
  intro t ht n
  obtain ⟨ha, hb⟩ := hc t ht n (allNodes n)
  refine ⟨a, b, different, rfl, sameName.symm, ⟨ha, ?_⟩, ⟨hb, ?_⟩⟩
  · rintro ⟨e, he, hea⟩
    exact (unsuperseded t e (tr.known_published t n e he)).1 hea
  · rintro ⟨e, he, heb⟩
    exact (unsuperseded t e (tr.known_published t n e he)).2 heb

#print axioms eventual_delivery
#print axioms convergence
#print axioms eventual_collision
#print axioms conflict_no_silent_winner

end ParaleanConvergence

/-! This bridge uses Registry's generated actions. It does not introduce
    an independent anti-entropy transition system. -/
namespace ParaleanRegistry
noncomputable section TemporalBridge

variable {node decl name snapshot : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq decl] [Inhabited decl]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]

attribute [local instance] Classical.propDecidable

abbrev ReceiveStep (th : Theory node decl name snapshot)
    (s s' : CanonicalState node decl name snapshot) (n : node) (d : decl) : Prop :=
  receive.ext.tr (Theory node decl name snapshot) (CanonicalState node decl name snapshot)
    node decl name snapshot (CanonicalRep node decl name snapshot) n d th s s'

theorem receive_enabled_iff (th : Theory node decl name snapshot)
    (s : CanonicalState node decl name snapshot) (n : node) (d : decl) :
    (∃ s', ReceiveStep th s s' n d) ↔
      s.alive n = true ∧ s.online n = true ∧ s.published d = true ∧ ¬s.known n d = true := by
  dsimp [ReceiveStep, receive.ext.tr, getFrom, setIn, instIsSubStateOfRefl,
    Veil.FieldRepresentation.get, canonicalFieldRep, Veil.canonicalFieldRepresentation]
  constructor
  · rintro ⟨s', ha, ho, hp, hk, _⟩
    exact ⟨ha, ho, hp, hk⟩
  · rintro ⟨ha, ho, hp, hk⟩
    exact ⟨_, ha, ho, hp, hk, rfl⟩

theorem receive_adds_known (th : Theory node decl name snapshot)
    (s s' : CanonicalState node decl name snapshot) (n : node) (d : decl)
    (h : ReceiveStep th s s' n d) : s'.known n d = true := by
  simp only [ReceiveStep, receive.ext.tr] at h
  dsimp [getFrom, setIn, instIsSubStateOfRefl, Veil.FieldRepresentation.get,
    canonicalFieldRep, Veil.canonicalFieldRepresentation] at h
  rcases h with ⟨_, _, _, _, hs⟩
  subst s'
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

abbrev RegistryStep (th : Theory node decl name snapshot)
    (s : CanonicalState node decl name snapshot) (l : Label node decl name snapshot)
    (s' : CanonicalState node decl name snapshot) : Prop :=
  Next (Theory node decl name snapshot) (CanonicalState node decl name snapshot)
    node decl name snapshot (CanonicalRep node decl name snapshot) th s l s'

/-- Durable publication survives every generated Registry action. Stable
    states cannot crash or partition, so their knowledge and readiness persist. -/
theorem registry_step_persistent (th : Theory node decl name snapshot)
    (s s' : CanonicalState node decl name snapshot) (l : Label node decl name snapshot)
    (h : RegistryStep th s l s') :
    (∀ d, s.published d = true → s'.published d = true) ∧
    (s.stable = true → s'.stable = true ∧
      (∀ n d, s.known n d = true → s'.known n d = true) ∧
      (∀ n, s.alive n = true → s'.alive n = true) ∧
      (∀ n, s.online n = true → s'.online n = true)) ∧
    ((s.stable = true → ∀ n, s.alive n = true ∧ s.online n = true) →
      s'.stable = true → ∀ n, s'.alive n = true ∧ s'.online n = true) := by
  cases l <;>
    simp only [RegistryStep, Next, NextAct, prepare.ext.derived_eq, publish.ext.derived_eq,
      receive.ext.derived_eq, commit.ext.derived_eq, crash.ext.derived_eq,
      recover.ext.derived_eq, partition.ext.derived_eq, reconnect.ext.derived_eq,
      heal.ext.derived_eq] at h
  all_goals
    dsimp [prepare.ext.tr, publish.ext.tr, receive.ext.tr, commit.ext.tr, crash.ext.tr,
      recover.ext.tr, partition.ext.tr, reconnect.ext.tr, heal.ext.tr,
      getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
      instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
      Veil.canonicalFieldRepresentation] at h
    simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp] at h
    try split_ifs at h
    all_goals
      repeat' rcases h with ⟨ha, h⟩
      try subst s'
      simp_all

#print axioms receive_adds_known
#print axioms registry_step_persistent

abbrev HealStep (th : Theory node decl name snapshot)
    (s s' : CanonicalState node decl name snapshot) : Prop :=
  heal.ext.tr (Theory node decl name snapshot) (CanonicalState node decl name snapshot)
    node decl name snapshot (CanonicalRep node decl name snapshot) th s s'

theorem heal_enabled_iff (th : Theory node decl name snapshot)
    (s : CanonicalState node decl name snapshot) :
    (∃ s', HealStep th s s') ↔ ¬s.stable = true := by
  dsimp [HealStep, heal.ext.tr, getFrom, setIn, instIsSubStateOfRefl,
    Veil.FieldRepresentation.get, canonicalFieldRep, Veil.canonicalFieldRepresentation]
  constructor
  · rintro ⟨s', hs, _⟩
    exact hs
  · intro hs
    exact ⟨_, hs, rfl⟩

theorem heal_sets_stable (th : Theory node decl name snapshot)
    (s s' : CanonicalState node decl name snapshot) (h : HealStep th s s') :
    s'.stable = true := by
  dsimp [HealStep, heal.ext.tr, getFrom, setIn, instIsSubStateOfRefl,
    Veil.FieldRepresentation.get, canonicalFieldRep, Veil.canonicalFieldRepresentation] at h
  rcases h with ⟨_, hs⟩
  subst s'
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

theorem reachable_ready (th : Theory node decl name snapshot)
    {s : CanonicalState node decl name snapshot} (hr : Reachable th s) :
    s.stable = true → ∀ n, s.alive n = true ∧ s.online n = true := by
  induction hr with
  | initial hi =>
    dsimp [RegistryInit, Init, initializer.ext.tr, getFrom, setIn, instIsSubStateOfRefl] at hi
    cases hi
    simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp]
  | step hr ht ih => exact (registry_step_persistent th _ _ _ ht).2.2 ih
  | stutter hr ih => exact ih

structure Trace (th : Theory node decl name snapshot) where
  state : Nat → CanonicalState node decl name snapshot
  initial : Reachable th (state 0)
  next : ∀ t, state (t + 1) = state t ∨ ∃ l, RegistryStep th (state t) l (state (t + 1))

variable {th : Theory node decl name snapshot}

theorem Trace.reachable (tr : Trace th) (t : Nat) : Reachable th (tr.state t) := by
  induction t with
  | zero => exact tr.initial
  | succ t ih =>
    rcases tr.next t with he | ⟨l, hn⟩
    · exact he.symm ▸ ih
    · exact Reachable.step ih hn

def Trace.ReceiveFair (tr : Trace th) : Prop :=
  ∀ n d cutoff,
    (∀ t, cutoff ≤ t → (tr.state t).alive n = true ∧ (tr.state t).online n = true ∧
      (tr.state t).published d = true ∧ ¬(tr.state t).known n d = true) →
    ∃ t, cutoff ≤ t ∧ ReceiveStep th (tr.state t) (tr.state (t + 1)) n d

def Trace.HealFair (tr : Trace th) : Prop :=
  ∀ cutoff, (∀ t, cutoff ≤ t → ¬(tr.state t).stable = true) →
    ∃ t, cutoff ≤ t ∧ HealStep th (tr.state t) (tr.state (t + 1))

theorem Trace.eventually_stable (tr : Trace th) (fair : tr.HealFair) :
    ∃ cutoff, (tr.state cutoff).stable = true := by
  classical
  by_contra absent
  obtain ⟨t, _, ht⟩ := fair 0 (fun t _ hs => absent ⟨t, hs⟩)
  exact absent ⟨t + 1, heal_sets_stable th _ _ ht⟩

theorem Trace.stable_after (tr : Trace th) {a b : Nat} (hab : a ≤ b)
    (hs : (tr.state a).stable = true) : (tr.state b).stable = true := by
  induction hab with
  | refl => exact hs
  | @step t ht ih =>
    rcases tr.next t with he | ⟨l, hn⟩
    · simpa only [he] using ih
    · exact ((registry_step_persistent th _ _ l hn).2.1 ih).1

/-- Every trace law is discharged using generated Registry transitions and
    the proved safety invariant. The only temporal premises are action fairness. -/
def Trace.deliveryTrace (tr : Trace th) (ha : TheoryAssumptions th)
    (cutoff : Nat) (stable : (tr.state cutoff).stable = true) :
    ParaleanConvergence.DeliveryTrace node decl where
  published t d := (tr.state t).published d = true
  known t n d := (tr.state t).known n d = true
  ready t n := (tr.state t).alive n = true ∧ (tr.state t).online n = true
  receive t n d := ReceiveStep th (tr.state t) (tr.state (t + 1)) n d
  published_step := by
    intro t d hp
    rcases tr.next t with he | ⟨l, hn⟩
    · simpa only [he] using hp
    · exact (registry_step_persistent th _ _ l hn).1 d hp
  recovery := cutoff
  ready_after := by
    intro t ht n
    exact reachable_ready th (tr.reachable t) (tr.stable_after ht stable) n
  known_step := by
    intro t ht n d hk
    rcases tr.next t with he | ⟨l, hn⟩
    · simpa only [he] using hk
    · exact ((registry_step_persistent th _ _ l hn).2.1 (tr.stable_after ht stable)).2.1 n d hk
  receive_adds := by
    intro t n d hr
    exact receive_adds_known th _ _ n d hr
  known_published := by
    intro t n d hk
    exact (reachable_safe th ha (tr.reachable t)).2.2.1 n d hk

theorem Trace.deliveryTrace_fair (tr : Trace th) (ha : TheoryAssumptions th)
    (cutoff : Nat) (stable : (tr.state cutoff).stable = true) (fair : tr.ReceiveFair) :
    (tr.deliveryTrace ha cutoff stable).WeakFair := by
  intro n d t₀ enabled
  exact fair n d t₀ (fun t ht => ⟨(enabled t ht).1.1, (enabled t ht).1.2,
    (enabled t ht).2.1, (enabled t ht).2.2⟩)

theorem Trace.eventual_delivery (tr : Trace th) (ha : TheoryAssumptions th)
    (hf : tr.HealFair) (rf : tr.ReceiveFair) (n : node) (d : decl)
    (t₀ : Nat) (hp : (tr.state t₀).published d = true) :
    ParaleanConvergence.EventuallyAlways (fun t => (tr.state t).known n d = true) := by
  obtain ⟨cutoff, hs⟩ := tr.eventually_stable hf
  exact ParaleanConvergence.eventual_delivery (tr.deliveryTrace ha cutoff hs)
    (tr.deliveryTrace_fair ha cutoff hs rf) n d t₀ hp

theorem Trace.convergence (tr : Trace th) (ha : TheoryAssumptions th)
    (hf : tr.HealFair) (rf : tr.ReceiveFair)
    (nodes : List node) (decls : List decl)
    (allNodes : ∀ n, n ∈ nodes) (allDecls : ∀ d, d ∈ decls) :
    ParaleanConvergence.EventuallyAlways (fun t => ∀ n d,
      (tr.state t).known n d = true ↔ (tr.state t).published d = true) := by
  obtain ⟨cutoff, hs⟩ := tr.eventually_stable hf
  exact ParaleanConvergence.convergence (tr.deliveryTrace ha cutoff hs)
    (tr.deliveryTrace_fair ha cutoff hs rf) nodes decls allNodes allDecls

theorem Trace.eventual_collision (tr : Trace th) (ha : TheoryAssumptions th)
    (hf : tr.HealFair) (rf : tr.ReceiveFair)
    (nodes : List node) (allNodes : ∀ n, n ∈ nodes)
    (a b : decl) (different : a ≠ b) (sameName : th.declName a = th.declName b)
    (t₀ : Nat) (pa : (tr.state t₀).published a = true) (pb : (tr.state t₀).published b = true)
    (unsuperseded : ∀ t e, (tr.state t).published e = true →
      th.ancestors e a ≠ true ∧ th.ancestors e b ≠ true) :
    ParaleanConvergence.EventuallyAlways (fun t => ∀ n,
      ParaleanConvergence.Conflict (fun d => (tr.state t).known n d = true)
        (fun e d => th.ancestors e d = true) th.declName (th.declName a)) := by
  obtain ⟨cutoff, hs⟩ := tr.eventually_stable hf
  exact ParaleanConvergence.eventual_collision (tr.deliveryTrace ha cutoff hs)
    (tr.deliveryTrace_fair ha cutoff hs rf) nodes allNodes
    (fun e d => th.ancestors e d = true) th.declName a b different sameName t₀ pa pb unsuperseded

theorem Trace.index_convergence (tr : Trace th) (ha : TheoryAssumptions th)
    (hf : tr.HealFair) (rf : tr.ReceiveFair)
    (nodes : List node) (decls : List decl)
    (allNodes : ∀ n, n ∈ nodes) (allDecls : ∀ d, d ∈ decls) :
    ParaleanConvergence.EventuallyAlways (fun t => ∀ n,
      (tr.state t).known n = (tr.state t).published) := by
  obtain ⟨cutoff, hc⟩ := tr.convergence ha hf rf nodes decls allNodes allDecls
  refine ⟨cutoff, ?_⟩
  intro t ht n
  funext d
  have h := hc t ht n d
  cases hk : (tr.state t).known n d <;>
    cases hp : (tr.state t).published d <;> simp_all

#print axioms reachable_ready
#print axioms Trace.eventual_delivery
#print axioms Trace.convergence
#print axioms Trace.eventual_collision
#print axioms Trace.index_convergence
#print axioms receive_enabled_iff
#print axioms heal_enabled_iff

theorem conflicting_name_not_current (th : Theory node decl name snapshot)
    (s : CanonicalState node decl name snapshot) (n : node) (key : name)
    (collision : ParaleanConvergence.Conflict (fun d => s.known n d = true)
      (fun e d => th.ancestors e d = true) th.declName key)
    (S : snapshot) (hc : current n S th s) :
    ∀ d, th.contents S d = true → th.declName d ≠ key := by
  intro d hd hn
  apply ParaleanConvergence.conflict_no_silent_winner
    (fun d => s.known n d = true) (fun e d => th.ancestors e d = true) th.declName key collision
  refine ⟨d, hn, ?_⟩
  dsimp [current, isHead, getFrom, readFrom, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    Veil.FieldRepresentation.get, canonicalFieldRep, Veil.canonicalFieldRepresentation] at hc
  exact hc d hd

#print axioms conflicting_name_not_current

def stutterTrace (th : Theory node decl name snapshot)
    (s : CanonicalState node decl name snapshot) (hr : Reachable th s) : Trace th where
  state _ := s
  initial := hr
  next _ := Or.inl rfl

/-- A reachable state with an undelivered durable declaration may stutter
    forever. Recovery alone therefore cannot imply delivery. -/
theorem reachable_stutter_prevents_delivery (th : Theory node decl name snapshot)
    (s : CanonicalState node decl name snapshot) (hr : Reachable th s)
    (n : node) (d : decl) (pub : s.published d = true) (missing : s.known n d ≠ true)
    (ready : s.alive n = true ∧ s.online n = true) :
    ¬ParaleanConvergence.EventuallyAlways
      (fun t => ((stutterTrace th s hr).state t).known n d = true) ∧
    ¬(stutterTrace th s hr).ReceiveFair := by
  constructor
  · rintro ⟨cutoff, hc⟩
    exact missing (hc cutoff (Nat.le_refl _))
  · intro fair
    obtain ⟨t, _, recv⟩ := fair n d 0 (fun _ _ => ⟨ready.1, ready.2, pub, missing⟩)
    exact missing (receive_adds_known th s s n d recv)

#print axioms reachable_stutter_prevents_delivery

end TemporalBridge
end ParaleanRegistry

namespace ParaleanConvergence

/-- A permanently idle scheduler satisfies the storage and recovery laws but
    loses delivery. This witnesses why action fairness cannot be omitted. -/
def idleTrace : DeliveryTrace Unit Unit where
  published _ _ := True
  known _ _ _ := False
  ready _ _ := True
  receive _ _ _ := False
  published_step := by intros; trivial
  recovery := 0
  ready_after := by intros; trivial
  known_step := by intros; assumption
  receive_adds := by intros; assumption
  known_published := by intros; trivial

theorem unfair_scheduler_counterexample :
    (∀ t, idleTrace.published t ()) ∧
    (∀ t, idleTrace.ready t ()) ∧
    ¬EventuallyAlways (fun t => idleTrace.known t () ()) ∧ ¬idleTrace.WeakFair := by
  refine ⟨fun _ => trivial, fun _ => trivial, ?_, ?_⟩
  · rintro ⟨cutoff, hc⟩
    exact hc cutoff (Nat.le_refl _)
  · intro fair
    obtain ⟨t, _, hr⟩ := fair () () 0 (by intro t ht; exact ⟨trivial, trivial, id⟩)
    exact hr

#print axioms unfair_scheduler_counterexample

end ParaleanConvergence
