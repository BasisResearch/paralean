import Paralean.Composition
import Paralean.Convergence

/-! Liveness of the guarded Registry/storage composition, via a proved trace
    projection into the generated Registry transition system. -/
namespace ParaleanComposition
noncomputable section EndToEnd

variable {node decl name snapshot replica obj writeQuorum readQuorum : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq decl] [Inhabited decl]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]
  [DecidableEq replica] [Inhabited replica] [DecidableEq obj] [Inhabited obj]
  [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum]

variable {th : Theory node decl name snapshot replica obj writeQuorum readQuorum}

theorem next_registry_projection
    {s s' : State node decl name snapshot replica obj writeQuorum readQuorum}
    (hn : Next th s s') :
    s'.registry = s.registry ∨ ∃ label,
      ParaleanRegistry.RegistryStep th.registry s.registry label s'.registry := by
  cases hn with
  | registry label ht hg => exact Or.inr ⟨label, ht⟩
  | storage label ht => exact Or.inl rfl
  | stutter => exact Or.inl rfl

theorem reachable_registry_projection
    {s : State node decl name snapshot replica obj writeQuorum readQuorum}
    (hr : Reachable th s) : ParaleanRegistry.Reachable th.registry s.registry := by
  induction hr with
  | initial hi => exact ParaleanRegistry.Reachable.initial hi.1
  | step hr hn ih =>
    rcases next_registry_projection hn with he | ⟨label, ht⟩
    · exact he.symm ▸ ih
    · exact ParaleanRegistry.Reachable.step ih ht

/-- Storage transitions and guarded Registry transitions share one timeline.
    Composition.Next already includes stuttering. -/
structure Trace (th : Theory node decl name snapshot replica obj writeQuorum readQuorum) where
  state : Nat → State node decl name snapshot replica obj writeQuorum readQuorum
  initial : Reachable th (state 0)
  next : ∀ t, Next th (state t) (state (t + 1))

theorem Trace.reachable (tr : Trace th) (t : Nat) : Reachable th (tr.state t) := by
  induction t with
  | zero => exact tr.initial
  | succ t ih => exact Reachable.step ih (tr.next t)

def Trace.toRegistryTrace (tr : Trace th) : ParaleanRegistry.Trace th.registry where
  state t := (tr.state t).registry
  initial := reachable_registry_projection tr.initial
  next t := next_registry_projection (tr.next t)

/-- Fairness of Registry Heal along the composed timeline. -/
abbrev Trace.HealFair (tr : Trace th) : Prop := tr.toRegistryTrace.HealFair

/-- Fairness of generated Registry Receive along the composed timeline.
    Storage work may interleave, but cannot starve an enabled receive forever. -/
abbrev Trace.ReceiveFair (tr : Trace th) : Prop := tr.toRegistryTrace.ReceiveFair

theorem Trace.eventual_delivery (tr : Trace th) (ha : Assumptions th)
    (hf : tr.HealFair) (rf : tr.ReceiveFair) (n : node) (d : decl)
    (t₀ : Nat) (hp : (tr.state t₀).registry.published d = true) :
    ParaleanConvergence.EventuallyAlways (fun t => (tr.state t).registry.known n d = true) := by
  exact tr.toRegistryTrace.eventual_delivery ha.1 hf rf n d t₀ hp

theorem Trace.index_convergence (tr : Trace th) (ha : Assumptions th)
    (hf : tr.HealFair) (rf : tr.ReceiveFair)
    (nodes : List node) (decls : List decl)
    (allNodes : ∀ n, n ∈ nodes) (allDecls : ∀ d, d ∈ decls) :
    ParaleanConvergence.EventuallyAlways (fun t => ∀ n,
      (tr.state t).registry.known n = (tr.state t).registry.published) := by
  exact tr.toRegistryTrace.index_convergence ha.1 hf rf nodes decls allNodes allDecls

theorem Trace.eventual_collision (tr : Trace th) (ha : Assumptions th)
    (hf : tr.HealFair) (rf : tr.ReceiveFair)
    (nodes : List node) (allNodes : ∀ n, n ∈ nodes)
    (a b : decl) (different : a ≠ b) (sameName : th.registry.declName a = th.registry.declName b)
    (t₀ : Nat) (pa : (tr.state t₀).registry.published a = true)
    (pb : (tr.state t₀).registry.published b = true)
    (unsuperseded : ∀ t e, (tr.state t).registry.published e = true →
      th.registry.ancestors e a ≠ true ∧ th.registry.ancestors e b ≠ true) :
    ParaleanConvergence.EventuallyAlways (fun t => ∀ n,
      ParaleanConvergence.Conflict (fun d => (tr.state t).registry.known n d = true)
        (fun e d => th.registry.ancestors e d = true)
        th.registry.declName (th.registry.declName a)) := by
  exact tr.toRegistryTrace.eventual_collision ha.1 hf rf nodes allNodes
    a b different sameName t₀ pa pb unsuperseded

theorem Trace.published_mono (tr : Trace th) {a b : Nat} (hab : a ≤ b)
    (d : decl) (hp : (tr.state a).registry.published d = true) :
    (tr.state b).registry.published d = true := by
  induction hab with
  | refl => exact hp
  | @step t ht ih =>
    rcases next_registry_projection (tr.next t) with he | ⟨label, hn⟩
    · simpa only [he] using ih
    · exact (ParaleanRegistry.registry_step_persistent th.registry _ _ label hn).1 d ih

/-- A published declaration retains a live storage copy throughout the suffix
    and eventually stays known at the target node. No storage-write fairness
    is needed because publication already required a storage acknowledgment. -/
theorem Trace.durable_delivery (tr : Trace th) (ha : Assumptions th)
    (hf : tr.HealFair) (rf : tr.ReceiveFair) (n : node) (d : decl)
    (t₀ : Nat) (hp : (tr.state t₀).registry.published d = true) :
    (∀ t, t₀ ≤ t → ∃ r, (tr.state t).storage.live r = true ∧
      (tr.state t).storage.stored r (th.payload d) = true) ∧
    ParaleanConvergence.EventuallyAlways (fun t => (tr.state t).registry.known n d = true) := by
  exact ⟨fun t ht => published_has_copy th ha (tr.reachable t) d (tr.published_mono ht d hp),
    tr.eventual_delivery ha hf rf n d t₀ hp⟩

end EndToEnd

#print axioms next_registry_projection
#print axioms reachable_registry_projection
#print axioms Trace.toRegistryTrace
#print axioms Trace.eventual_delivery
#print axioms Trace.index_convergence
#print axioms Trace.eventual_collision
#print axioms Trace.durable_delivery

end ParaleanComposition
