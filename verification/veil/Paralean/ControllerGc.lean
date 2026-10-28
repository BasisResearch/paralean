import Std

/-!
Local transition lemmas for W4 controller metadata. `Object` denotes a
snapshot incarnation, not a byte hash or a P2 protocol object. `reachable`
already includes current, pending, retained, checkpoint, catalogue, demand,
W3 tombstone-lineage and transitive dependency roots; `Roots` and `Reachable`
below make that root set explicit. These lemmas do not refine the Rust
transactions.
-/

namespace Paralean.ControllerGc

variable {Object Worker : Type}

def afterCollect (live : Object → Prop) (victim : Object) : Object → Prop :=
  fun object => live object ∧ object ≠ victim

theorem reachable_live_after_collect
    (live reachable : Object → Prop) (victim : Object)
    (hLive : ∀ object, reachable object → live object)
    (hUnreachable : ¬ reachable victim) :
    ∀ object, reachable object → afterCollect live victim object := by
  intro object hReachable
  constructor
  · exact hLive object hReachable
  · intro hEq
    subst object
    exact hUnreachable hReachable

theorem recovery_roots_live_after_collect
    (live reachable recoveryRoots : Object → Prop) (victim : Object)
    (hLive : ∀ object, reachable object → live object)
    (hRecovery : ∀ object, recoveryRoots object → reachable object)
    (hUnreachable : ¬ reachable victim) :
    ∀ object, recoveryRoots object → afterCollect live victim object := by
  intro object hRoot
  exact reachable_live_after_collect live reachable victim hLive hUnreachable
    object (hRecovery object hRoot)

/-- The GC root inventory. `tombstoned` holds W3 tombstone lineage: a
tombstoned position leaves the live view, but its record, certificates and
anchor marker must stay reachable. -/
structure Roots (Object : Type) where
  current : Object → Prop
  pending : Object → Prop
  retained : Object → Prop
  checkpoint : Object → Prop
  catalogue : Object → Prop
  demand : Object → Prop
  tombstoned : Object → Prop

def Roots.any (roots : Roots Object) (object : Object) : Prop :=
  roots.current object ∨ roots.pending object ∨ roots.retained object ∨
    roots.checkpoint object ∨ roots.catalogue object ∨ roots.demand object ∨
    roots.tombstoned object

/-- Reachability from the roots along dependencies (including RGA anchors). -/
inductive Reachable (roots : Roots Object) (dep : Object → Object → Prop) : Object → Prop
  | root {object : Object} : roots.any object → Reachable roots dep object
  | dep {object target : Object} :
      Reachable roots dep object → dep object target → Reachable roots dep target

theorem tombstone_lineage_live_after_collect
    (roots : Roots Object) (dep : Object → Object → Prop)
    (live : Object → Prop) (victim : Object)
    (hLive : ∀ object, Reachable roots dep object → live object)
    (hUnreachable : ¬ Reachable roots dep victim) :
    ∀ object target, roots.tombstoned object → dep object target →
      afterCollect live victim object ∧ afterCollect live victim target := by
  intro object target hTombstoned hDep
  have hRoot : Reachable roots dep object :=
    .root (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hTombstoned))))))
  exact ⟨reachable_live_after_collect live (Reachable roots dep) victim hLive hUnreachable object hRoot,
    reachable_live_after_collect live (Reachable roots dep) victim hLive hUnreachable target (.dep hRoot hDep)⟩

structure Lease (Worker : Type) where
  holder : Worker
  term : Nat
  expires : Nat

def publishAllowed (lease : Lease Worker) (worker : Worker)
    (stagedTerm now : Nat) : Prop :=
  lease.holder = worker ∧ lease.term = stagedTerm ∧ now < lease.expires

theorem stale_term_cannot_publish
    (lease : Lease Worker) (worker : Worker) (stagedTerm now : Nat)
    (hStale : stagedTerm ≠ lease.term) :
    ¬ publishAllowed lease worker stagedTerm now := by
  intro hAllowed
  exact hStale hAllowed.2.1.symm

theorem handover_fences_old_term
    (lease : Lease Worker) (worker : Worker) (oldTerm now : Nat)
    (hNewTerm : lease.term = oldTerm + 1) :
    ¬ publishAllowed lease worker oldTerm now := by
  apply stale_term_cannot_publish
  intro hSame
  omega

/- A batch compaction moves selected records from the snapshot to retained
   replay storage in one atomic transition. This proves coverage, assuming the
   implementation commits both halves together and preserves record contents. -/
def afterCompactSnapshot (current selected : Object → Prop) : Object → Prop :=
  fun request => current request ∧ ¬ selected request

def afterCompactReplay (replay current selected : Object → Prop) : Object → Prop :=
  fun request => replay request ∨ (current request ∧ selected request)

theorem atomic_compaction_preserves_retry_coverage
    (current replay selected known : Object → Prop)
    (hCovered : ∀ request, known request → current request ∨ replay request) :
    ∀ request, known request →
      afterCompactSnapshot current selected request ∨
      afterCompactReplay replay current selected request := by
  classical
  intro request hKnown
  rcases hCovered request hKnown with hCurrent | hReplay
  · by_cases hSelected : selected request
    · exact Or.inr (Or.inr ⟨hCurrent, hSelected⟩)
    · exact Or.inl ⟨hCurrent, hSelected⟩
  · exact Or.inr (Or.inl hReplay)

theorem terminal_compaction_preserves_pending
    (current selected terminal pending : Object → Prop)
    (hCurrent : ∀ request, pending request → current request)
    (hTerminal : ∀ request, selected request → terminal request)
    (hPending : ∀ request, pending request → ¬ terminal request) :
    ∀ request, pending request → afterCompactSnapshot current selected request := by
  intro request hPendingRequest
  refine ⟨hCurrent request hPendingRequest, ?_⟩
  intro hSelected
  exact hPending request hPendingRequest (hTerminal request hSelected)

end Paralean.ControllerGc
