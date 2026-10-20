import Std

/-!
Local transition lemmas for W4 controller metadata. `Object` denotes a
snapshot incarnation, not a byte hash or a P2 protocol object. `reachable`
already includes current, pending, retained, checkpoint, catalogue, demand and
transitive dependency roots. These lemmas do not refine the Rust transactions.
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
