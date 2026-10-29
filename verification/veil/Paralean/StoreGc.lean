import Std

/-!
Local transition lemmas for W4-rest design 1 (physical P2/S3 store GC), as
built. The state is abstract: `present` is the S3 object store, `gc` the FDB
`gcobj` state, `refs` says the `gcref` range of an object is nonempty,
`ocert` the T6 certificate, `inflight` says a forwarded DELETE of the object
may still execute at Garage. `named` is what committed metadata, staged
records, pending jobs and fetched anti-entropy objects name; `IndexComplete`
says every named object has a `gcref` entry. These lemmas do not refine the
Rust transactions; the bounded `StoreGc.tla` model checks the interleavings.
-/

namespace Paralean.StoreGc

variable {Obj : Type} [DecidableEq Obj]

inductive GcObj where
  | none
  | sighted (t : Nat)
  | doomed
  | deleting (nonce : Nat)
  | gone (t nonce : Nat)
  deriving DecidableEq

/-- States in which an object may be named and served. -/
def GcObj.live : GcObj → Prop
  | .none => True
  | .sighted _ => True
  | _ => False

def GcObj.isDeleting : GcObj → Prop
  | .deleting _ => True
  | _ => False

structure Store (Obj : Type) where
  present : Obj → Prop
  gc : Obj → GcObj
  refs : Obj → Prop
  ocert : Obj → Prop
  inflight : Obj → Prop

def update (f : Obj → β) (a : Obj) (b : β) : Obj → β :=
  fun x => if x = a then b else f x

/-- Every named object is present and in a live GC state. -/
def Safe (s : Store Obj) (named : Obj → Prop) : Prop :=
  ∀ o, named o → s.present o ∧ (s.gc o).live

def IndexComplete (s : Store Obj) (named : Obj → Prop) : Prop :=
  ∀ o, named o → s.refs o

/-- The implementation's invariant: an acknowledged object in a live GC state
(none or Sighted) is present. -/
def LivePresent (s : Store Obj) (acked : Obj → Prop) : Prop :=
  ∀ o, acked o → (s.gc o).live → s.present o

/-- A certificate vouches only for a present, live object. -/
def OcertSound (s : Store Obj) : Prop :=
  ∀ o, s.ocert o → s.present o ∧ (s.gc o).live

/-- A DELETE can be in flight only while the key is `Deleting`. -/
def InflightDeleting (s : Store Obj) : Prop :=
  ∀ o, s.inflight o → (s.gc o).isDeleting

/-! ### Doom -/

/-- The sweep's doom transaction: `Doomed` and the object's `ocert` cleared. -/
def doom (s : Store Obj) (o : Obj) : Store Obj :=
  { s with gc := update s.gc o .doomed, ocert := update s.ocert o False }

theorem doom_preserves_safe (s : Store Obj) (named : Obj → Prop) (o : Obj)
    (hSafe : Safe s named) (hIndex : IndexComplete s named)
    (hUnref : ¬ s.refs o) :
    Safe (doom s o) named := by
  intro x hNamed
  have hNe : x ≠ o := by
    intro hEq
    subst hEq
    exact hUnref (hIndex x hNamed)
  simp only [doom, update, if_neg hNe]
  exact hSafe x hNamed

theorem doom_preserves_ocert_sound (s : Store Obj) (o : Obj)
    (hSound : OcertSound s) : OcertSound (doom s o) := by
  intro x hCert
  by_cases hEq : x = o
  · subst hEq
    simp [doom, update] at hCert
  · simp only [doom, update, if_neg hEq] at hCert ⊢
    exact hSound x hCert

theorem doom_preserves_live_present (s : Store Obj) (acked : Obj → Prop) (o : Obj)
    (hInv : LivePresent s acked) : LivePresent (doom s o) acked := by
  intro x hAcked hLive
  by_cases hEq : x = o
  · subst hEq
    simp [doom, update, GcObj.live] at hLive
  · simp only [doom, update, if_neg hEq] at hLive ⊢
    exact hInv x hAcked hLive

/-! ### s3-guard and Garage -/

inductive Principal where
  | gc
  | forged
  | other
  deriving DecidableEq

/-- The guard matches the GC access key (Garage later checks the signature)
and admits a `Doomed` or `Deleting` key; it writes `Deleting{fresh nonce}`. -/
def guardAdmits (p : Principal) (g : GcObj) : Prop :=
  (p = .gc ∨ p = .forged) ∧ (g = .doomed ∨ g.isDeleting)

theorem guard_delete_requires_doomed_or_deleting (p : Principal) (g : GcObj)
    (hAdmit : guardAdmits p g) : g = .doomed ∨ g.isDeleting :=
  hAdmit.2

theorem guard_refuses_other_key (g : GcObj) : ¬ guardAdmits .other g := by
  intro hAdmit
  rcases hAdmit.1 with h | h <;> cases h

def admit (s : Store Obj) (o : Obj) (nonce : Nat) (signed : Prop) : Store Obj :=
  { s with gc := update s.gc o (.deleting nonce),
           inflight := fun x => if x = o then s.inflight o ∨ signed else s.inflight x }

/-- Garage executes a forwarded DELETE. -/
def garageExec (s : Store Obj) (o : Obj) : Store Obj :=
  { s with present := update s.present o False }

/-- The guard's completion: `Deleting{n}` to `Gone{clock, n}`. -/
def deleteDone (s : Store Obj) (o : Obj) (clock nonce : Nat) : Store Obj :=
  { s with gc := update s.gc o (.gone clock nonce) }

theorem admit_preserves_inflight_deleting (s : Store Obj) (o : Obj) (nonce : Nat)
    (signed : Prop) (hInv : InflightDeleting s) :
    InflightDeleting (admit s o nonce signed) := by
  intro x hIn
  by_cases hEq : x = o
  · subst hEq
    simp [admit, update, GcObj.isDeleting]
  · simp only [admit, update, if_neg hEq] at hIn ⊢
    exact hInv x hIn

theorem admit_preserves_live_present (s : Store Obj) (acked : Obj → Prop) (o : Obj)
    (nonce : Nat) (signed : Prop) (hInv : LivePresent s acked) :
    LivePresent (admit s o nonce signed) acked := by
  intro x hAcked hLive
  by_cases hEq : x = o
  · subst hEq
    simp [admit, update, GcObj.live] at hLive
  · simp only [admit, update, if_neg hEq] at hLive ⊢
    exact hInv x hAcked hLive

/-- Executing a forwarded DELETE removes only an object that is `Deleting`,
so every named object and every live acknowledged object stays present. -/
theorem exec_preserves_safe (s : Store Obj) (named acked : Obj → Prop) (o : Obj)
    (hSafe : Safe s named) (hLivePresent : LivePresent s acked)
    (hInv : InflightDeleting s) (hIn : s.inflight o) :
    Safe (garageExec s o) named ∧ LivePresent (garageExec s o) acked := by
  have hDel := hInv o hIn
  have hNotLive : ¬ (s.gc o).live := by
    intro hLive
    cases hG : s.gc o <;> simp_all [GcObj.live, GcObj.isDeleting]
  constructor
  · intro x hNamed
    have hNe : x ≠ o := by
      intro hEq
      subst hEq
      exact hNotLive (hSafe x hNamed).2
    simp only [garageExec, update, if_neg hNe]
    exact hSafe x hNamed
  · intro x hAcked hLive
    have hNe : x ≠ o := by
      intro hEq
      subst hEq
      exact hNotLive hLive
    simp only [garageExec, update, if_neg hNe]
    exact hLivePresent x hAcked hLive

/-- The fix: the guard writes `Gone` only when no forwarded DELETE of the key
can still execute. Then no DELETE is in flight for a `Gone` key, so a later
revival cannot be undone by a stale DELETE. -/
theorem quiescent_gone_preserves_inflight_deleting (s : Store Obj) (o : Obj)
    (clock nonce : Nat) (hInv : InflightDeleting s) (hQuiet : ¬ s.inflight o) :
    InflightDeleting (deleteDone s o clock nonce) := by
  intro x hIn
  by_cases hEq : x = o
  · subst hEq
    exact absurd hIn hQuiet
  · simp only [deleteDone, update, if_neg hEq]
    exact hInv x hIn

/-- Without quiescence the invariant fails: a DELETE in flight for a `Gone`
key is exactly the state a stale DELETE executes from. -/
theorem nonquiescent_gone_breaks_inflight_deleting (s : Store Obj) (o : Obj)
    (clock nonce : Nat) (hIn : s.inflight o) :
    ¬ InflightDeleting (deleteDone s o clock nonce) := by
  intro hInv
  have h := hInv o hIn
  simp [deleteDone, update, GcObj.isDeleting] at h

theorem gone_preserves_live_present (s : Store Obj) (acked : Obj → Prop) (o : Obj)
    (clock nonce : Nat) (hInv : LivePresent s acked) :
    LivePresent (deleteDone s o clock nonce) acked := by
  intro x hAcked hLive
  by_cases hEq : x = o
  · subst hEq
    simp [deleteDone, update, GcObj.live] at hLive
  · simp only [deleteDone, update, if_neg hEq] at hLive ⊢
    exact hInv x hAcked hLive

/-! ### Referencing transactions and revival -/

/-- A referencing transaction refuses `Doomed`, `Deleting` and `Gone`. -/
def refAllowed : GcObj → Prop
  | .none => True
  | .sighted _ => True
  | _ => False

theorem ref_allowed_iff_live (g : GcObj) : refAllowed g ↔ g.live := by
  cases g <;> simp [refAllowed, GcObj.live]

theorem ref_refuses_doomed : ¬ refAllowed .doomed := id

theorem ref_refuses_deleting (n : Nat) : ¬ refAllowed (.deleting n) := id

theorem ref_refuses_gone (t n : Nat) : ¬ refAllowed (.gone t n) := id

def reference (s : Store Obj) (o : Obj) : Store Obj :=
  { s with gc := update s.gc o (match s.gc o with | .sighted _ => .none | g => g),
           refs := update s.refs o True }

/-- A referencing transaction on a live, acknowledged object keeps every
named object safe and indexed. Its presence comes from `LivePresent`. -/
theorem reference_preserves_safe (s : Store Obj) (named acked : Obj → Prop)
    (o : Obj) (hSafe : Safe s named) (hIndex : IndexComplete s named)
    (hLivePresent : LivePresent s acked) (hAcked : acked o)
    (hAllowed : refAllowed (s.gc o)) :
    Safe (reference s o) (fun x => named x ∨ x = o) ∧
      IndexComplete (reference s o) (fun x => named x ∨ x = o) := by
  have hLive : (s.gc o).live := (ref_allowed_iff_live _).mp hAllowed
  have hPresent : s.present o := hLivePresent o hAcked hLive
  constructor
  · intro x hNamed
    by_cases hEq : x = o
    · subst hEq
      refine ⟨hPresent, ?_⟩
      simp only [reference, update]
      cases hG : s.gc x <;> simp_all [GcObj.live]
    · simp only [reference, update, if_neg hEq]
      rcases hNamed with hNamed | hNamed
      · exact hSafe x hNamed
      · exact absurd hNamed hEq
  · intro x hNamed
    by_cases hEq : x = o
    · subst hEq
      simp [reference, update]
    · simp only [reference, update, if_neg hEq]
      rcases hNamed with hNamed | hNamed
      · exact hIndex x hNamed
      · exact absurd hNamed hEq

/-- `gc_revive`: clear `gcobj` only if it is still the exact `Gone` read
before the re-PUT (or the GET-verification). -/
def reviveOK (seen current : GcObj) : Prop :=
  (∃ t n, seen = .gone t n) ∧ current = seen

def revive (s : Store Obj) (o : Obj) : Store Obj :=
  { s with gc := update s.gc o .none }

theorem revive_requires_exact_gone (seen current : GcObj)
    (hOK : reviveOK seen current) : ∃ t n, current = .gone t n ∧ seen = current := by
  obtain ⟨⟨t, n, hSeen⟩, hEq⟩ := hOK
  exact ⟨t, n, hEq ▸ hSeen, hEq.symm⟩

/-- A revival whose bytes are present (the re-PUT after reading this exact
`Gone`, with no DELETE in flight for a `Gone` key) keeps `LivePresent`. -/
theorem revive_preserves_live_present (s : Store Obj) (acked : Obj → Prop)
    (o : Obj) (hInv : LivePresent s acked) (hPresent : s.present o) :
    LivePresent (revive s o) acked := by
  intro x hAcked hLive
  by_cases hEq : x = o
  · subst hEq
    exact hPresent
  · simp only [revive, update, if_neg hEq] at hLive ⊢
    exact hInv x hAcked hLive

omit [DecidableEq Obj] in
/-- The re-PUT stays: if the `Gone` read before the PUT is still current, no
DELETE was admitted since (admission writes `Deleting`), and with the fix no
earlier DELETE is in flight for a `Gone` key. -/
theorem gone_key_has_no_inflight_delete (s : Store Obj) (o : Obj) (t n : Nat)
    (hInv : InflightDeleting s) (hGone : s.gc o = .gone t n) : ¬ s.inflight o := by
  intro hIn
  have h := hInv o hIn
  rw [hGone] at h
  exact h

/-! ### Atomic multi-group batches -/

/-- T12 (and T13): one transaction runs every member's body, which clears
`Sighted` and writes the member's referrer, and `batch/<id>`, which references
every member. -/
def batchCommit (s : Store Obj) (members : Obj → Prop) [DecidablePred members] :
    Store Obj :=
  { s with gc := fun x => if members x then
                            (match s.gc x with | .sighted _ => .none | g => g)
                          else s.gc x,
           refs := fun x => members x ∨ s.refs x }

omit [DecidableEq Obj] in
/-- If every member passes its body's check (all or nothing), the commit keeps
every named object, now including every member, present, live and indexed. -/
theorem batch_commit_preserves_safe (s : Store Obj) (named acked members : Obj → Prop)
    [DecidablePred members] (hSafe : Safe s named) (hIndex : IndexComplete s named)
    (hLivePresent : LivePresent s acked) (hAcked : ∀ m, members m → acked m)
    (hAll : ∀ m, members m → refAllowed (s.gc m)) :
    Safe (batchCommit s members) (fun x => named x ∨ members x) ∧
      IndexComplete (batchCommit s members) (fun x => named x ∨ members x) := by
  constructor
  · intro x hNamed
    by_cases hMember : members x
    · have hLive : (s.gc x).live := (ref_allowed_iff_live _).mp (hAll x hMember)
      refine ⟨hLivePresent x (hAcked x hMember) hLive, ?_⟩
      simp only [batchCommit, if_pos hMember]
      cases hG : s.gc x <;> simp_all [GcObj.live]
    · rcases hNamed with hNamed | hNamed
      · simp only [batchCommit, if_neg hMember]
        exact hSafe x hNamed
      · exact absurd hNamed hMember
  · intro x hNamed
    simp only [batchCommit]
    rcases hNamed with hNamed | hNamed
    · exact Or.inr (hIndex x hNamed)
    · exact Or.inl hNamed

/-! ### Dead catalogue records -/

/-- T5 needs `rank = fence` and the fence only grows, so a record staged
below the fence can never commit: retiring it loses nothing. -/
theorem dead_record_never_commits (rank fence later : Nat)
    (hDead : rank < fence) (hMonotone : fence ≤ later) : rank ≠ later := by
  omega

end Paralean.StoreGc
