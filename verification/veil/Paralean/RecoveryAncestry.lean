import Paralean.Recovery

/-! Catalog ancestry is exactly reachability through recorded parents. -/
namespace ParaleanRecovery

inductive ParentPath (th : Theory record workspace snapshot decl name token scan) :
    record → record → Prop where
  | edge {c p} : th.parent c p = true → ParentPath th c p
  | trans {c p a} : ParentPath th c p → ParentPath th p a → ParentPath th c a

noncomputable section
variable {record workspace snapshot decl name token scan : Type}
  [DecidableEq record] [Inhabited record]
  [DecidableEq workspace] [Inhabited workspace]
  [DecidableEq snapshot] [Inhabited snapshot]
  [DecidableEq decl] [Inhabited decl]
  [DecidableEq name] [Inhabited name]
  [DecidableEq token] [Inhabited token]
  [DecidableEq scan] [Inhabited scan]

theorem ancestor_iff_parent_path
    (th : Theory record workspace snapshot decl name token scan)
    (ha : TheoryAssumptions th) (c a : record) :
    th.ancestor c a = true ↔ ParentPath th c a := by
  constructor
  · have justified : ∀ k c, th.causalRank c = k → ∀ a,
        th.ancestor c a = true → ParentPath th c a := by
      intro k
      induction k using Nat.strongRecOn with
      | ind k ih =>
        intro c hc a hca
        obtain ⟨p, hp, hpa⟩ := ha.2.2.2 c a hca
        rcases hpa with rfl | hpa
        · exact .edge hp
        · have lower : th.causalRank p < k := hc ▸ ha.1 c p (ha.2.1 c p hp)
          exact .trans (.edge hp) (ih _ lower p rfl a hpa)
    exact justified _ c rfl a
  · intro path
    induction path with
    | edge hp => exact ha.2.1 _ _ hp
    | trans _ _ ih₁ ih₂ => exact ha.2.2.1 _ _ _ ih₁ ih₂

/-- Parentless records cannot claim any ancestry. This excludes the review counterexample. -/
theorem no_parent_no_ancestor
    (th : Theory record workspace snapshot decl name token scan)
    (ha : TheoryAssumptions th) (c : record)
    (root : ∀ p, th.parent c p = false) : ∀ a, th.ancestor c a = false := by
  intro a
  cases h : th.ancestor c a
  · rfl
  · obtain ⟨p, hp, _⟩ := ha.2.2.2 c a h
    simp [root p] at hp

theorem reconstruction_parent_iff
    (th : Theory record workspace snapshot decl name token scan)
    (ha : TheoryAssumptions th) (s : CanonicalState record workspace snapshot decl name token scan)
    (hs : Safe th s) (hr : s.reconstructed = true) (c : record) :
    s.heads c = true ↔ s.committed c = true ∧
      ¬∃ d, s.committed d = true ∧ ParentPath th d c := by
  simpa only [ancestor_iff_parent_path th ha] using reconstruction_iff th s hs hr c

theorem parent_conflict_iff
    (th : Theory record workspace snapshot decl name token scan)
    (ha : TheoryAssumptions th) (s : CanonicalState record workspace snapshot decl name token scan)
    (hs : Safe th s) (hr : s.reconstructed = true) :
    s.conflict = true ↔ ∃ c d,
      (s.committed c = true ∧ ¬∃ e, s.committed e = true ∧ ParentPath th e c) ∧
      (s.committed d = true ∧ ¬∃ e, s.committed e = true ∧ ParentPath th e d) ∧ c ≠ d := by
  simpa only [reconstruction_parent_iff th ha s hs hr] using conflict_iff th s hs hr

/-- In a parentless catalog, two distinct retained records remain heads. -/
theorem parentless_records_conflict
    (th : Theory record workspace snapshot decl name token scan)
    (ha : TheoryAssumptions th) (s : CanonicalState record workspace snapshot decl name token scan)
    (hs : Safe th s) (hr : s.reconstructed = true)
    (roots : ∀ c p, th.parent c p = false)
    (c d : record) (hc : s.committed c = true) (hd : s.committed d = true) (hne : c ≠ d) :
    s.conflict = true := by
  apply (conflict_iff th s hs hr).2
  have head : ∀ a, s.committed a = true → s.heads a = true := by
    intro a hcomm
    apply (reconstruction_iff th s hs hr a).2
    refine ⟨hcomm, ?_⟩
    rintro ⟨b, _, hba⟩
    simp [no_parent_no_ancestor th ha b (roots b) a] at hba
  exact ⟨c, d, head c hc, head d hd, hne⟩

end
#print axioms ancestor_iff_parent_path
#print axioms no_parent_no_ancestor
#print axioms reconstruction_parent_iff
#print axioms parent_conflict_iff
#print axioms parentless_records_conflict
end ParaleanRecovery
