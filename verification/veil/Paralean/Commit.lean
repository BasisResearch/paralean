import Paralean.Composition

/-! Freshness is checked at the successful commit transition. It is not a
permanent property of stored checkpoints: later receipt can supersede members.
The labelled transition also includes commits that write the existing head. -/

namespace ParaleanRegistry

noncomputable section CommitProofs
variable {node decl name snapshot : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq decl] [Inhabited decl]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]

attribute [local instance] Classical.propDecidable

/-- Fresh, buildable snapshots have a successful commit whenever the node is ready. -/
theorem commit_enabled_iff
    (th : Theory node decl name snapshot) (st : CanonicalState node decl name snapshot)
    (n : node) (S : snapshot) :
    (∃ st', RegistryNext th st (.commit n S) st') ↔
      st.alive n = true ∧ st.online n = true ∧
      (∀ d, th.contents S d = true → st.known n d = true) ∧
      buildable S th st ∧ current n S th st := by
  simp only [RegistryNext, Next, NextAct, commit.ext.derived_eq]
  dsimp [commit.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
    Veil.canonicalFieldRepresentation]
  constructor
  · rintro ⟨st', ha, ho, hk, hv, hd, hu, he, hc, _⟩
    exact ⟨ha, ho, hk, ⟨hv, hd, hu, he⟩, hc⟩
  · rintro ⟨ha, ho, hk, hb, hc⟩
    rcases hb with ⟨hv, hd, hu, he⟩
    exact ⟨_, ha, ho, hk, hv, hd, hu, he, hc, rfl⟩

/-- The actual generated commit relation supplies the freshness premise. -/
theorem commit_fresh
    (th : Theory node decl name snapshot) (st st' : CanonicalState node decl name snapshot)
    (n : node) (S : snapshot) (ht : RegistryNext th st (.commit n S) st') :
    current n S th st ∧ st'.head n = S := by
  simp only [RegistryNext, Next, NextAct, commit.ext.derived_eq] at ht
  dsimp [commit.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
    Veil.canonicalFieldRepresentation] at ht
  rcases ht with ⟨_, _, _, _, _, _, _, hc, hs⟩
  subst st'
  refine ⟨hc, ?_⟩
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

theorem commit_member_unique_head
    (th : Theory node decl name snapshot) (st st' : CanonicalState node decl name snapshot)
    (n : node) (S : snapshot) (ht : RegistryNext th st (.commit n S) st')
    (d e : decl) (hd : th.contents S d = true) (hn : th.declName e = th.declName d) :
    isHead n e th st ↔ e = d :=
  (commit_fresh th st st' n S ht).1 d hd e hn

/-- Every committed member is known and has no known descendant at admission. -/
theorem commit_member_not_stale
    (th : Theory node decl name snapshot) (st st' : CanonicalState node decl name snapshot)
    (n : node) (S : snapshot) (ht : RegistryNext th st (.commit n S) st')
    (d : decl) (hd : th.contents S d = true) :
    st.known n d = true ∧ ¬∃ e, st.known n e = true ∧ th.ancestors e d = true := by
  have hh := (commit_member_unique_head th st st' n S ht d d hd rfl).2 rfl
  exact hh

theorem stale_member_blocks_commit
    (th : Theory node decl name snapshot) (st st' : CanonicalState node decl name snapshot)
    (n : node) (S : snapshot) (d e : decl) (hd : th.contents S d = true)
    (hk : st.known n e = true) (ha : th.ancestors e d = true) :
    ¬RegistryNext th st (.commit n S) st' := by
  intro ht
  exact (commit_member_not_stale th st st' n S ht d hd).2 ⟨e, hk, ha⟩

theorem commit_excludes_collision
    (th : Theory node decl name snapshot) (st st' : CanonicalState node decl name snapshot)
    (n : node) (S : snapshot) (ht : RegistryNext th st (.commit n S) st')
    (a b : decl) (ha : isHead n a th st) (hb : isHead n b th st)
    (hn : th.declName a = th.declName b) (hne : a ≠ b) :
    ∀ d, th.contents S d = true → th.declName d ≠ th.declName a := by
  intro d hd hname
  exact collision_blocks_current th st n S a b d ha hb hname.symm
    (hn.symm.trans hname.symm) hne hd (commit_fresh th st st' n S ht).1

theorem collision_blocks_commit
    (th : Theory node decl name snapshot) (st st' : CanonicalState node decl name snapshot)
    (n : node) (S : snapshot) (a b d : decl)
    (ha : isHead n a th st) (hb : isHead n b th st)
    (hna : th.declName a = th.declName d) (hnb : th.declName b = th.declName d)
    (hne : a ≠ b) (hd : th.contents S d = true) :
    ¬RegistryNext th st (.commit n S) st' := by
  intro ht
  exact collision_blocks_current th st n S a b d ha hb hna hnb hne hd
    (commit_fresh th st st' n S ht).1

end CommitProofs

#print axioms commit_fresh
#print axioms commit_enabled_iff
#print axioms commit_member_unique_head
#print axioms commit_member_not_stale
#print axioms stale_member_blocks_commit
#print axioms commit_excludes_collision
#print axioms collision_blocks_commit

end ParaleanRegistry

namespace ParaleanComposition

noncomputable section CommitProofs
variable {node decl name snapshot replica obj writeQuorum readQuorum : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq decl] [Inhabited decl]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]
  [DecidableEq replica] [Inhabited replica] [DecidableEq obj] [Inhabited obj]
  [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum]

/-- A successful guarded commit carries its generated action label.
`Next` erases labels, so a state pair alone cannot distinguish a same-head
commit from a stutter. No head-change test is imposed here. -/
inductive CommitStep (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (n : node) (S : snapshot) :
    State node decl name snapshot replica obj writeQuorum readQuorum →
    State node decl name snapshot replica obj writeQuorum readQuorum → Prop where
  | registry {rg rg' disk} :
      ParaleanRegistry.RegistryNext th.registry rg (.commit n S) rg' →
      Guard th disk (.commit n S) → CommitStep th n S ⟨rg, disk⟩ ⟨rg', disk⟩

theorem CommitStep.to_next
    (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (n : node) (S : snapshot)
    (s s' : State node decl name snapshot replica obj writeQuorum readQuorum)
    (ht : CommitStep th n S s s') : Next th s s' := by
  cases ht with
  | registry hr hg => exact Next.registry (.commit n S) hr hg

theorem commit_fresh
    (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (n : node) (S : snapshot)
    (s s' : State node decl name snapshot replica obj writeQuorum readQuorum)
    (ht : CommitStep th n S s s') :
    ParaleanRegistry.current n S th.registry s.registry ∧
      s'.registry.head n = S ∧ s.storage.acknowledged (th.manifest S) = true := by
  cases ht with
  | registry hr hg =>
    have hf := ParaleanRegistry.commit_fresh th.registry _ _ n S hr
    exact ⟨hf.1, hf.2, hg⟩

theorem commit_member_not_stale
    (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (n : node) (S : snapshot)
    (s s' : State node decl name snapshot replica obj writeQuorum readQuorum)
    (ht : CommitStep th n S s s') (d : decl) (hd : th.registry.contents S d = true) :
    s.registry.known n d = true ∧
      ¬∃ e, s.registry.known n e = true ∧ th.registry.ancestors e d = true := by
  cases ht with
  | registry hr hg => exact ParaleanRegistry.commit_member_not_stale th.registry _ _ n S hr d hd

theorem commit_excludes_collision
    (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (n : node) (S : snapshot)
    (s s' : State node decl name snapshot replica obj writeQuorum readQuorum)
    (ht : CommitStep th n S s s')
    (a b : decl) (ha : ParaleanRegistry.isHead n a th.registry s.registry)
    (hb : ParaleanRegistry.isHead n b th.registry s.registry)
    (hn : th.registry.declName a = th.registry.declName b) (hne : a ≠ b) :
    ∀ d, th.registry.contents S d = true → th.registry.declName d ≠ th.registry.declName a := by
  cases ht with
  | registry hr hg => exact ParaleanRegistry.commit_excludes_collision th.registry _ _ n S hr a b ha hb hn hne

end CommitProofs

#print axioms CommitStep.to_next
#print axioms commit_fresh
#print axioms commit_member_not_stale
#print axioms commit_excludes_collision

end ParaleanComposition
