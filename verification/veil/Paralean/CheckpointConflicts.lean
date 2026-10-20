import Paralean.Groups

/-! OPEN-26 at the generated, storage-coupled commit label. The registry's
current check is universal over every selected group and every declared name;
an unrelated second head therefore blocks any snapshot containing either.
Buildability independently forbids selecting both atomic groups. -/

set_option veil.smt.trust false

namespace ParaleanCheckpointConflicts
open ParaleanGroups ParaleanGroupComposition

variable {node group name snapshot replica obj writeQuorum readQuorum : Type}
  [DecidableEq node] [Inhabited node]
  [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name]
  [DecidableEq snapshot] [Inhabited snapshot]
  [DecidableEq replica] [Inhabited replica]
  [DecidableEq obj] [Inhabited obj]
  [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum]

theorem either_unresolved_head_blocks_commit
    (th : ParaleanGroupComposition.Theory node group name snapshot replica obj writeQuorum readQuorum)
    (s s' : ParaleanGroupComposition.State node group name snapshot replica obj writeQuorum readQuorum)
    (n : node) (S : snapshot) (a b g : group) (x : name)
    (ha : ParaleanGroups.isHead n a x th.registry s.registry)
    (hb : ParaleanGroups.isHead n b x th.registry s.registry)
    (hne : a ≠ b)
    (hg : th.registry.contents S g = true)
    (hx : th.registry.member g x = true) :
    ¬ParaleanGroupComposition.CommitStep th n S s s' := by
  intro hstep
  exact ParaleanGroups.overlapping_heads_block_commit th.registry
    s.registry s'.registry n S a b g x ha hb hne hg hx
    (ParaleanGroupComposition.CommitStep.registry_transition s s' n S hstep)

theorem every_unresolved_checkpoint_rejected
    (th : ParaleanGroupComposition.Theory node group name snapshot replica obj writeQuorum readQuorum)
    (s : ParaleanGroupComposition.State node group name snapshot replica obj writeQuorum readQuorum)
    (n : node) (S : snapshot) (a b : group) (x : name)
    (ha : ParaleanGroups.isHead n a x th.registry s.registry)
    (hb : ParaleanGroups.isHead n b x th.registry s.registry)
    (hne : a ≠ b)
    (contains_conflict : ∃ g, th.registry.contents S g = true ∧
      th.registry.member g x = true) :
    ¬∃ s', ParaleanGroupComposition.CommitStep th n S s s' := by
  rintro ⟨s', hstep⟩
  obtain ⟨g, hg, hx⟩ := contains_conflict
  exact either_unresolved_head_blocks_commit th s s' n S a b g x ha hb hne hg hx hstep

#print axioms every_unresolved_checkpoint_rejected
end ParaleanCheckpointConflicts
