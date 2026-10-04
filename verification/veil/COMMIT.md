# Commit freshness

`Paralean/Commit.lean` proves properties of the generated Registry commit action.
Freshness concerns the committing node's knowledge immediately before admission.
A later discovery may make an existing checkpoint stale.

- `commit_enabled_iff`: a successor exists exactly when the node is alive and
  online, the selected contents are known, and the snapshot is buildable and current.
- `commit_fresh`: every generated successful commit selects a current snapshot
  and sets the node's head to that snapshot.
- `commit_member_unique_head`: each selected declaration is the unique known
  causal head for its name.
- `stale_member_blocks_commit` and `collision_blocks_commit`: a known descendant
  or conflicting pair prevents committing a snapshot containing the affected name.

These statements include commits that write the existing head. Testing only
`head' ≠ head` would miss a stale repeated commit.

The composition's `CommitStep` retains the generated action label and storage
guard. `CommitStep.to_next` embeds it in the actual composed transition relation.
Its freshness theorem also establishes acknowledgement of the chosen manifest.
The unlabelled state pair alone cannot distinguish a same-head commit from a stutter.

TLA's `CommitFreshness` checks an observational `lastCommitCurrent` field. Each
commit writes its pre-state `Current` result; every other action preserves it.
Mutation checks remove the guard outright or bypass it only for unchanged heads.
Both must violate `CommitFreshness`.

The checker and exporter remain trusted interfaces. Admissibility is conditional
on their predicates; it does not construct source code or establish that required
task targets are present. All theorem axiom audits permit only the standard Lean
foundations.
