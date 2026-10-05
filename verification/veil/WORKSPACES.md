# Transparent workspaces: placement and names

`Paralean.Workspaces` (`ParaleanWorkspaces`) layers the "Transparent workspaces" rules of
`docs/architecture.md` over the Groups registry: `Next s t := (∃ l, GroupsNext th s l t) ∧ Guard L th s t`.
Groups is unchanged. `reachable_groups` transfers every Groups theorem.

## Model

`Layout`: immutable `fileOf`, `anchor : group → Option group`, Lamport `ts`, `author`, an
injective author tie-break `tie`, a `tombstone` flag and an enumeration `univ`. Assumed:
`key_inj` (`(ts, author)` identifies a group, so no node reuses a Lamport time; this is not
derivable because crashes wipe `known`). Revision ancestry is the Groups theory's `ancestors`
(per name: `revisions`). A tombstone is a deletion: a revision that supersedes its ancestors
and is never rendered.

`Guard` has two parts.

- `StageGuard`: a newly pending `pending n d` needs `Staged`: the anchor is a lineage root (no
  ancestors) of the same file that `n` knows or has itself pending; `ts e < ts d` for every `e`
  that `n` knows or has pending; `author d = n`; every revision ancestor is known and in the
  same file; and every same-file dependency `e` satisfies `PosLt e d` (it renders above `d`).
- `PublishGuard`: a group newly published from `n`'s pending bit has an anchor that `n` knows.
  An anchor that was `n`'s own pending group is therefore published first.

`staged_local`: staging reads only `n`'s known and pending sets and immutable data; publication
reads only the publisher's known set. `guard_stutter` and `receive_guard`: receives are never
blocked.

Positions. `path d` is the root-first list of keys down the anchor chain and `Prec` the RGA
order on it (a proper prefix first, otherwise the larger key at the first difference first).
`root d` is the minimum-key group among `d` and its ancestors. `PosLt` orders groups by
`Prec` of their roots, then by own key, oldest first. `Live K d`: `d` is known, not a tombstone,
and no known group has it as an ancestor (for any name). `render L th K f` is `univ` sorted by
`PosLt`, filtered to the live groups of `f`.

Records carry their positions. `Carried`/`carried d` is what `d`'s record holds: file, key,
tombstone flag, revision-ancestor IDs, names, dependency IDs, the anchor path of its lineage
root (`path (root d)`) and its lineage key per name (`lkey x d`). The author computes the last
two at staging from groups it knows or has pending. `AgreeOn L L' th th' K`: two layouts and
theories give equal `carried d` for every `d` in `K`; they may differ arbitrarily elsewhere.

Names. `lroot x d` is the minimum-key group among `d` and the groups it revises for `x`;
`lkey x d` its key. `Cand K x d`: `d` is `Live` in `K` and declares non-target `x`. A group
revised for one of its names only (Groups' `valid_ancestry` allows revising `{foo, bar}` for
`foo`) is superseded and holds none of its names. The winner is the candidate least under
`LinLt` (lineage key, then own key within one lineage). `renamed` gives `x` to the winner and to
target names, and `fresh x d` otherwise. `Naming` has a `reserved` namespace (for example a
prefix the elaborator rejects in user source): `fresh` is injective and always reserved, and
environment or imported names (`env`) are not reserved. `NamesChecked N` is the per-group
admission check: a valid group declares (`declared`, public or scoped, which includes
`member`) no reserved name. It reads only that group, so nothing is assumed about groups
declared in the future.

There is no source text in the model. A rendered declaration (`RenderedDecl`) is its ID, its
rendered names and its pinned dependency IDs. The intended implementation regenerates the
projection from each declaration's elaborated statement and pinned dependency IDs, so a rename
is a re-render, not a textual substitution. `remote% <declID>` elaboration checks the registry
binding of the ID (statement, dependencies, receipt), not the rendered name, which is a local
binding of that ID.

## Results

Order and rendering:

- `prec_strict_total_order`, `posLt_strict_total_order`: strict total orders.
- `render_pairwise`, `render_nodup`, `render_mem` (rendered iff live and in `f`),
  `render_unique` (any strictly `PosLt`-sorted list of exactly the live groups of `f` is the
  render), `tombstone_not_rendered`, `superseded_not_rendered`.
- `render_order_stable`: two groups rendered under both `K` and `K'` have the same relative order.
- `render_sublist_live`: the old render, filtered to groups still live in `K'`, is a sublist of
  the new render. `render_disappears`: if `K ⊆ K'` and `d` leaves the render, `K'` newly
  contains a revision or tombstone with `d` as an ancestor.
- `revision_root`, `revision_in_place`: a revision whose ancestry is exactly `w` and `w`'s
  ancestry, and which is newer than `w`, has `w`'s root, so it takes `w`'s place relative to
  every other lineage.
- `anchor_closed`, `ancestors_closed` (invariants over the real `Next`): a published group's
  anchor and revision ancestors are published, in the same file and older. A pending group's
  anchor is published or the author's own pending group (`Inv`); `groups_pending_cleared`: a
  pending bit is cleared only by publishing that group or by a crash of the node.
  `reachable_wf_known`, `reachable_wf_published`: known and published sets are valid and newer
  than their ancestors. `path_published`, `known_anchor_published`.

Locality (records carry their positions):

- `posLt_iff_paths`, `linLt_iff_keys`: the render and winner orders compare carried root paths,
  lineage keys and keys only.
- `live_carried`, `render_carried`, `renamed_carried`, `view_carried`: if `AgreeOn L L' th th' K`
  (and the naming parameters agree; for `view_carried` also snapshot membership), the render,
  the names and the whole `View` of `K` are equal. Rendering never reads an unknown anchor or
  ancestor, although Groups' `receive` is not causal. Convergence (`eventually_identical`) is
  unchanged: `View` is a function of the known records.

Insertion and dependencies:

- `staged_pos_iff`: for a fresh insertion `d` (no ancestors), a group `x` known or pending at
  the author at staging satisfies `PosLt x d` iff `x`'s root is the anchor or precedes it
  (`Above`).
- `intention_preserved` (both sides): in every render containing `d` and a group `x` that the
  author knew or had itself pending at staging, `x` precedes `d` if `Above d x`, and `d`
  precedes `x` otherwise. So an author's own unpublished groups keep the intended order.
  `insert_after_anchor`: the same for the author's render of its known set plus `d`.
- `deps_precede`: a same-file dependency precedes the dependent group in every render showing
  both (immediate from the guard's `PosLt` clause).

Names:

- `winner_eq_some`, `winner_exists`, `names_unique` (non-target names of valid groups, under
  `NamesChecked`), `fresh_not_declared`, `fresh_env`, `renamed_env` (a rendered name that is an
  environment name is the declared name itself).
- `revise_winner_keeps_name`: if `w` wins `x` in `K` and a non-tombstone `r` revises `w` for
  `x` (with `K ∪ {r}` well formed and `r` not already superseded in `K`), the winner in
  `K ∪ {r}` is `r` or has `w`'s lineage root.
- `winner_change_explained`: if `K ⊆ K'` (well formed) and the winner's lineage root changes,
  then `K'` newly contains a group declaring `x` with lineage key strictly below the old
  winner's; or newly contains a tombstone that revises the old winner; or the newest member
  `m` of the old winner's `x`-lineage in `K'` is superseded by a group `e` that revises it for
  another name only, with `e` or `m` new.

Definitional or corollary (not guarantees about source text):

- `render_function`, `names_agree`: rendering and naming are functions of the known set (by
  rewriting with the hypothesis).
- `rename_preserves_deps`: `renderDecl` keeps ID, dependencies and snapshot data (by `rfl`).
- `eventually_identical`: Groups' index convergence (`HealFair`, `ReceiveFair`) rewritten
  through `View`, which is a function of the known set.

`Example` (nodes A, B; groups 0 to 3 in one file, all reachable under the guard): A and B
concurrently insert 1 and 2 after 0, both declaring name 0, and receive them in opposite
orders (`arrival_orders`, `arrival_render_diverges`). Group 1 wins (`collision_resolved`;
2 renders as `fresh 0 2`). A then revises 1 with 3. Both render `[0, 2, 3]`: 3 replaces 1
in 1's place (`final_render`). The winner of name 0 is 3, although 2's own key is below 3's
(`revised_winner_keeps_name`). `stage_follows_anchor`, `final_dep_precedes` exercise the
guard; `dep_guard_needed` shows a layout with 1 anchored at the file start renders 1 above its
dependency 0 and is rejected. `delete_frees_name`: with 3 a tombstone, the render is `[0, 2]`
and the name passes to 2.

Necessity witnesses for the hardening:

- `partial_revision_frees_name`: group 0 declares names 0 and 1; group 1 revises it for name 0
  only; group 2 declares name 1. Group 0 is not rendered. Under the old candidate rule
  (`OldCand`, unrevised for that name) 0 is a candidate for name 1 and beats 2 on lineage key,
  so no rendered declaration would carry name 1. With `Live` in `Cand`, 2 wins and keeps it.
- `own_pending_anchor`: node A publishes 0, stages 1 after 0, then stages 2 after 1 while 1 is
  only pending (`o3.known false 1 = false`). The old guard (anchor known) rejects that staging,
  so A could only anchor 2 at 0, where the newer sibling renders first (`[0, 2, 1]`). Now the
  final render is `[0, 1, 2]` and `intention_preserved` places 1 above 2 in every render. The
  whole trace is reachable under the guard (`o_r6`).
- `publish_guard_needed`: from the state with 1 and 2 pending, Groups can publish 2 before 1.
  `StageGuard` accepts that step; `PublishGuard` rejects it; otherwise 2 would be published
  with an unpublished anchor.
- `render_reads_unknown_anchor`: two layouts agree on file, anchor ID, key and tombstone of the
  known groups 1 and 2 and differ only on the unknown anchor 0 of 1; they render `{1, 2}` as
  `[2, 1]` and `[1, 2]`. A record's own fields do not determine the render; the root path must
  be carried (`render_carried`).
- `reserved_check_needed`: if valid group 0 may declare `8 = fresh 0 2`, group 2 loses name 0,
  renders as 8, and 0 keeps 8: two declarations render to one name. `ex_names_checked`: the
  main example passes the check.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.

## TLA+ (`verification/tla/Workspace.tla`)

Three agents (one receive-only), two files, five declarations: `a1` declares `foo` and
`bar`, `a1` and `b1` collide on `foo`, `a3` revises `a1` for `foo` only, `a2` declares `bar`,
`b2` is a tombstone of `a2`. A declaration has a primary name `Name[d]` and extra names
`Also[d]`; a revision revises for the primary name. Invariants `SameKnownSameRender`,
`NameAgreement`, `AnchorBefore`, `NoSupersededRendered`, `NamesUnique`, `NameHeld` (a name
declared by a rendered declaration is kept by a rendered declaration); action properties
`RenderStable`, `DisappearOnlySuperseded`, `IntentionPreserved`, `WinnerLineageKeepsName`;
liveness `EventuallyIdentical` under one weak-fairness condition on receives. 23,932
distinct states. Coverage witnesses `NeverWinnerRevised`, `NeverPartialRevisionFreed` (after
`a3`, `a2` holds `bar` although `a1` is older) and `NeverDeleted` are expected to fail.
Mutation `workspace_superseded_holds_name` (heads for a name exclude only declarations revised
for that name) violates `NameHeld`. Receive in the TLA model is causal for anchors and revision
ancestors, and publication is atomic (no pending state), so the own-pending anchor rule is
covered by the Lean witnesses only.

## Not established

- `known` is not anchor- or ancestor-closed: Groups' `receive` may deliver `d` before its anchor
  or ancestors. Rendering reads only carried record data (`render_carried`), so a group whose
  anchor or root is unknown renders at its carried position. The implementation must store the
  root's anchor path and the per-name lineage keys in each record and must not recompute them
  from other records. Delivery order is still not causal; a reader may show a revision whose
  revised group it has not received.
- `intention_preserved` and `insert_after_anchor` cover fresh insertions only. For revisions the
  statement is `revision_in_place`, which assumes the revision's ancestry is exactly the
  revised group's history; a merge revision takes the least root of what it merges.
- Intention is stated at staging (`prepare`), where the guard is checked. A node that learns a
  newer sibling before `publish` sees `d` below that sibling. The order itself is unaffected.
- The dependency clause orders positions; it does not model Lean's scoping or `remote%`.
- `winner_change_explained` and `revise_winner_keeps_name` need the known set to be well formed
  (`WF`), which holds for reachable known and published sets.
- The publication guard can delay a group behind its author's own pending anchor. No liveness
  is claimed for it beyond the author eventually publishing in order.
- `NamesChecked` is a validation rule; the renderer's namespace (`reserved`) and that imports
  never use it (`env_unreserved`) are assumptions about the name encoding.
- Target names keep `x` for every declaration. Their uniqueness is TargetNames' owner rule.
- Collisions with environment or imported names are not resolved: `fresh` avoids them, but a
  declared name equal to an imported name is not renamed.
- Bytes are modelled as `View`. Canonical whitespace, the `remote%` text, drafts, git
  projection and timing of writes into working copies are not modelled.
