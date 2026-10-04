# Atomic declaration groups

`Paralean/Groups.lean` extends the protocol to immutable atomic groups. Veil generates initialization, all nine actions, labeled `Next`, and their state predicates. Proofs use those generated relations. `ParaleanGroups` holds the group protocol. `ParaleanGroupComposition` couples it to generated durable storage.

## Representation

A group ID identifies its checked package. `member g x` lists every declaration name in that package, including generated declarations. `deps g h` pins exact external group identities. Internal mutual references belong inside the group; they are not external dependency edges. No transition modifies names, dependencies, revisions, or snapshot contents.

`revisions g a x` states that group `g` supersedes `a` for name `x`. Both groups must contain that name. Valid revision ancestry is transitively closed **per name**. The aggregate `ancestors g a` holds exactly when some name has such a revision edge. Admission checks all aggregate ancestors. First-publication rank decreases along every dependency and ancestor edge.

This permits overlapping name sets. Superseding `{x,y}` only for `y` does not supersede its `x` binding. A snapshot still selects whole groups. Selecting a replacement that overlaps an old group excludes that old group entirely. Keeping its unaffected declarations requires a checked replacement group that explicitly provides them. No model operation silently splits a mutual group.

Publication and snapshot contents have one Boolean per group. `PublishedBinding` and `SnapshotBinding` expand that bit through immutable membership. There is no independently mutable publication or snapshot bit for a name. `no_subset_publication` and `no_subset_snapshot` prove that selecting one included name selects every included name.

## Safety

`initial_safe`, nine action preservation theorems, `next_safe`, and `reachable_safe` prove validation, exact dependency closure, known-publication containment, safe checkpoints, and strict dependency ranks. The corresponding ancestor preservation and reachability theorems prove ancestor closure and strict ancestor ranks. `reachable_acyclic` and `reachable_ancestor_acyclic` apply to every nonempty published subset, including infinite subsets.

Additional capstones:

- `snapshot_no_duplicate_name`: distinct selected groups cannot bind the same name.
- `snapshot_exact_dependency`: checkpoint members bring their pinned dependency identities.
- `dependency_path_snapshot_closed`: this closure extends to arbitrary finite dependency paths.
- `dependency_path_conflict_blocks_commit`: conflicts anywhere in two dependency closures reject commit.
- `commit_unique_head_for_every_name`: a successful commit selects the unique local causal head for every name of every selected group.
- `stale_name_blocks_commit` and `overlapping_heads_block_commit`: a stale binding or concurrent overlap rejects commit.
- `next_preserves_historical_snapshot`: later actions preserve an old checkpoint's buildability and publication containment, even after replacing its head pointer.

Freshness belongs to the successful commit event. Later discoveries can make the checkpoint stale. They do not alter its exact contents or dependency meanings.

## Adequacy and execution

`publish_enabled_iff` and `commit_enabled_iff` prove both directions of enabledness against generated actions. Satisfying the guards supplies an actual successor; rejecting every operation cannot satisfy these theorems. `resolved_group_current` derives freshness from per-name resolution of competing known groups. `resolved_group_commit_enabled` supplies its successful commit.

The concrete example uses groups `0={x,y}`, `1={y,z}`, and `2={x,y,z}`. Group 2 supersedes group 0 for `x,y` and group 1 for `y,z`. `overlap_assumptions` checks the complete schema. `overlap_reachable` starts from generated initialization and performs three generated prepare/publication pairs. `overlap_pipeline_success` then performs the actual generated commit and produces a reachable checkpoint binding all three names. This is a registry execution; storage composition has separate general reachability and enabledness proofs.

## Storage and temporal closure

The composition guards group publication with acknowledgement of `payload g` and checkpoint advancement with acknowledgement of `manifest S`. The payload interface denotes the whole group package, including all names and pinned dependencies. The storage validator must enforce that interpretation. It does not store independent logical facts for individual group members.

`ParaleanGroupComposition.initial_safe`, `next_safe`, and `reachable_safe` establish coupling with the generated storage protocol. `published_recoverable`, `checkpoint_declaration_recoverable`, and `checkpoint_manifest_recoverable` provide a live stored copy in every surviving recovery quorum. Their `*_has_copy` counterparts provide a surviving copy without choosing a quorum. `published_ancestor_has_copy` covers revision ancestry. `guarded_commit_enabled_iff` also proves adequacy for the composed labeled commit. `commit_fresh` derives group freshness, the updated checkpoint, and its manifest acknowledgement from that label.

Both namespaces provide generated trace bridges. `Trace.eventual_delivery` requires fair healing and receipt. `Trace.index_convergence` additionally requires finite enumerations covering nodes and groups. Storage steps interleave in the composed trace; projection proves that they preserve the group state. Neither bridge assumes delivery or convergence as a state invariant.

`Trace.eventual_name_collision` requires two **distinct** admitted groups containing a common name and no published per-name descendant of either. Under fair healing and receipt, every node eventually rejects every commit containing that name. The composed theorem rejects `CommitStep` under the same conditions. `eventual_two_heads` is the weaker intermediate head-visibility statement.

## Compatibility and boundaries

`singletonTheory` interprets the existing one-name registry with `member g x ↔ declName g = x`. `singleton_assumptions` transports its schema assumptions. `singleton_buildable_iff` proves exact equality of buildable snapshot meaning. This is an explicit compatible interpretation; a complete implementation refinement between the protocols is not claimed.

The checker, ID encoding, complete generated-name capture, exact dependency extraction, durable payload construction, source capsules, and stock-Lean export remain implementation interfaces. `valid` and `exportable` retain the original abstract contracts. The model requires nonempty valid groups, exact aggregate ancestry, per-name ancestry schema, empty checkpoint contents, and an exportable empty checkpoint. Storage requires write/read quorum intersection and the generated failure envelope. Liveness requires the stated fairness and finiteness conditions.

SMT trust is disabled. Kernel compilation uses the pinned Veil toolchain. No added axioms, incomplete proofs, native evaluation, or trusted SMT results are used. Printed capstone footprints contain only `propext`, `Classical.choice`, and `Quot.sound`.
