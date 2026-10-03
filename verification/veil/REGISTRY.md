# Registry safety

`Paralean/Registry.lean` is a Veil model, not a parallel handwritten transition system. `#gen_spec` generates its initializer, actions, labeled `Next`, and verification predicates. All proofs use those generated definitions.

The kernel checks `initializer_safe` and every action's successful-execution safety condition. `next_safe` transfers those proofs to generated `Next`. `reachable_safe` inducts over initial states, generated transitions, and stuttering.

Consequences:

- `published_valid`: every durable declaration passed the abstract validator.
- `published_closed`: every dependency identity is durable.
- `known_published`: receipt and local publication never expose an unpublished declaration.
- `snapshot_safe`: every committed snapshot is valid, dependency-closed, name-compatible, exportable, and contained in durable publication.
- `reachable_acyclic`: every nonempty subset of published declarations has a member with no dependency inside that subset. This matches TLA `Acyclic`; it also holds for infinite subsets.
- `collision_blocks_current`: two distinct causal heads sharing a name block selecting a current version of that name. Names never select a winner by clock order.

## Correspondence

Veil Boolean relations represent TLA sets. Node and declaration sorts are unrestricted inhabited types. The `decl` sort denotes revision/package identities (`RevisionID`), not content-only `DeclID`. A content ID deduplicates declaration content. A revision ID includes the content ID and causal parents, allowing reverts to preserve a new causal history. Dependencies, causal ancestors, declaration names, and validator results are immutable theory fields.

Veil uses a `snapshot` sort with immutable `contents` and `exportable` relations. TLA sets correspond to snapshot values whose contents are those sets. Taking the snapshot sort as declaration subsets recovers TLA's snapshot domain. Different snapshot values may denote the same set; safety does not require extensional equality. The snapshot assumptions assert that `emptySnapshot` has empty contents and is exportable. The validator schema contract additionally requires each valid revision's ancestors to share its name and contain every ancestor's own ancestors. This enforces same-name causal ancestry and transitive closure; it does not assume admission safety.

`head` stores a snapshot value. Crashes preserve that value and publication; they clear volatile `known` and `pending`. Receipt may arrive before local dependencies. Commit checks local containment, closure, compatibility, exportability, and current causal heads. Later publication may make an existing snapshot stale. Its exact contents remain safe.

Ghost `clock` and `rank` record first publication order. A first publication records the previous clock and advances it. Repeated publication leaves the rank unchanged. Erasing these fields gives the TLA actions. They introduce no action guard, network coordination, storage assumption, or numerical quorum argument. The invariant proves strict rank decrease along admitted dependencies. Natural-number well-founded induction proves TLA's subset definition of acyclicity.

## Proof boundary

`valid` is the abstract checker interface. The proof does not verify Lean's checker, content-address construction, storage durability, export tooling, or implementation/model refinement. The ancestry schema contract is a trusted validator obligation. No validator theorem assumes admission safety. Dependency identities are immutable model inputs; each admission verifies that its dependencies were already locally known. Durable-store success is the `Publish` linearization point. Storage failure assumptions belong to the durability model. End-to-end crash durability additionally requires the coupled model connecting registry publication to acknowledged storage and snapshot commit to an acknowledged manifest; separate component proofs do not establish that connection.

SMT trust is disabled. No SMT verdict is used as a proof. The audited theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. No incomplete proofs or added axioms are permitted.
