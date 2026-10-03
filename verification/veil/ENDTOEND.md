# Coupled protocol liveness

`Paralean/EndToEnd.lean` connects the guarded Registry/storage composition to
the existing temporal proofs.

`next_registry_projection` inspects the actual `Composition.Next` constructors.
A Registry action projects to the generated Registry action. A storage action
projects to a Registry stutter. The acknowledgment guards on publication and
checkpoint advancement remain enforced by the composed transition.

`reachable_registry_projection` proves the same correspondence for reachable
states. `Trace.toRegistryTrace` constructs a Registry trace from a composed
trace, including its initial reachability and every successor transition.

The transferred results are:

- `Trace.eventual_delivery`: an already-published declaration eventually stays
  known at each node.
- `Trace.index_convergence`: finite covering lists of nodes and declarations
  yield eventual permanent equality of every node's index and publication set.
- `Trace.eventual_collision`: distinct same-name published heads eventually
  remain conflicting at every node, provided no published descendant supersedes
  either head.
- `Trace.durable_delivery`: publication also retains a live storage copy at
  every later time, using the proved coupling and storage invariants.

`HealFair` and `ReceiveFair` are explicit fairness predicates on the projected
generated Registry actions along the composed timeline. Storage actions may
interleave indefinitely, but cannot starve a continuously enabled receive.
The fairness predicates require action execution. They do not assume delivery.

No fairness of storage writes is needed for already-published declarations.
Publication already requires a storage acknowledgment. These theorems make no
promise that every draft is written, acknowledged, or published.

This is a proof of the composed abstract protocol. It does not establish
refinement to the executable database, network transport, or storage adapter.
The storage failure envelope and immutable Registry theory assumptions remain
explicit premises. The axiom audits permit only Lean's standard foundations.
