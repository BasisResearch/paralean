# Delivery and convergence

`Paralean/Convergence.lean` proves temporal properties in Lean over the Veil
Registry model. Veil generates the action relations. Lean checks the trace
arguments. No trusted SMT result, new axiom, or incomplete proof is used.

## Trace and fairness

`ParaleanRegistry.Trace` starts from a proved reachable Registry state. Each
successor is a generated `Next` transition or a stutter. The immutable theory
is fixed for the entire trace.

`ReceiveFair` says that, from every cutoff, a receive action that stays enabled
eventually executes. Its guard requires an alive, online node, a durable
publication, and absent local knowledge. The execution is the generated
`receive.ext.tr` relation. Delivery is not a fairness premise.
`receive_enabled_iff` proves that this guard is equivalent to existence of a
generated successor state. `heal_enabled_iff` does the same for Heal.

`HealFair` applies the same condition to the generated Heal action. Heal is
enabled while `stable` is false, and `crash` and `partition` require
`¬stable`. So `HealFair` is not a fairness assumption in the usual sense: it is
eventual permanent stabilisation. After the forced `heal`, no node ever crashes
or partitions again.
Generated transitions preserve stability. Reachability proves that stable
nodes stay alive and online.

The transition bridge proves that publication persists through every action,
knowledge grows after stability, and receive adds its target declaration.
`reachable_safe` supplies `known ⊆ published`.

## Checked results

- `Trace.eventual_delivery`: every published declaration eventually becomes
  known at each node and stays known. No finite declaration universe is needed.
- `Trace.convergence` and `Trace.index_convergence`: finite lists covering all nodes and declarations yield
  one cutoff after which every node's index equals the durable published index.
  Publication quiescence is not assumed. Finiteness supplies a common cutoff.
- `Trace.eventual_collision`: two distinct published declarations with the
  same immutable name eventually remain conflicting heads at every node.
  This requires that no published declaration supersede either head. Later
  explicit resolution would invalidate that premise.
- `conflicting_name_not_current`: Registry's actual `current` predicate rejects
  any snapshot containing a declaration with a conflicting name. Neither head
  can silently become the chosen winner.
- `reachable_stutter_prevents_delivery`: a reachable state with an undelivered
  durable declaration may stutter forever. Being alive and online does not
  force delivery without receive fairness.
- `unfair_scheduler_counterexample`: a concrete anti-entropy projection meets
  publication persistence and permanent readiness but never delivers. This
  projection witness is separate from Registry's initial-state reachability.

The collision conclusion concerns the multi-value index. It does not prove
that a command-line error is emitted, nor that a previously committed snapshot
is retracted after learning a collision.

## Verification boundary

The bridge uses Registry's generated transitions directly. There is no second
anti-entropy transition model. The smaller `DeliveryTrace` interface packages
proved Registry facts for reusable temporal reasoning.

The TLA model and Veil Registry represent the same receive guards, durable
publication, crash/recovery, partition/reconnection, and Heal behavior. The
Veil snapshot sort uses immutable contents; TLA uses declaration subsets.
No machine-checked translation between the two specifications is claimed.
No refinement proof connects either specification to the executable database,
storage adapter, network transport, or Lean artifact checker.

`ReceiveFair` abstracts a scheduler that eventually serves a continuously
enabled receive. `HealFair` is stronger than fairness: it assumes the system
eventually stabilises for good (every node alive and online, no further crash
or partition). Neither gives a latency bound. Convergence is not proved for
runs with crashes or partitions that recur forever. Permanent crashes,
permanent partitions and an unfair scheduler remain permitted by the safety
specification.

The `#print axioms` commands audit the capstones. Permitted foundations are
`propext`, `Classical.choice`, and `Quot.sound` only.
