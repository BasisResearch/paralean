# General recovery adequacy

`Paralean/RecoveryAdequacy.lean` imports the coupled recovery model. It proves recovery is usable for every committed historical checkpoint, beyond the concrete execution witness.

`physical_historical_recovery_adequate` starts from `CoupledSafe`, any committed record `c`, a surviving recovery quorum, and a complete physical scan whose readiness matches actual acknowledged record/manifest/payload storage. It constructs three actual `CoupledNext` transitions. Its statement also records their exact generated labels:

1. `enumerate v` discovers the checkpoint and its admitted causal closure.
2. `reconstruct` computes the causal heads and conflict observation.
3. `historical c` selects exactly the requested committed checkpoint.

The resulting state preserves the original writer flag, fence, and storage state. Historical selection may preserve an unresolved conflict. Recovery does not acquire a writer lease.

`committed_admissible_from_physical_scan` derives admissibility from physical coverage, storage readiness, and the proved `Records` invariant. It uses committed-ancestor closure to discharge the entire causal-closure condition. Admissibility is not an extra premise on `c`.

`physical_enumeration_enabled_with_label` exposes the generated enumeration label alongside the existing enumeration interface. `reconstruction_enabled_for_known_record` and `historical_enabled_for_known_record` construct deterministic successor states and prove their generated action relations.

`reachable_physical_historical_recovery` extends any reachable execution prefix through this path. It supplies a reachable selected checkpoint, unchanged authorization/storage, and surviving copies of its catalog record, manifest, and every selected atomic-group payload.

The scanner must supply a complete hash-validated scan value and the stated readiness interpretation. The theorem does not implement the scanner or promise delivery during a partition. Its action-existence proof uses no temporal fairness assumption. Quorum intersection, metadata compatibility, object-role separation, and the existing failure envelope remain the recovery model's assumptions.

The pinned Lean/Veil compiler checks all capstones. Their axiom footprints contain only `propext`, `Classical.choice`, and `Quot.sound`. No incomplete proofs, added axioms, native evaluation, or trusted SMT results are used.
