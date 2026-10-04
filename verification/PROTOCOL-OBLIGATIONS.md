# Protocol proof obligations

This extension addresses the protocol gaps identified in the review of the
README and implementation plan. Each completed claim requires a checked consumer
over the actual generated transitions, an explicit assumption boundary and a
nonempty execution or enabledness theorem.

| Obligation | Proof or check |
|---|---|
| Atomic groups with overlapping name sets | `Groups`: membership, per-name causal heads, closure and group commit |
| Preserve storage and convergence when using groups | `ParaleanGroupComposition`: generated component transitions and trace projection |
| Reject corrupt, stale, misaddressed and mismatched responses | `Delivery`: exact packet/receipt/request/node/epoch checks |
| Reject empty or incomplete task completion | `Delivery`: every immutable required contract must have a selected checked result |
| Allow different proofs of one fixed target | `DeliveryAlternatives`: two distinct accepted objects complete the same required request |
| Bind completion to actual durable/current commit | `Admission`: paired finish and guarded group commit |
| Require a discoverable catalogue entry before completion | `CompletionRecovery`: same-store catalogue guard, exact image/workspace, required-target recovery after failures |
| Rediscover publications after every worker index is erased | `PublicationDiscovery`: durable typed markers, physical quorum scan, guarded generated receive |
| Enforce catalogue and discovery guards together | `Protocol`: shared-store composition of both extensions |
| Exercise both guards before loss and recovery | `ProtocolExecution`: joint initial state, helper/target publication markers, matching catalogue, completion, disk/desktop loss and exact recovery |
| Exercise necessity of the new guards | `ProtocolGuardChecks`: missing catalogue, mismatched image and absent publication-marker regressions |
| Invalidate pending responses on actual worker crash | `Admission`: paired group crash and delivery cancellation |
| Prevent package/manifest object aliasing | Typed constructors consumed by `Admission.protocolTheory` |
| Lose the local checkpoint ID and recover through a catalog | `Recovery`: physical quorum scan, candidate validation, causal reconstruction and selection |
| Handle staged catalog entries and stale writer tokens | `Recovery`: admission/re-acknowledgement and fencing |
| Reconstruct history from recorded parents | `RecoveryAncestry`: exact parent-path ancestry, head and conflict equivalences |
| Combine receipts, group admission, completion and disk loss | `AdmissionExecution`: connected two-worker execution, dependent target, two-name helper group and surviving copies |
| Exercise failure after useful work | `CheckpointReuse`: acknowledge, commit, destroy an acknowledged replica, crash/recover and recommit |
| Test the original registry's effective admission/freshness guards | [Guard matrix](TLA-GUARDS.md), including independent closure/exporter oracles |

The README distinguishes abstract protocol proofs from implementation correctness.
The remaining implementation contracts are the Lean checker and exporter,
signature/integrity verification, canonical encoding and ancestry-schema decoding,
complete physical catalogue/marker enumeration, stable writes and exclusive ownership service. Those contracts must
be implemented and tested before applying these results to a distributed service.

The failure envelope still requires a surviving recovery quorum. New acknowledgements
need a usable write quorum. Eventual delivery requires eventual recovery/connectivity
and fair service. Finite global convergence requires finite worker and revision
universes. Proof search termination, speedup, Byzantine storage, dynamic membership
and garbage collection are not established by these protocol extensions.
