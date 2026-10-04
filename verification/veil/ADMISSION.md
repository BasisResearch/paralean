# Coupled receipt and completion

`Paralean/Admission.lean` couples generated packet actions to the generated atomic-group/storage protocol. `ParaleanAdmission.Next` is the product relation. It preserves both component safety invariants from their initial states. `reachable_protocol_projection` proves that every product execution is an actual guarded group/storage execution.

`protocolTheory` uses `ParaleanArtifacts.Object.payload g` and `Object.manifest S` as its **actual** storage maps. These constructors make payload IDs injective and payload/manifest kinds disjoint. `Object.catalog` supplies a separate namespace for numeric recovery-record IDs in the same store. `Compatible` equates the delivery and registry validator, dependency, membership, checkpoint-content, and exportability fields. No manufactured registry replaces the actual protocol state.

## Receipt

An `AcceptStep` pairs the generated `Delivery.accept` with generated group receipt. An already-known group permits a duplicate response without another group update. Packet validity, signed receipt fields, recipient, current request, and request epoch must all match. The receipt binds the exact packet group; a request can accept different groups satisfying its fixed contract.

`accept_published_durable` proves that successful acceptance makes that exact packet group locally known, published, acknowledged as a typed payload, and backed by a surviving stored copy. `accept_checked_realizes` proves that the checked object realizes the precise current request. `accept_enabled_iff` proves both enabledness directions: an admissible packet succeeds when the group is already known or its generated receipt is enabled.

`corrupt_rejected` and `stale_rejected` inherit the checked packet rejection rules. Send/drop labels carry no receipt-admission evidence. A state pair can match more than one action; the named event supplies the relevant guards.

## Worker crash

Passive protocol transitions exclude the generated group crash. The product crash pairs generated group crash with generated delivery cancellation. `CrashStep` is its labeled event. Cancellation increments the epoch and clears active/accepted/completion flags. Recovery can restore the group worker but leaves the delivery request inactive. A new request start is required before response admission.

`crash_epoch` and `crash_rejects_old_response` prove that a packet carrying the pre-crash epoch cannot be accepted after the coupled crash. This closes the same-node crash/recovery replay path; recipient binding alone would not close it.

## Completion

`Delivery.done` is a component observation. The authoritative product completion event is `FinishStep`. It pairs generated `Delivery.finish n S` with the actual `GroupComposition.CommitStep n S`, at the same state pair and for the same immutable checkpoint.

`finish_complete_current_durable` proves the resulting completion flag and result, the actual checkpoint head, unique current bindings before commit, acknowledged typed manifest, and realization of **every** immutable required request. `finish_required_groups` supplies a selected checked group for each target. `finish_all_groups_durable` gives publication, typed payload acknowledgement, and a surviving copy for every selected group. `finish_required_targets_durable` ties membership, checked status, contract satisfaction, publication, acknowledgement and a surviving copy to the same group witness for each target.

`finish_enabled_iff` proves that satisfying delivery readiness, group knowledge/buildability/freshness, worker readiness, and manifest acknowledgement supplies an actual product successor. `empty_cannot_finish` rejects an empty checkpoint when a required request exists. A component-only candidate finish is not evidence of `FinishStep`.

## Boundaries

The receipt verifier, request encoding, checker, complete atomic-group capture, storage writes, ID encoding, and export tool remain implementation interfaces. The model equates both components' immutable artifact meanings; an implementation must preserve those equalities. Receipt verification authenticates the signed request, object, epoch, and recipient. Object constructors prove abstract namespace separation; they do not establish hash collision resistance.

The group/storage failure envelope and quorum assumptions remain unchanged. Temporal guarantees are available through the projected group/storage execution; this module establishes finite-prefix safety and event adequacy.

`AdmissionExecution.lean` proves `combined_receipt_commit_disk_failure`. One
connected execution writes and acknowledges a two-name helper group and its
dependent target, prepares and publishes both, accepts both signed receipts at
a second worker, stores and acknowledges the manifest, and performs the paired
completion/commit. It then destroys a replica that stored and acknowledged both
payloads and the manifest. The other replica retains all three objects. The final
checkpoint still contains both checked groups and completes the nonempty task.
The theorem includes the connected paths, both named acceptance events, the named
completion event, and the generated disk-loss transition.

The pinned remote Lean/Veil build checks this module. Printed capstone footprints use only `propext`, `Classical.choice`, and `Quot.sound`. No incomplete proofs, added axioms, native evaluation, or trusted SMT results are used.
