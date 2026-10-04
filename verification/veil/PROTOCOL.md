# Completion and discovery after losing local state

`Paralean.Protocol` combines the catalogue-completion and publication-discovery
extensions over one typed store. `Admission`, `Groups` and `Recovery` remain
component specifications. The joint protocol supplies the stronger service
contract.

## Catalogue-backed completion

`CompletionRecovery` carries admission state, catalogue-recovery state and one
storage state. Its finish event requires the actual `Admission.FinishStep` and
a retained catalogue record for the exact snapshot and workspace. The catalogue
invariant establishes acknowledgement of that record, its manifest and every
selected group payload.

`finish_enabled_iff` proves that the extra guard admits completion whenever the
original completion conditions and matching catalogue evidence hold.
`completed_required_target_recovery` carries one checked group witness per
required target through allowed replica destruction and desktop-ID loss. It
establishes surviving catalogue, manifest and payload copies and recovery of the
same immutable snapshot.

`physical_recovery_extends_composed_prefix` constructs three product transitions:
enumerate, reconstruct and select the requested historical record. Recovery reads
the store and scan results. Admission's recorded head/result describe prior work;
they are not inputs to enumeration. The recovery component clears its local
catalogue, selected-ID validity and writer authorisation on desktop loss.

`Recovery.committed` means a durably retained, admitted catalogue record. It also
includes validated staged records adopted by recovery. It is not evidence that
a writer executed the fenced `commit` action. Read-only adoption does not grant
writer ownership.

## Durable publication discovery

The shared storage identity adds a distinct `publication group` constructor.
The joint protocol fixes payload, manifest, catalogue and publication mappings to
these constructors, so objects cannot alias across roles.
Successful publication couples the generated group publish transition with the
generated acknowledgement of its discovery marker. Ordinary storage operations
cannot acknowledge an unpublished marker independently of publication.

The invariant equates acknowledged markers with admitted publications. A physical
scan enumerates marker IDs stored on a read quorum. Acceptance additionally
requires acknowledgement evidence. Staged bytes alone cannot introduce a group.
Quorum intersection proves that every published marker appears in every surviving
complete quorum scan. Accepted IDs are exactly the published group IDs.

Generated receive transitions require this scan evidence. The recovery theorem
remains applicable when every worker's index is empty. Exact dependency IDs and
revision ancestors retain their own discoverable markers.

## Joint transitions and checks

`Protocol` enforces both extensions on the same storage state. Its publication
operation has the generated publish and acknowledgement as internal component
steps. Finish retains the catalogue guard. Recovery operates on that same store.
Other visible operations pair exactly one transition from each component;
arbitrary hidden sequences are not allowed. Admission events and storage events
are distinguished by their constructors, including when their endpoints coincide.
Reachability supplies both component invariants.

`Protocol.completed_required_target_recovery` constructs three joint recovery
transitions after completion and failures. The final reachable state selects the
exact catalogue record and snapshot. Recovery preserves the post-failure writer
and fencing state. `Protocol.Trace.eventual_delivery` and `index_convergence`
project the same joint run to physically guarded discovery and fair anti-entropy.

`ProtocolExecution` starts from the joint initial state. Two workers publish a
two-name helper and its dependent target, persist both publication markers,
accept receipts, and complete after retaining the matching catalogue record.
It then destroys a replica, loses the remembered catalogue ID, and selects the
same snapshot through three joint recovery transitions. The separate
`PublicationDiscovery` execution erases every worker index before rediscovery.

`ProtocolGuardChecks` records the rejected cases independently of the strengthened
guards: the original component finish can lack catalogue evidence or reference
a different image; the original receive can name a publication with no physically
stored marker. The strengthened operations reject those cases.

The checker, exporter, canonical encoding, receipt verification, stable writes,
complete physical enumeration and ownership authority remain interface contracts.
The failure envelope still requires a surviving recovery quorum. Progress still
requires eventual connectivity, recovery and fair service. No implementation,
garbage collector, membership-change protocol or Byzantine store is verified.
