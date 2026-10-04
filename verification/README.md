# Verification scope

The checked subject is the abstract distribution protocol. The production Lean
fork, serializer, validator service, source exporter, object-store adapter and
LSP transport are not implemented or verified here.

## Models

- [Registry](tla/Registry.tla): private preparation; validated publication;
  immutable dependencies; admitted causal ancestry; causal name heads; conflicts;
  compatible checkpoints and freshness at commit time;
  crash/recovery, partitions and eventual anti-entropy.
- [Durability](tla/Durability.tla): stable object writes, write-quorum acknowledgements,
  permanent replica loss and recovery-quorum intersection.
- [Publication](tla/Publication.tla): composition. Publication requires an acknowledged
  package; checkpoint advancement requires an acknowledged manifest. Storage steps
  leave registry state unchanged and vice versa.

Quorums are sets with a supplied intersection member. No numeric majority formula
is used. TLC instantiates three replicas and intersecting two-member sets; Veil
proofs quantify over abstract quorum and replica types.

The registry's `Decls` are immutable revision/package identities. Separate content
deduplication permits reverts without reusing obsolete revision identities.
Valid ancestry must have the same name and be transitively closed. The TLA and
original Veil registry have one name per record. The additional Veil `Groups`
model handles overlapping multi-name groups, per-name revision ancestry and
whole-group snapshots. Capturing complete Lean groups and frontend capsules
remains an implementation obligation.

## TLC results

Exhaustive finite-state checks ran on the AWS development box with TLA tools
1.7.4, OpenJDK 25 and eight TLC workers. These are full reachable-state searches
for the listed finite instances, not proofs for arbitrary cluster sizes.

| Scenario | Configuration | Distinct states | Checked properties |
|---|---|---:|---|
| Chain | 2 workers, 3 revisions | 125,232 | Admission, closure, acyclicity, snapshots |
| Collision | 2 workers, 2 conflicting revisions | 15,928 | Safety, fair delivery, convergence, eventual collision |
| Revision | 2 workers, upstream edit and old consumer | 174,512 | Safety and no retargeting |
| Revert | 2 workers, 3 sequential revisions | 99,756 | Revert is a new head; no false conflict |
| Rejected | 2 workers, bad proof and cyclic pair | 17 | Nothing invalid/circular admitted |
| Quorums | 3 storage replicas, 2 objects | 439 | Recovery and no acknowledged data loss |
| Integrated | 1 worker, 3 replicas, package/checkpoint objects | 89,428 | Guarded publication and checkpoint recovery |
| CheckpointReuse | Committed checkpoint, acknowledged-replica loss, worker restart | 43,888 | Surviving copies and repeated commit |
| ExportRejected | Closed snapshot rejected by exporter | 22 | Export rejection despite dependency closure |

The suite explores 549,222 distinct states across separate scenarios. Fingerprint
collision estimates, seeds, timings and state counts are retained in the raw logs.
No symmetry reduction or state/depth constraints hide behaviors.

Eight reachability witnesses establish full B→A→B dependency-chain commitment,
dependent publication, collisions, acknowledgements, disk loss, integrated
commitment, checkpoint reuse after loss and admission despite export rejection.
Twenty mutations exercise admission, ancestor closure, freshness, acknowledgement,
fairness, storage guards, name selection, exportability and useful work.
The harness requires the intended invariant/temporal error, not merely nonzero exit.
The deliberately over-restrictive model must lose both dependent-work witnesses.
The [guard matrix](TLA-GUARDS.md) records effective guards and redundant ones.
Closure and exporter mutations use independent property oracles.

Freshness is checked at every commit, including a repeated commit to the same
checkpoint. TLA records the pre-state `Current` result in observational ghost
state. Later discoveries may make the stored checkpoint stale without violating
this property. Deleting either the ancestry guard or the freshness guard produces
the corresponding counterexample.

The design iteration caught two specification-level gaps: revisions needed distinct
identity from content; and independent storage/registry models lacked acknowledgement
coupling. Revert and integrated cases cover the repaired design. Syntax/tooling
failures were corrected before accepting runs.

## Veil and Lean proofs

Veil is pinned to `d05518f22076b8cc84fb2d2b74d196aa979bfe8f`, using Lean 4.32.0.
This is independent of the proposed fork's nightly compiler. GPT Sol agents authored
the proof modules; the Lean kernel, not agent or SMT assertions, checks their proofs.

| Module | Guarantees |
|---|---|
| [Registry](veil/Paralean/Registry.lean) | Generated-action preservation, dependency and ancestor closure, acyclicity of both relations, immutable compatible snapshots |
| [Durability](veil/Paralean/Durability.lean) | Generated-action preservation, live quorum intersection retains every acknowledged object |
| [Convergence](veil/Paralean/Convergence.lean) | Delivery and convergence over generated registry traces; fixed unsuperseded conflicting pair eventually diagnoses |
| [Composition](veil/Paralean/Composition.lean) | Actual generated component transitions with storage guards; published packages and checkpoint contents/manifests retain recoverable copies |
| [EndToEnd](veil/Paralean/EndToEnd.lean) | Trace projection, temporal guarantees, composed ancestor closure/acyclicity and surviving ancestor packages |
| [Commit](veil/Paralean/Commit.lean) | Generated commit admissibility iff its guards hold; pre-state freshness, exclusion of stale/conflicting members, guarded composition |
| [Groups](veil/Paralean/Groups.lean) | Atomic multi-name groups, per-name heads, dependency-path conflicts, overlap resolution, storage composition and fair convergence |
| [Delivery](veil/Paralean/Delivery.lean) | Request/receipt/object/recipient/epoch binding, cancellation, required-target completion and a nonempty execution |
| [DeliveryAlternatives](veil/Paralean/DeliveryAlternatives.lean) | Two distinct result objects complete the same immutable required contract |
| [Admission](veil/Paralean/Admission.lean) | Receipt acceptance and completion paired with actual group/storage transitions; durable required targets and crash invalidation |
| [AdmissionExecution](veil/Paralean/AdmissionExecution.lean) | One connected two-worker run with atomic helper admission, dependent target receipts, durable completion and subsequent replica destruction |
| [Recovery](veil/Paralean/Recovery.lean) | Lost-ID catalog recovery, staged-record validation, causal reconstruction, historical selection and fencing |
| [RecoveryAncestry](veil/Paralean/RecoveryAncestry.lean) | Ancestry equals parent-path reachability; reconstructed heads and conflicts follow recorded parents |
| [RecoveryAdequacy](veil/Paralean/RecoveryAdequacy.lean) | A complete recovery path exists for every previously committed record given a surviving quorum scan |
| [PublicationDiscovery](veil/Paralean/PublicationDiscovery.lean) | Durable publication markers, physical quorum discovery after all worker indexes are erased, staged-marker rejection and fair convergence |
| [CompletionRecovery](veil/Paralean/CompletionRecovery.lean) | Completion requires a catalogue record for the exact image/workspace; checked required targets survive failures and remain recoverable |
| [Protocol](veil/Paralean/Protocol.lean) | Both strengthened guards on one typed store, with actual joint publication, completion, discovery and recovery transitions |
| [CompletionRecoveryExecution](veil/Paralean/CompletionRecoveryExecution.lean) | Nonempty completion after catalogue acknowledgement, replica destruction, desktop-ID loss and exact physical recovery |
| [ProtocolExecution](veil/Paralean/ProtocolExecution.lean) | One reachable execution through the joint protocol, including publication markers and catalogue-backed completion |
| [ProtocolGuardChecks](veil/Paralean/ProtocolGuardChecks.lean) | Missing catalogue, mismatched image and missing publication-marker regressions |

The models use explicit theory parameters/hypotheses. No project axioms, incomplete
proofs or trusted SMT verdicts are used. Final theorem audits permit only `propext`,
`Classical.choice`, and `Quot.sound`. [Audit.lean](veil/Audit.lean) additionally scans
the generated project namespaces. Proofs reason about Veil's generated transitions;
they are not proofs of an unrelated handwritten state machine.

Read the component notes for exact theorem statements and mappings:
[registry](veil/REGISTRY.md), [storage](veil/DURABILITY.md),
[convergence](veil/CONVERGENCE.md), [composition](veil/COMPOSITION.md),
[end-to-end projection](veil/ENDTOEND.md), [commit freshness](veil/COMMIT.md),
[atomic groups](veil/GROUPS.md), [packet delivery](veil/DELIVERY.md),
[coupled admission](veil/ADMISSION.md), [catalog recovery](veil/RECOVERY.md),
[recovery adequacy](veil/RECOVERY-ADEQUACY.md).
[The joint protocol](veil/PROTOCOL.md) strengthens the original component models;
its catalogue and publication-marker guards are part of the service contract.
The TLA/Veil correspondence is documented, not mechanically translated.

## Assumptions and limits

- `Valid` is the trusted checker/policy interface; `Exportable` is the source-build
  interface. The proofs do not implement or verify them.
- Buildability alone does not imply task completion. `Delivery` checks every
  immutable required contract; `Admission` pairs completion with an actual durable
  current commit. An empty snapshot cannot finish a nonempty required task.
  Different checked objects can satisfy the same contract. Each completion witness
  binds snapshot membership, checking, satisfaction and durability to one group.
  The joint protocol additionally requires a retained catalogue record for that
  same snapshot before completion. Its recovery path uses the physical store,
  without reading the old admission head or result.
- Hash/serialization/receipt correctness and stable-write completion are interface
  obligations. The package includes source, body and metadata; the manifest denotes
  its exact contents. Typed payload, manifest, catalogue and publication constructors separate
  object roles. They do not prove physical encoding or hash collision resistance.
- Crash safety tolerates loss only while a recovery quorum survives. New publication
  also needs a usable write quorum. Repair, changing membership and GC are absent.
- Safety permits permanent partitions/crashes. Temporal proofs assume that workers
  eventually remain alive/connected and continuously enabled receives are served.
  Recurrent brief recovery alone is insufficient. There is no latency bound.
- Per-revision delivery needs no finite universe. One global convergence cutoff
  requires finite worker and revision universes. No claim covers an indefinitely
  growing infinite registry with all indexes equal after a fixed time.
- Publication discovery requires complete physical enumeration and durable
  acknowledgement evidence for marker objects. The marker acknowledgement and
  publication form one logical event. The strengthened receive guard consumes
  physical scan evidence; fairness applies to this guarded operation. A surviving
  copy of an unindexed payload alone is insufficient.
- Eventual collision proves a fixed distinct same-name pair with no published
  descendants. Explicit resolution changes that premise. The index conflict is
  proved; emitting a UI diagnostic is an implementation obligation.
- Already committed snapshots remain valid after becoming stale. The current
  registry may report conflicts while an old stock-buildable snapshot remains usable.
- `Recovery` reconstructs catalog heads after losing the local ID and validates
  staged entries before adoption. Its record type assumes schema-valid ancestry;
  the decoder must reject malformed metadata. Physical enumeration completeness, durable-write
  receipts and the external fencing authority remain implementation contracts.
  Read-only recovery does not grant writer ownership.
- Neither proof search termination, eventual draft publication, performance,
  nor adversarial storage/validator correctness is established.

## Reproduce on Linux/AWS

Install Java, Python 3, Git, curl, elan, Node/npm and Clang as required by the pinned Veil
checkout. Use this repository as the working directory:

```sh
bash scripts/bootstrap-verification.sh
bash scripts/check-tla.sh
bash scripts/check-tla-negative.sh
bash scripts/check-veil.sh
```

Bootstrap verifies the TLA jar SHA256 and pins Veil. Proof checks compile dependencies
before consumers into `.runs/veil`; they do not use stale source-directory objects.
Logs go to `.runs/`. The archived run and source hashes are in [results](results/README.md).

The separate [Lean experiments](../experiments/run.sh) require an installed Lean
binary. Their recorded run used stock Lean 4.34.1. They are not distributed proofs.
