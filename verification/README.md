# Verification scope

The checked subject is the abstract distribution protocol. The production Lean
fork, validator service, object-store adapter and LSP transport are not
implemented. The P1 prototype (`impl/p1`, on stock Lean) implements capture, an
encoder, a local content-addressed store, replay and stock export; none of it is
verified here. The mapping of the modelled store to FoundationDB and S3 is a
written argument ([store.md](../docs/store.md)), not a proof.

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
- [Hardened](tla/Hardened.tla): the receipt, target, publication-certificate and
  catalogue guards on one shared store (three replicas, two workers, one target
  record and fence), with a lagging read of the target record, owner handover,
  fence rotation and re-acquisition, one replica loss and one index erasure. The
  separate hardening models (`Receipts`, `Targets`, `Certificates`, `Fencing`)
  check one guard family each. See [HARDENED-TLA.md](tla/HARDENED-TLA.md).

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

Exhaustive finite-state checks ran on 2026-10-05 on a shared Apple M4 (macOS,
OpenJDK 17.0.18) with TLC2 2.19 (see [toolchain](results/tlc/toolchain.txt))
and four TLC workers. These are full reachable-state searches
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
| CheckpointReuse | Restricted spec: a staged ordering of Integrated's actions (committed checkpoint, acknowledged-replica loss, worker restart) | 43,888 | Surviving copies and repeated commit on that restricted execution only |
| ExportRejected | Closed snapshot rejected by exporter | 22 | Export rejection despite dependency closure |
| Receipts | 2 workers, valid/dependent/invalid groups, Byzantine staging; the receipt guard is on staging only, publish is the base publish | 181 | Staged and published groups valid, receipted, dependency-closed |
| Targets | 2 workers, one target name, 3 proofs, crash, owner reassignment (2 epochs), head kept in the owner record | 838,428 | Target proofs form a chain; unique head across handovers; the recorded head tops the chain |
| Fencing | 3 replicas (symmetry-reduced), fence register with re-acquisition (tokens 1..3), fenced first writes, repair from a named live source, fenced commit certificates, scan of live certificates | 754,348 | Stale first writes never stored; commit certificates, adopted and selected records committed under the fence; a late-acknowledged stale record is never adopted; certified records are found by every fully live scan |
| Certificates | 3 replicas, 2 groups, 2 nodes, loss and index erasure (symmetry-reduced) | 536,937 | Certificates sound; replies survive; scans between quorum and published; checkpoints certified and discoverable |
| Workspace | 3 agents, 2 files, 5 declarations, a two-name group revised for one name, collision, winner revision, tombstone; staging and publication are separate steps, receive is in any order for anchors | 62,098 | Same known set renders identically; only live heads render; a superseded group holds no name; stable order; revised winner keeps its name; intention preserved; published anchors are published; eventually identical |
| WorkspacePending | 3 agents, 1 file, 3 declarations; an author stages two declarations, the second anchored at the first while it is pending | 4,199 | As Workspace; the anchor is published first and renders above in every copy; a record received before its anchor renders at its carried position |

The suite explores 5,526,366 distinct states across twenty separate scenarios. Fingerprint
collision estimates, seeds, timings and state counts are retained in the raw logs.
No state/depth constraints hide behaviors. `Certificates` uses symmetry reduction
over replicas, groups and nodes, and `Fencing` over replicas; both check only
invariants, for which this is sound.

### Larger scopes

`scripts/check-tla.sh --wide` runs larger instances of the same models
(`TLA_WIDE_SCENARIOS` in `scripts/tla-common.sh`). They are not in the default
suite because of their runtime. All are invariant-only (Workspace also checks its
action properties); symmetry is used only where noted. Runtimes are from the
archived run on a shared Apple M4 with four workers and a 6 GiB heap; under heavier
load TargetsWide took up to 23min 28s and FencingWide up to 10min 54s.

| Scenario | Bump over the default instance | Distinct states | Runtime |
|---|---|---:|---:|
| ReceiptsWide | 3 workers (was 2) | 1,513 | under 1s |
| TargetsWide | 3 workers, 3 epochs (was 2, 2); symmetry over proofs and the non-initial workers | 12,400,854 | 5min 00s |
| FencingWide | 4 replicas (was 3), majority (3-member) quorums; replica symmetry | 1,860,196 | 5min 41s |
| WorkspaceWide | 3 publishing authors in one file (was 2), a collision, a cross-author revision and an own-pending anchor; no symmetry | 25,725 | 24s |

Not feasible here: `Certificates` with 3 nodes (stopped after 20 minutes at
3,873,820 distinct states, 2,118,416 queued) and with 3 groups (stopped after 20
minutes at 6,080,122 distinct states, 3,272,152 queued). `Certificates` is still
checked only at 3 replicas, 2 groups and 2 nodes. Not attempted: Fencing with a
fourth token, Targets with 2 target names (the model has one name), Fencing with
5 replicas. The liveness instances keep their small constants.

### Combined hardened model

`scripts/check-tla-hardened.sh` checks [Hardened](tla/Hardened.tla), which puts
the receipt, target, certificate and catalogue guards on one shared store. It is
opt-in: neither `check-tla.sh` nor `check-tla-negative.sh` runs it. A complete run
writes `.runs/tla/hardened/MANIFEST`; `archive-verification.sh` then archives its
29 logs in [results/tlc/hardened](results/tlc/hardened), and `--verify` checks
each archived log's provenance and expected outcome. Without a complete run that
directory is removed. Both instances use replica symmetry and check invariants
only (safety and reachability, no liveness). Runtimes are from the archived run,
four workers, 6 GiB heap, on the shared machine.

| Instance | Configuration | Distinct states | Depth | Runtime | Checked properties |
|---|---|---:|---:|---:|---|
| Hardened | 3 replicas, 2 workers, proofs `p1`, `p2`, invalid group `x`; one owner handover (`MaxEpoch = 1`), one fence rotation (`MaxFence = 2`); one replica loss, one index erasure | 3,104,542 | 35 | 7min 28s | Receipts (`StagedValid`, `StagedReceipted`, `PublishedValid`, `PublishedReceipted`); targets (`TargetChain`, `HeadUnique`, `RecordTopsChain`); certificates (`CertSound`, `ReceivedPublished`, `PublishedDiscoverable`, `CheckpointDiscoverable`); catalogue (`StaleNeverStored`, `CertFenced`, `ReadyCommitFenced`, `ReadyFirstWriteFenced`, `ReadySnapshotSound`); `CompletedRecoverable`; `FailureEnvelope`, `TypeOK` |
| HardenedReacquire | As Hardened, no handover (`MaxEpoch = 0`), fence rotated away and re-acquired (`MaxFence = 3`) | 280,614 | 30 | 57s | As Hardened |

The same script runs 8 coverage witnesses (each `Never*` property must fail), 16
single-guard mutations (each must report its named invariant violation) and 3
redundancy probes (each guard deletion must leave the listed invariants intact;
`r_unfenced_put_adoption`, `r_commit_without_own_quorum` and
`r_ready_without_object_certs`: 3,766,968, 7,628,232 and 3,104,542 distinct
states in 9min 59s, 17min 22s and 7min 53s). The
whole suite took 44min 29s. Findings are in the
[guard matrix](TLA-GUARDS.md#combined-hardened-model); the model, its restrictions
and what it leaves out are in [HARDENED-TLA.md](tla/HARDENED-TLA.md).

`scripts/check-tla-negative.sh` makes 81 TLC runs:

- 26 coverage witnesses: a `Never*` invariant or action property that must fail.
  They establish full B→A→B dependency-chain commitment, dependent publication,
  collisions, acknowledgements, disk loss, integrated commitment, checkpoint reuse
  after loss and admission despite export rejection. The hardening models add
  receipted and dependent publication, a committed alternative target proof, a
  target handover, recovery after fence rotation, recovery of a record written
  after the writer re-acquired the fence, an acknowledgement and a repair after
  rotation, certificate rediscovery after loss, a commit after a replying replica
  is lost, converged concurrent inserts, a resolved name collision, a revised
  winner, a deletion, a partial revision that frees a name, an author anchoring at
  its own pending declaration, and a declaration rendered before its anchor arrives.
- 49 mutations, each expecting a named invariant or temporal violation (two of
  them run the original design against the new liveness properties). They
  make 46 distinct source edits: three deletions are run twice against different
  oracles (`unreceipted_staging`/`unreceipted_publication`,
  `unknown_ancestor`/`unclosed_ancestors`,
  `fencing_unfenced_commit`/`fencing_unfenced_commit_selected`).
  They exercise admission, ancestor closure, freshness, acknowledgement,
  fairness, storage guards, name selection, exportability and useful work. The
  hardening mutations remove the receipt staging guard (Receipts has no separate
  publication guard), each target guard conjunct (owner, revise the recorded
  head, single pending, epoch fence), replace the head read by a scan subset or
  drop the head update, remove the catalogue first-write fence, the commit
  certificate fence, the commit certificate's Ack precondition and the repair
  source read, make recovery adopt on byte quorums instead of certificates,
  remove the publication certificate scan, commit and writer-knowledge guards,
  break the workspace rendering, lineage winner, live-head, name-holding and
  Lamport-clock rules, remove the workspace publication guard, read the clock
  from published declarations only, and render by the anchor tree instead of
  carried paths.
- 3 missing-witness runs: an over-restrictive model must lose a useful-work witness.
- 3 redundant-check deletions that must pass.
The harness requires the intended invariant/temporal error, not merely nonzero exit.
The deliberately over-restrictive models must lose their dependent-work and
checkpoint-reuse witnesses.
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
| [Convergence](veil/Paralean/Convergence.lean) | Delivery and convergence over generated registry traces under receive fairness and eventual permanent stabilisation (`heal`); fixed unsuperseded conflicting pair eventually diagnoses |
| [Composition](veil/Paralean/Composition.lean) | Actual generated component transitions with storage guards; published packages and checkpoint contents/manifests retain recoverable copies |
| [EndToEnd](veil/Paralean/EndToEnd.lean) | Trace projection, temporal guarantees, composed ancestor closure/acyclicity and surviving ancestor packages |
| [Commit](veil/Paralean/Commit.lean) | Generated commit admissibility iff its guards hold; pre-state freshness, exclusion of stale/conflicting members, guarded composition |
| [Groups](veil/Paralean/Groups.lean) | Atomic multi-name groups, per-name heads, dependency-path conflicts, overlap resolution, storage composition and fair convergence |
| [Delivery](veil/Paralean/Delivery.lean) | Request/receipt/object/recipient/epoch binding, cancellation, required-target completion and a nonempty execution |
| [DeliveryAlternatives](veil/Paralean/DeliveryAlternatives.lean) | Two distinct result objects complete the same immutable required contract |
| [Admission](veil/Paralean/Admission.lean) | Receipt acceptance and completion paired with actual group/storage transitions; durable required targets and crash invalidation |
| [AdmissionExecution](veil/Paralean/AdmissionExecution.lean) | One connected two-worker run with atomic helper admission, dependent target receipts, durable completion and subsequent replica destruction |
| [Recovery](veil/Paralean/Recovery.lean) | Lost-ID catalog recovery, staged-record validation, causal reconstruction, historical selection and fencing. Base readiness (`StorageReady`) reads ghost acknowledgement; the hardened path uses [CatalogCertificates](veil/Paralean/CatalogCertificates.lean) |
| [RecoveryAncestry](veil/Paralean/RecoveryAncestry.lean) | Ancestry equals parent-path reachability; reconstructed heads and conflicts follow recorded parents |
| [RecoveryAdequacy](veil/Paralean/RecoveryAdequacy.lean) | A complete recovery path exists for every previously committed record given a surviving quorum scan value that satisfies `PhysicalScan` and `ReadyScan` (assumed, not constructed) |
| [PublicationDiscovery](veil/Paralean/PublicationDiscovery.lean) | Durable publication markers, physical quorum discovery after all worker indexes are erased, staged-marker rejection and fair convergence |
| [CompletionRecovery](veil/Paralean/CompletionRecovery.lean) | Completion requires a catalogue record for the exact image/workspace; checked required targets survive failures and remain recoverable |
| [Protocol](veil/Paralean/Protocol.lean) | Both strengthened guards on one typed store, with actual joint publication, completion, discovery and recovery transitions |
| [CompletionRecoveryExecution](veil/Paralean/CompletionRecoveryExecution.lean) | Nonempty completion after catalogue acknowledgement, replica destruction, desktop-ID loss and exact physical recovery |
| [ProtocolExecution](veil/Paralean/ProtocolExecution.lean) | One reachable execution through the joint protocol, including publication markers and catalogue-backed completion |
| [ProtocolGuardChecks](veil/Paralean/ProtocolGuardChecks.lean) | Restatements of the guards: a missing catalogue, a mismatched image or a missing publication marker is rejected. They are not necessity proofs |
| [LeanNames](veil/Paralean/LeanNames.lean) | Command-granularity capture; public names (declared, auto-named instances, eager auxiliaries) collide; derived names collide with their base; private and compiler-auxiliary names render group-unique; consumer-realized reserved names leave heads unchanged |
| [PublicationReceipts](veil/Paralean/PublicationReceipts.lean) | Staging requires a verified validator receipt; with workers that skip validity, guarded steps are exactly protocol steps, so every staged and published group is valid; the guard is necessary |
| [TargetNames](veil/Paralean/TargetNames.lean) | Owner/epoch record holding the latest published proof (head), updated by the epoch-fenced publish; reassignment at any time; owner-only proofs that revise the recorded head; the guard reads only the record and the preparer's state (`guard_observable`); chain and unique head across handovers; a scan-based check admits two heads (`scan_check_unsafe`); alternatives complete |
| [CatalogFencing](veil/Paralean/CatalogFencing.lean) | First catalogue writes conditional on the store fence; every stored, selected and completion record was first written under its token's fence; repair copies, acknowledgements and commits after rotation (so adoption needs CatalogCertificates). `FirstWrite` reads whether any replica holds the bytes |
| [CatalogCertificates](veil/Paralean/CatalogCertificates.lean) | Per-replica commit certificates (conditional on the fence) and manifest/payload certificates; every commit or adoption needs them durable on live replicas; committed and selected records were committed under the fence (`committed_fenced`, `selected_fenced`); a stale uncertified record stays uncommitted; certificate readiness implies the base `StorageReady`; the scan is built from the store (`certScanValue`) and recovery of any committed record is enabled (`certified_recovery`) |
| [AckCertificates](veil/Paralean/AckCertificates.lean) | Per-replica certificates and writers' reply logs; commit needs the committer's own reply quorum; scans contain every certificate-quorum group and only published ones; commit survives a lost replier |
| [Hardened](veil/Paralean/Hardened.lean) | All five guards on one joint transition, with certificate writes and reassignments as stuttering steps; every component safety theorem holds simultaneously (no liveness); cross-guard results: certified recovery with fenced selection (`hardened_certified_recovery`) and the recorded target head is certificate-discoverable and receivable by a new owner (`recorded_head_receivable`) |
| [HardenedExecution](veil/Paralean/HardenedExecution.lean) | One concrete trace through every hardened guard: catalogue certificates before the commit, a target reassignment that keeps the recorded head, fence rotation, a fenced first write and commit certificate at fence 1, replica and desktop loss, certificate rediscovery, the new owner receiving the recorded head, and fenced recovery |
| [Workspaces](veil/Paralean/Workspaces.lean) | Transparent workspaces: only live heads render and hold names, in stable lineage-root order; staging may anchor on the author's own pending groups, and a group publishes only after its anchor; records carry anchor paths and lineage keys, so rendering depends only on known records; fresh names live in a reserved namespace that valid groups cannot declare; revising a winner keeps its name; intention preserved both sides |

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
[recovery adequacy](veil/RECOVERY-ADEQUACY.md),
[catalogue certificates](veil/CATALOG-CERTIFICATES.md).
[The joint protocol](veil/PROTOCOL.md) strengthens the original component models;
its catalogue and publication-marker guards are part of the service contract.
The [hardened protocol](veil/HARDENED.md) adds receipt-gated staging, target
ownership with a recorded head, fenced catalogue writes, and publication and
catalogue certificates. The [Lean naming layer](veil/LEAN-NAMES.md) and
[transparent workspaces](veil/WORKSPACES.md) are separate refinements of the Groups
registry; `Hardened` imports neither.
The TLA/Veil correspondence is documented, not mechanically translated.

## Assumptions and limits

- `Valid` is the trusted checker/policy interface; `Exportable` is the source-build
  interface. The proofs do not implement or verify them.
- The receipt guard binds a receipt to the group ID only, not to worker, request,
  policy or checker version. `HeldReceipt` reads the global in-flight packet set,
  which any actor may extend, so on reachable states it is equivalent to the static
  `Receipted` fact. The substance of the receipt results is the `receipt_sound`
  assumption.
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
- Crash safety tolerates loss only while a recovery quorum survives. The loss
  budget is lifetime-cumulative: lost replicas never return and nothing repairs
  them, so the envelope bounds all losses over the whole run, not losses per
  incident. New publication also needs a usable write quorum. Repair, changing
  membership and GC are absent.
- Safety permits permanent partitions/crashes. Temporal proofs assume eventual
  permanent stabilisation (`HealFair` forces a `heal`, after which no crash or
  partition is enabled) and that continuously enabled receives are served. This
  is stronger than fairness. Recurrent brief recovery alone is insufficient.
  There is no latency bound.
- Per-revision delivery needs no finite universe. One global convergence cutoff
  requires finite worker and revision universes. No claim covers an indefinitely
  growing infinite registry with all indexes equal after a fixed time.
- Publication discovery requires complete physical enumeration and durable
  acknowledgement evidence for marker objects. The marker acknowledgement and
  publication form one logical event. The strengthened receive guard consumes
  physical scan evidence; fairness applies to this guarded operation. A surviving
  copy of an unindexed payload alone is insufficient. In the hardened model the
  receive reads publication certificates instead (`AckCertificates`).
- Eventual collision proves a fixed distinct same-name pair with no published
  descendants. Explicit resolution changes that premise. The index conflict is
  proved; emitting a UI diagnostic is an implementation obligation.
- Already committed snapshots remain valid after becoming stale. The current
  registry may report conflicts while an old stock-buildable snapshot remains usable.
- `Recovery` reconstructs catalog heads after losing the local ID and validates
  staged entries before adoption. Its record type assumes schema-valid ancestry;
  the decoder must reject malformed metadata. In the base model its readiness test
  reads ghost acknowledgement; the hardened model replaces it with certificates
  read from live replicas. Durable-write receipts and the external fencing
  authority remain implementation contracts.
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
bash scripts/check-tla-hardened.sh   # optional, about 45 minutes
bash scripts/check-veil.sh
```

Bootstrap verifies the TLA jar SHA256 and pins Veil. Proof checks compile dependencies
before consumers into `.runs/veil`; they do not use stale source-directory objects.
Logs go to `.runs/`. The archived run and source hashes are in [results](results/README.md).

The separate [Lean experiments](../experiments/run.sh) require an installed Lean
binary. Their recorded run used stock Lean 4.34.1. They are not distributed proofs.
