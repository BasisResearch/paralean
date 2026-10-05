# Hardened joint protocol

`Paralean/Hardened.lean` (namespace `ParaleanHardened`) closes design gaps found in
review of the [joint protocol](PROTOCOL.md). Each visible step is a
`ParaleanProtocol.Next` step that also satisfies five guards. Lean naming refines
group membership below the protocol and needs no transition guard.

| Gap | Fix | Module |
|---|---|---|
| Publication trusted the publisher's own `valid` check | Staging a group requires a held, verified validator receipt for that exact group | [PublicationReceipts](PUBLICATION-RECEIPTS.md) |
| Alternative proofs of one target collided on its name | Each target has an owner, an epoch and the latest published proof (head) in one store record; the owner's new proof revises that head; publication is fenced by the epoch and updates the head | [TargetNames](TARGET-NAMES.md) |
| Any process could Put a catalogue record that recovery auto-selects | A new write of a record's bytes either passes a conditional check of its token against the store's fence, or copies bytes read from a named live replica | [CatalogFencing](CATALOG-FENCING.md) |
| Catalogue recovery read ghost acknowledgement and ghost commit history, and adopted stale records that were acknowledged late | Certificates for the record, manifest and payloads, written as all-quorum writes from the writer's own reply log; the commit certificate is conditional on the fence and on the record's parents being ready; certificates may be repaired; commit and adoption need durable certificates; recovery's scan is computed from the answers of a responding read quorum, and its enumerate is lifted into a hardened step | [CatalogCertificates](CATALOG-CERTIFICATES.md) |
| Discovery read Durability's ghost `acknowledged` flag | Scans read per-replica certificates; publication writes the publisher's certificate quorum in the same transaction; commits require the committer's own reply quorum, collected over time | [AckCertificates](ACK-CERTIFICATES.md) |
| `member` ignored reserved, generated and private Lean names | Capture per command; public names (including auto-named instances and eager auxiliaries) collide; private and compiler-auxiliary names are group-keyed; reserved names are re-realized | [LeanNames](LEAN-NAMES.md) |

## Composition

`Extra` is the product of:

- the first-write fencing history (`e.1`);
- publication certificates and each writer's reply log (`e.2.1`);
- catalogue certificates, the catalogue writer's reply log and the
  commit-certificate fence history (`e.2.2.1`);
- the target ownership record: owner, epoch, recorded head, prepared epochs (`e.2.2.2`).

Certificate writes (other than the publisher's), certificate repair and target
reassignments are Extra-only steps: the protocol state stutters and every other
guard accepts the stutter. A publication is one step of all five components: the
base publish (marker acknowledgement), the publisher's certificate quorum
(`AckCertificates.PublishWrite`) and the fenced head update
(`TargetNames.advance`), as in docs/store.md's T1.
`Next (s,e) (t,e') := ParaleanProtocol.Next s t ∧ Guard s e t e'`, where `Guard`
conjoins the five component guards. `reachable_receipts`, `reachable_targets`,
`reachable_fencing`, `reachable_certificates` and `reachable_catalog` project a
hardened reachable state onto each component's `Reachable`. `reachable_protocol`
projects onto the joint protocol, so every earlier theorem still applies.

`hardened_safe` states, for one reachable state:

- the original joint invariants (`CompletionRecovery.Safe`, `PublicationDiscovery.Safe`);
- every published group has a verified validator receipt;
- no node has two heads for a target name, across arbitrary reassignments;
- a selected catalogue record was first written while its token was the fence, and
  its commit certificate was written while its token was the fence;
- every certificate names a published group; every published group has a
  certificate quorum (`published_certified`); every checkpoint group has the
  committer's own reply quorum and is found by a certificate scan of any fully
  live recovery quorum;
- every committed catalogue record is physically certified (`CatReady`).

## Implementation recovery

The base `enumerate v` carries a precondition on ghost state (every record in the
`committed` history is decoded and ready in `v`), and the base coupling checks
ready records against Durability's ghost `acknowledged`. The hardened model keeps
both unchanged (weakening the first would break the base `CatalogComplete`
invariant) and proves that recovery's implementation step implies them.

- `SStep`: a hardened step, or an implementation enumerate
  (`CatalogCertificates.ScanEnumerate`): recovery reads a read quorum all of whose
  members answered, computes the scan from those answers
  (`CatalogCertificates.certScanValue`: decoded = a member returned the bytes, ready
  = members returned the record, manifest and payload certificates) through a
  `ScanCodec`, and applies the enumerate state change, checking nothing else.
- `scan_enumerate_hardened`: from any reachable hardened state, an implementation
  enumerate is a hardened step (all five guards). The ghost precondition, the ghost
  readiness test and the adoption guard are derived from the certificates.
- `sreachable_iff`: runs whose recovery enumerates this way reach exactly the
  hardened states, so `hardened_safe` and every other hardened theorem hold for them.
- `hardened_certified_recovery`: from any reachable hardened state, any responding
  read quorum and any committed record, an implementation enumerate, a
  reconstruction and a historical selection select the record in three hardened
  steps; its commit certificate passed the fence check.

## Other cross-guard results

- `recorded_head_receivable` (target record + publication certificates + all other
  guards): the head in a target's owner/epoch record is a published proof of the
  name and tops every published proof of it. It has a certificate quorum (written
  with its publication), so every fully live certificate scan finds it, and any
  live, online node that does not know it (a new owner whose index was erased) can
  receive it by a hardened step. The new owner's prepare must then revise exactly
  that head (`TargetNames.guard_observable`), so the target chain does not depend
  on the owner's scan being complete. The earlier premise that the head has a
  certificate quorum is gone: the head can no longer be stranded.
- `owner_prepare_enabled` (enabledness after a handover): in every reachable
  hardened state, the current owner of a target name (for example a new owner
  after reassignment) knows the recorded head or can receive it by a hardened step,
  and any base preparation by the owner of a group with a held receipt that revises
  the recorded head of each target name it declares (all owned by it), with no
  other pending proof of those names, is a hardened step. It is an enabledness
  result, not eventual progress: whether such a revision exists and is base-enabled
  depends on the theory and the delivery state.
- `lift_recovery_only`: a step that changes only the recovery component passes the
  receipt, target, first-write and publication-certificate guards.

## Execution

[HardenedExecution](Paralean/HardenedExecution.lean) uses the
`CompletionRecovery.Example` instance: two workers, two groups, two replicas (write
quorum = both, read quorum = replica `true`), fence tokens of rank 0 and 1, and two
catalogue records, `false` a child of `true`. Its scan type carries any
decode/readiness pair, and `codec` is a concrete `ScanCodec`.

`hardened_nonvacuous`, one trace, every step hardened:

- The initial owner of the target name prepares the required target holding a
  verified receipt and publishes it; the publish records it as the name's head and
  writes the publisher's certificates on both replicas (each publication does).
- The committing worker receives each group through a physical certificate read,
  then puts its own certificates for both groups on both replicas. Before those
  puts it holds no certificate quorum for the target (its commit guard reads only
  its own replies).
- Each acknowledgement adds the catalogue writer's replies to its log. From that
  log the writer writes payload, manifest and commit certificates for record `true`
  as quorum writes (commit certificate under fence 0; record `true` has no
  parents). The catalogue commits and the worker finishes.
- The desktop is lost. The controller reassigns the target name to the other worker
  (epoch 1); the record keeps its head. The fence rotates to 1.
- Under fence 1, record `false` (rank-1 token) is first written, acknowledged, and
  its manifest written and acknowledged. It gets no commit certificate.
- A replica is lost, every worker index is erased, a certificate scan rediscovers
  exactly the published groups, and the new owner receives the recorded head through
  a certificate-guarded receive.
- Recovery enumerates by `ScanEnumerate` over the surviving read quorum. The scan
  decodes both records (both sets of bytes are on the surviving replica) and marks
  only record `true` ready; record `false` is rejected for lack of a commit
  certificate. Reconstruction and `automatic` select record `true`.

`hardened_scan_adoption`, sharing that trace up to record `false`'s
acknowledgement: the writer writes record `false`'s manifest and commit
certificates (fence 1; its parent, record `true`, is ready on the read quorum), a replica is lost, and the same scan over the same bytes
marks both records ready. `enumerate` adopts record `false` (it was not committed;
`AdoptGuard` holds by the surviving certificates), and `automatic` selects it as the
unique head. Selection is decided by certificates, not by which bytes decode.

`stale_owner_publish_blocked`: after the target is prepared under epoch 0, the
controller reassigns the name (epoch 1). The former owner's publication of its
pending target is a base protocol step, but no hardened step (the epoch fence).

`hardened_receipt_rejected`: in a variant of the instance whose validator signs
only receipt `true`, the helper's receipt is in flight in a reachable hardened
state; staging the helper is a base protocol step there, but no hardened step.

## Implementation contracts introduced

- Validators sign receipts over the exact content-addressed group ID, policy and
  checker version. Workers stage only with a receipt.
- The controller keeps each target's owner, epoch and head in one store record. The
  owner reads it before preparing, revises the head and stamps its proof with the
  epoch; the publication write is conditional on the epoch and sets the head.
  Targets declared by one group share an owner.
- The catalogue store performs transactional writes conditional on a fence item
  (etcd `Txn`, DynamoDB `TransactWriteItems`, FoundationDB); fence rotation is a
  linearizable write to the same store; each token rank is issued once. First
  writes and commit certificates use it. An unfenced copy of record bytes names the
  live replica it read them from.
- Catalogue certificates (commit, manifest, payload) are written as one transaction
  that is readable only once it has reached a write quorum, and only after the
  writer holds its own write quorum of replies for the object. A commit certificate
  also requires every parent record's commit, manifest and payload certificates.
  A replacement replica receives copies of existing certificates (repair) before it
  counts towards a write quorum.
- Recovery waits for every member of some read quorum to answer and decides
  readiness from those answers. A lost replica never rejoins under the same
  identity.
- Publication certificates are stored per replica separately from object bytes.
  Writers persist the replies they receive. The publication transaction writes the
  publication marker, the publisher's certificates on the write quorum that
  acknowledged it (with the publisher's record of those replies) and the fenced
  target-record head update atomically; an aborted publication writes none of them.
- Capture runs at command granularity with a trusted name classifier. Instances
  are named canonically. The renderer and exporter mangle scoped names to
  group-unique Lean names.

## Not established

- The receipt is not bound to a request, checker or policy, because requests are
  opaque in the model. Untrusted workers are modelled only at staging.
- Publication certificates mirror Durability's rules in separate state rather than
  being generated Durability objects; so do catalogue certificates. The writer-side
  premise of a publication certificate write is that the writer knows the group; the catalogue
  writer's reply log is recorded at Durability's `Ack` step rather than reply by
  reply.
- All-quorum catalogue certificate writes are a store contract, not derived from
  per-replica writes. Certificate repair copies only to existing live replicas;
  replica replacement is not modelled, and there is no write-back by readers.
- The joint trace does not show a new owner preparing a revision of a non-empty
  head: the instance has one target group and no revisions. That case is shown in
  the TargetNames model (`TargetNames.Example.handover_witness`) and in general by
  `recorded_head_receivable`.
- Receipt rejection is shown on a variant instance (the main instance's validator
  signs both receipts, which the main trace needs).
- No fair-convergence result is restated for the hardened model: the new guards
  strengthen every step, so the earlier fair-convergence theorems do not transfer.
  `owner_prepare_enabled` is an enabledness lemma only; `HandoverProgress`,
  `RecoveryAdopts`, `CommittedDiscoverable` and `PublishedDiscoverable` are checked
  only in TLA.
- Each TLA model is an independent finite abstraction of one fix. `tla/Fencing.tla`
  still decides catalogue readiness over live replicas with per-replica certificate
  writes.
