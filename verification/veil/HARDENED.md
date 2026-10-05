# Hardened joint protocol

`Paralean/Hardened.lean` (namespace `ParaleanHardened`) closes design gaps found in
review of the [joint protocol](PROTOCOL.md). Each visible step is a
`ParaleanProtocol.Next` step that also satisfies five guards. Lean naming refines
group membership below the protocol and needs no transition guard.

| Gap | Fix | Module |
|---|---|---|
| Publication trusted the publisher's own `valid` check | Staging a group requires a held, verified validator receipt for that exact group | [PublicationReceipts](PUBLICATION-RECEIPTS.md) |
| Alternative proofs of one target collided on its name | Each target has an owner, an epoch and the latest published proof (head) in one store record; the owner's new proof revises that head; publication is fenced by the epoch and updates the head | [TargetNames](TARGET-NAMES.md) |
| Any process could Put a catalogue record that recovery auto-selects | A record's first write is conditional on its token equalling the store's fence | [CatalogFencing](CATALOG-FENCING.md) |
| Catalogue recovery read ghost acknowledgement, and adopted stale records that were acknowledged late | Per-replica certificates for the record, manifest and payloads; the record's commit certificate is a conditional write on the fence; commit and adoption need durable certificates; the scan is computed from the store | [CatalogCertificates](CATALOG-CERTIFICATES.md) |
| Discovery read Durability's ghost `acknowledged` flag | Scans read per-replica certificates; commits require the committer's own reply quorum, collected over time | [AckCertificates](ACK-CERTIFICATES.md) |
| `member` ignored reserved, generated and private Lean names | Capture per command; public names (including auto-named instances and eager auxiliaries) collide; private and compiler-auxiliary names are group-keyed; reserved names are re-realized | [LeanNames](LEAN-NAMES.md) |

## Composition

`Extra` is the product of:

- the first-write fencing history (`e.1`);
- publication certificates and each writer's reply log (`e.2.1`);
- catalogue certificates and the commit-certificate fence history (`e.2.2.1`);
- the target ownership record: owner, epoch, recorded head, prepared epochs (`e.2.2.2`).

Certificate writes and target reassignments are Extra-only steps: the protocol state
stutters and every other guard accepts the stutter.
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
- every certificate names a published group; every checkpoint group has the
  committer's own reply quorum and is found by a certificate scan of any fully
  live recovery quorum;
- every committed catalogue record is physically certified (`CatReady`).

## Cross-guard results

- `hardened_certified_recovery` (catalogue certificates + fence + all other guards):
  from any reachable hardened state, any fully live read quorum and any committed
  record, recovery computes the certificate scan from the store
  (`CatalogCertificates.certScanValue`), enumerates, reconstructs and selects the
  record in three hardened steps. The selected record's commit certificate passed
  the fence check. No scan value, `ReadyScan` or acknowledgement oracle is assumed.
- `recorded_head_receivable` (target record + publication certificates + all other
  guards): the head in a target's owner/epoch record is a published proof of the
  name and tops every published proof of it. If it has a certificate quorum, every
  fully live certificate scan finds it, and any live, online node that does not know
  it (a new owner whose index was erased) can receive it by a hardened step. The
  new owner's prepare must then revise exactly that head
  (`TargetNames.guard_observable`), so the target chain does not depend on the
  owner's scan being complete.
- `lift_recovery_only`: a step that changes only the recovery component passes the
  receipt, target, first-write and publication-certificate guards.

## Execution

[HardenedExecution](Paralean/HardenedExecution.lean) gives one concrete trace in
which all five guards hold on every step (`hardened_nonvacuous`):

- The initial owner of the target name prepares the required target holding a
  verified receipt and publishes it; the publish records it as the name's head.
- The committing worker receives each group through a physical certificate read,
  then puts its own certificates for both groups on both replicas. Before those
  puts no node holds a certificate quorum for the target.
- The catalogue record is acknowledged; its payloads and manifest get
  acknowledgement certificates and the record gets its commit certificate under
  fence 0 on both replicas. The catalogue commits and the worker finishes.
- The desktop is lost. The controller reassigns the target name to the other worker
  (epoch 1); the record keeps its head. The fence rotates to 1.
- Under fence 1, a second record with a rank-1 token is first written, acknowledged
  and given a commit certificate on both replicas (`eF false = some 1`,
  `certFence false = some 1`). It is not committed: this instance has two records
  with no ancestry, and committing both would leave two heads.
- A replica is lost, every worker index is erased, a certificate scan rediscovers
  exactly the published groups, the new owner receives the recorded head through a
  certificate-guarded receive, and recovery auto-selects the record whose commit
  certificate passed the fence check.

The new owner preparing a revision after reassignment is not in this trace: the
instance has one target group. It is shown in the TargetNames model
(`TargetNames.Example.handover_witness`) and in general by `recorded_head_receivable`.

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
  writes and commit certificates use it.
- Each replica stores acknowledgement certificates separately from object bytes:
  publication markers, catalogue manifests and payloads, and record commit
  certificates. Writers persist the replies they receive.
- Capture runs at command granularity with a trusted name classifier. Instances
  are named canonically. The renderer and exporter mangle scoped names to
  group-unique Lean names.

## Not established

The receipt is not bound to a request, checker or policy, because requests are
opaque in the model. Untrusted workers are modelled only at staging. Publication
certificates mirror Durability's rules in separate state rather than being
generated Durability objects; so do catalogue certificates. Discovery is complete
only for groups with a certificate quorum. The writer-side premise of a certificate
write is the writer's own Ack, modelled by the ghost flag. There is no certificate
repair. No liveness result is restated for the hardened model: the new guards
strengthen every step, so the earlier fair-convergence theorems do not transfer.
Each TLA model is an independent finite abstraction of one fix.
