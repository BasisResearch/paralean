# Catalogue certificates and fenced commit records

`Paralean/CatalogCertificates.lean` (namespace `ParaleanCatalogCertificates`) guards
`ParaleanProtocol.Next`. It closes two gaps in catalogue recovery.

- `ParaleanRecovery.StorageReady`, the base readiness test of `enumerate`, reads
  Durability's ghost `acknowledged` flag for the record, its manifest and its
  payloads. After replica loss a lone surviving copy cannot show whether it was
  acknowledged.
- `ParaleanCatalogFencing` fences only first writes. A stale writer can first-write
  one replica before a rotation, then repair, acknowledge and commit after it.
  Recovery adopts that record (`CatalogFencing.Example.late_ack_and_repair_execution`).

## Model

`Extra replica record obj` has three fields.

- `ocert x o`: replica `x` holds an acknowledgement certificate for object `o`
  (manifest or payload). Store state, erased when `x` is lost.
- `rcert x c`: replica `x` holds the commit certificate of record `c`. Store
  state, erased when `x` is lost. This is the commit record.
- `certFence c`: ghost. The fence each commit certificate of `c` was checked against.

Certificate writes are extra-only steps (`CertStep`); the protocol state stutters.

- `CertStep.record x c`: `live x`, `acknowledged (.catalog (encode c))`, and
  `tokenRank (recordToken c) = fence`. A conditional write on the fence register.
  Sets `rcert x c` and `certFence c := some fence`.
- `CertStep.object x o`: `live x` and `acknowledged o`. Not fenced.

The `acknowledged` premise is the writer's own Ack conclusion (it holds the write
replies). It is not read by any recovery step.

Readiness reads live replicas only:

- `RecordDurable c`: for some write quorum, every live member holds `rcert _ c`.
- `ObjectDurable o`: the same for `ocert _ o`.
- `CatReady c`: the record, its manifest and every payload of its image are durable.

`AdoptGuard`: a protocol step that makes a record committed needs `CatReady` in the
pre-state. This covers the writer's own `commit` and adoption by `enumerate`.
`Guard := (AdoptGuard ∧ e' = clearLost s t e) ∨ (t = s ∧ CertStep s e e')`.

## Concrete scan

`ScanCodec r` says the recovery theory's scan type can carry any decode/readiness
pair (`build`, `decoded_build`, `ready_build`). `certScanValue codec q` is the scan
recovery computes from the store:

- decoded: the record's bytes are on a live member of read quorum `q`;
- ready: `CatReady`.

No `PhysicalScan` or `ReadyScan` hypothesis is used on the hardened path.
`ParaleanRecovery.enumeration_enabled_of_cover` replaces `ReadyScan` (readiness equal
to ghost acknowledgement) with two weaker premises: the scan covers committed
records, and readiness implies `StorageReady`.

## Results

All `Reachable`, by induction over the real `Next`. Axioms: `propext`,
`Classical.choice`, `Quot.sound`.

Invariant `Inv`:

- `rcert x c` implies the record's bytes are acknowledged and
  `certFence c = some (tokenRank (recordToken c))`;
- `ocert x o` implies `o` is acknowledged;
- `certFence c = some k` implies `k = tokenRank (recordToken c) ≤ fence`;
- every committed record is `CatReady` and has `certFence c = some rank`.

Fencing:

- `record_cert_fenced`: every commit certificate passed the fence check.
- `committed_fenced`: every committed record, including adopted ones, has a commit
  certificate written while its token rank was the fence.
- `selected_fenced`: the selected record was committed while its writer held the fence.
- `stale_record_cert_rejected`: a commit certificate for a record whose token rank is
  not the fence is not a certificate step.
- `stale_stays_uncertified`, `uncertified_not_committed`: once the fence passes a
  record's token rank, a record without a commit certificate never gets one, so it
  is never committed or adopted. This excludes the late-ack-and-repair zombie.

Readiness:

- `catReady_storageReady`: `CatReady` implies the base `StorageReady`. The ghost read in
  the base guard is discharged by certificates.
- `committed_catReady`: every committed record stays certified under any loss allowed
  by the failure envelope.
- `certScanValue_covers`, `certScanValue_sound`: the concrete scan of a fully live read
  quorum covers every committed record and passes the base readiness test.
- `certified_recovery`: from any reachable state and fully live read quorum, the
  concrete scan, a reconstruction and a historical selection select any committed
  record in three steps of this layer. Every known record after the scan is `CatReady`.

Joint model: `ParaleanHardened.hardened_certified_recovery` lifts `certified_recovery`
to all five guards and adds the fence statement for the selected record.
`ParaleanHardened.Example.hardened_nonvacuous` writes certificates before the commit,
and a first write plus a commit certificate of a rank-1 record under fence 1.

## TLA

`tla/Fencing.tla` models the same design: a fenced `CommitCert` after the writer's
`Ack`, and a `Scan` that adopts only records whose certificates are durable on live
replicas. Mutations (`scripts/check-tla-negative.sh`):

- `fencing_unfenced_commit`, `fencing_unfenced_commit_selected`: no fence check on
  `CommitCert`; `CertFenced` and `SelectedFenced` fail.
- `fencing_stale_selected`: `Scan` adopts on a live byte quorum (the old design); a
  record first written before rotation and acknowledged after it is adopted
  (`NoLateAckedKnown` fails).
- `fencing_cert_unacked`: `CommitCert` without the writer's Ack; a certified record's
  bytes can be lost (`ScanFindsCertified` fails).

## Implementation contract

- The commit certificate is a transactional write conditional on the fence item
  (etcd `Txn`, DynamoDB `TransactWriteItems`, FoundationDB), issued after the writer
  has its write quorum of replies for the record bytes.
- Object certificates follow the writer's Ack of the manifest or payload.
- Recovery reads the certificates of every reachable replica, and decides readiness
  per write quorum over the replicas it reaches.
- Certificates are never garbage-collected. A lost replica's certificates are gone.

## Not established

- There is no certificate repair. A record adopted after replica loss needs certificates
  on every live member of a write quorum; with write quorum = all replicas this only
  holds for records certified before the loss.
- The `acknowledged` premise of a certificate write is the writer's Ack conclusion,
  modelled by the ghost flag because Durability's Ack is not attributed to a writer.
- The base `enumerate` precondition still requires the scan to cover every committed
  record. `certScanValue_covers` discharges it; base-model theorems stated with
  `ReadyScan` (RecoveryAdequacy, CompletionRecovery, Protocol) remain base-model results.
- Liveness is not restated.
