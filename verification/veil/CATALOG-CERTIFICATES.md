# Catalogue certificates and fenced commit records

`Paralean/CatalogCertificates.lean` (namespace `ParaleanCatalogCertificates`) guards
`ParaleanProtocol.Next`. It closes three gaps in catalogue recovery.

- `ParaleanRecovery.StorageReady`, the base readiness test of `enumerate`, reads
  Durability's ghost `acknowledged` flag for the record, its manifest and its
  payloads. After replica loss a lone surviving copy cannot show whether it was
  acknowledged.
- The base `enumerate` precondition reads the ghost `committed` history: the scan
  must decode and mark ready every record ever committed.
- `ParaleanCatalogFencing` fences only first writes. A stale writer can first-write
  one replica before a rotation, then repair, acknowledge and commit after it.
  Recovery adopts that record (`CatalogFencing.Example.late_ack_and_repair_execution`).

## Model

`Extra replica record obj` has four fields.

- `ocert x o`: replica `x` holds the certificate for object `o` (manifest or
  payload). Store state, erased when `x` is lost.
- `rcert x c`: replica `x` holds the commit certificate of record `c`. Store state,
  erased when `x` is lost. This is the commit record.
- `reply o x`: the catalogue writer's own reply log: replica `x` acknowledged the
  writer's write of `o`. Writer-local (like `AckCertificates.certReply`), so the
  loss of `x` does not erase it. It is recorded at the step where the writer's
  acknowledgement of `o` completes (Durability's `Ack`: every member of a write
  quorum is live and holds `o`), for each live replica holding `o` (`logReplies`).
- `certFence c`: ghost. The fence each commit certificate of `c` was checked against.

Certificate writes are extra-only steps (`CertStep`); the protocol state stutters.
Each is one transactional write applied to every member of a live write quorum
`w`: a reader never observes a certificate that has not reached a write quorum.

- `CertStep.record w c`: every member of `w` is live, the writer's reply log holds a
  write quorum of replies for `.catalog (encode c)` (`ReplyQuorum`),
  `tokenRank (recordToken c) = fence` (a conditional write on the fence register),
  and every parent of `c` is `ScanReady` on some responding read quorum (the writer
  read the parents' commit, manifest and payload certificates). Sets `rcert x c` for
  every member of `w` and `certFence c := some fence`.
- `CertStep.object w o`: every member of `w` is live and `ReplyQuorum o`. Not fenced.
- `CertStep.repairRecord x y c`, `CertStep.repairObject x y o`: certificate repair.
  Replica `y` (live) receives a copy of a certificate that live replica `x` holds.
  Unconditional and unfenced, like byte repair. `certFence` is unchanged.

No certificate step reads Durability's `acknowledged` flag. `replyQuorum_acknowledged`
shows the reply log is sound for it.

Readiness has a store side and a reader side.

- Store: `RecordDurable c` (for some write quorum, every live member holds
  `rcert _ c`), `ObjectDurable o`, and `CatReady c` (the record, its manifest and
  every payload of its image are durable). These state durability; a reader cannot
  evaluate them, because it cannot tell a lost replica from an unreachable one.
- Reader: `Responded q`: every member of read quorum `q` answered. Only live
  replicas answer, and a lost replica never answers again under the same identity
  (`live` never returns to `true`), so this is `∀ x ∈ q, live x`. `ScanReady q c`:
  members of `q` returned the record's commit certificate, its manifest certificate
  and every payload certificate. It reads only the answers.
- `scanReady_iff_catReady`: on every reachable state and every responding `q`,
  `ScanReady q c ↔ CatReady c`. Right to left is quorum intersection (`meet w q` is
  in `q`, answered, so is live, so still holds the copy written to `w`). Left to right
  is the all-quorum certificate write: any certificate a member returns is on every
  live member of the write quorum it was written to.

`AdoptGuard`: a protocol step that makes a record committed needs `CatReady` in the
pre-state. This covers the writer's own `commit` and adoption by `enumerate`.
`Guard := (AdoptGuard ∧ e' = advance s t e) ∨ (t = s ∧ CertStep s e e')`, where
`advance` erases the certificates of lost replicas and logs the writer's replies.

## Concrete scan and the implementation step

`ScanCodec r` says the recovery theory's scan type can carry any decode/readiness
pair (`build`, `decoded_build`, `ready_build`). `ParaleanHardened.Example.codec`
instantiates it. `certScanValue codec q` is the scan recovery computes from the
answers of `q`:

- decoded: a member of `q` returned the record's bytes (`QuorumCatalog`);
- ready: `ScanReady q`.

`ScanEnumerate codec p q`: recovery reads a responding read quorum, computes
`certScanValue` and applies the `enumerate` state change
(`ParaleanRecovery.scanEffect`). It checks no ghost precondition.

## Results

All `Reachable`, by induction over the real `Next`. Axioms: `propext`,
`Classical.choice`, `Quot.sound`.

Invariant `Inv`:

- `rcert x c` implies the record's bytes are acknowledged,
  `certFence c = some (tokenRank (recordToken c))`, and `RecordDurable c`;
- `ocert x o` implies `o` is acknowledged and `ObjectDurable o`;
- `certFence c = some k` implies `k = tokenRank (recordToken c) ≤ fence`;
- every committed record is `CatReady` and has `certFence c = some rank`;
- every reply in the writer's log is for an acknowledged object;
- every parent of a record holding a commit certificate is `CatReady`.

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
  Certificate repair never sets `certFence`, so it cannot certify a stale record.

Parents (the orphan commit):

- `record_cert_parents_ready`: every parent of a record holding a commit
  certificate is `CatReady`.
- `record_cert_ancestors_ready` (needs the coupled recovery assumptions): every
  ancestor of such a record is `CatReady`, so it is `ScanReady` in the scan of every
  responding read quorum. By induction over parent paths
  (`ParaleanRecovery.ancestor_iff_parent_path`): a ready parent has a durable commit
  certificate, which a live replica holds, so its own parents are ready.
- `orphan_record_cert_rejected`: a commit certificate for a record with a parent
  that no responding read quorum shows ready is not a certificate step.
- `orphan_not_adopted` (necessity): a record with an ancestor that the scan of `q`
  does not mark ready is not admissible for that scan, so `enumerate` never adopts
  it. Without the parent check a record could be certified over a parent that was
  acknowledged but never committed (its writer was fenced out first), and recovery
  could never adopt it (TLA `fencing_commit_orphan` breaks `RecoveryAdopts`).

Readiness and recovery:

- `catReady_storageReady`: `CatReady` implies the base `StorageReady`.
- `committed_catReady`: every committed record stays certified under any loss allowed
  by the failure envelope.
- `catReady_scanReady`, `scanReady_catReady`, `scanReady_iff_catReady`: reader
  readiness over a responding read quorum equals store readiness.
- `responded_exists`: the failure envelope supplies a responding read quorum.
- `certScanValue_covers`: on every reachable state, the scan of a responding read
  quorum decodes and marks ready every committed record. This discharges the base
  `enumerate` precondition, which reads the ghost `committed` history; the
  precondition itself is unchanged (weakening it would break the `CatalogComplete`
  invariant of `ParaleanRecovery`).
- `certScanValue_sound`: a record the scan marks ready is `CatReady` (so adopting it
  passes `AdoptGuard`) and passes the base `StorageReady` test.
- `scan_enumerate_step`: from every reachable state, an implementation enumerate
  (`ScanEnumerate`) is a step of this layer. `ParaleanHardened.scan_enumerate_hardened`
  and `ParaleanHardened.sreachable_iff` lift this to the joint model.
- `certified_recovery`: from any reachable state, any responding read quorum and any
  committed record, `ScanEnumerate`, a reconstruction and a historical selection select
  the record in three steps of this layer. Every known record after the scan is
  `CatReady`.

Joint model: `ParaleanHardened.hardened_certified_recovery` lifts `certified_recovery`
to all five guards. `ParaleanHardened.Example.hardened_nonvacuous` recovers by
`ScanEnumerate` through `codec`; the scan decodes record `false` (rank-1 token, bytes
and manifest acknowledged under fence 1, no commit certificate) and rejects it, and
recovery selects record `true`. `ParaleanHardened.Example.hardened_scan_adoption`:
with record `false`'s certificates written under fence 1, the same scan over the
same bytes adopts record `false` through `enumerate` (`AdoptGuard` holds by
certificates) and selects it as the unique head.

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
- `fencing_commit_orphan` (on `FencingLive`): `CommitCert` without the parents check;
  `RecoveryAdopts` fails. The Lean counterpart is the parent premise of
  `CertStep.record`.
- `fencing_no_cert_repair` (on `FencingLive`): no `CertRepair`; `RecoveryAdopts`
  fails.

The TLA `Scan` still decides durability over live replicas, and its certificates are
written per replica; it has not been updated to the read-quorum readiness and
all-quorum certificate writes of the Lean model.

### Certificate repair in Lean

The Lean model has `repairRecord`/`repairObject` steps, and they preserve every
invariant (a copy names a record or object whose properties are already
established), so `scanReady_iff_catReady` is unchanged. Lean does not need repair
for readiness to persist: `RecordDurable`/`ObjectDurable` quantify over the *live*
members of a write quorum, certificates are written to a whole write quorum at once,
and a lost replica never rejoins, so durability never decays under the failure
envelope (`committed_catReady`). TLA needs `CertRepair` for liveness because its
`CertDurable` requires a fully live write quorum holding the certificate, which a
loss destroys. The contract this implies: an implementation that replaces a lost
replica with a new member of the write quorum (a membership change, not modelled in
Lean) must copy existing certificates to it before counting it towards durability;
that copy is the repair step.

## Implementation contract

- Certificate writes (commit certificates and object certificates) are single
  transactional writes that become readable only once they reach a write quorum (a
  consensus-replicated store such as etcd `Txn`, DynamoDB `TransactWriteItems` or
  FoundationDB). A store where a reader can see a certificate on one replica before
  the write completes does not meet this contract.
- The commit certificate write is conditional on the fence item, and is issued only
  after the writer holds a write quorum of replies for the record bytes. Object
  certificates likewise follow the writer's own write-quorum replies.
- Recovery waits until every member of some read quorum has answered, and decides
  readiness from those answers alone.
- A commit certificate write reads the parents' commit, manifest and payload
  certificates on a responding read quorum and aborts unless all are present.
- A lost replica never rejoins under the same identity; a replacement replica gets a
  new identity and receives copies of existing certificates (repair) before it
  counts towards a write quorum.
- Certificates are never garbage-collected. A lost replica's certificates are gone.

## Not established

- Replica replacement (membership change) is not modelled; repair only copies to
  existing live replicas. With write quorum = all replicas, no new certificate can
  be written after a loss.
- All-quorum certificate writes are an atomicity assumption about the store (above),
  not derived from per-replica writes. With per-replica writes, a reader that sees a
  certificate on one replica would need write-back before adopting.
- The writer's reply log is recorded at Durability's `Ack` step; the per-reply
  arrival of stable-write acknowledgements is not modelled separately.
- `Responded q` is the model of "every member of `q` answered"; timeouts and the
  choice of which quorum to wait for are not modelled.
- Base-model theorems stated with `ReadyScan` or a fixed scan (RecoveryAdequacy,
  CompletionRecovery, Protocol, the `CatalogFencing` examples) remain base-model
  results.
- Liveness (`RecoveryAdopts`) is checked only in TLA; Lean shows the certificate
  side of adoptability (`record_cert_ancestors_ready`), not workspace identity or
  buildability of ancestors.
