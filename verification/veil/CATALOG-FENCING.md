# Fenced catalogue writes

`ParaleanCatalogFencing` guards `ParaleanProtocol.Next`. In the base protocol only `commit`
checks a token, so a stale writer can Put a fresh catalogue object via storage steps,
which `enumerate` adopts, `automatic` selects and the completion guard accepts.

## Model

- Hypothesis `recordToken : record → token`: the token embedded in record `c`'s object
  `.catalog (encode c)`.
- `Extra := record → Option Nat`: ghost `writtenAt`, the fence at the first step that
  newly stores or acknowledges the record's object. Set once, never changed.
- `NewWrite s t c`: the step newly stores `c`'s object on a replica or newly
  acknowledges it.
- `Fenced s c`: `tokenRank (recordToken c) = fence` (pre-step). The `writer` flag of the
  recovery component is not read.
- `CopySource s c`: a live replica holds `c`'s bytes. This is a positive read: the
  writer names the replica it read the bytes from, and that replica answered.
- `Guard`: every new write is `Fenced` or has a `CopySource` (a repair copy, or the Ack
  of bytes already on a write quorum); `e' = update e`. The guard reads the fence
  register, the record's token, the store delta and one live replica the writer read.
  It never decides that *no* replica holds the bytes. Commit keeps its base check
  `writer ∧ tokenRank epoch = fence`.
- `FirstWrite s t c` (specification only, not read by the guard): a new write while
  no replica held the bytes (`¬ StoredSomewhere`). `firstWrite_fenced`: under the guard
  every first write is `Fenced`, because a first write has no source replica.
- `Next (s,e) (t,e') := ParaleanProtocol.Next s t ∧ Guard s e t e'`; `guard_stutter`,
  `reachable_protocol` (existing theorems transfer).

## Results (no `sorry`; axioms: propext, Classical.choice, Quot.sound)

- `present_fenced` (no assumptions) and `catalog_objects_fenced`: every record whose
  catalogue bytes are on some replica or that is acknowledged, and every committed record
  (including those adopted by `enumerate`), has `writtenAt c = some (tokenRank (recordToken c))`
  and `tokenRank (recordToken c) ≤ fence`. That is, it was first written while its token
  was the current fence. Later copies, Acks and commits may happen under a newer fence.
- `selected_not_stale` / `completion_not_stale`: the same for the selected record
  (automatic or historical) and for the record behind `FinishStep`.
- `firstWrite_fenced`, `stale_first_write_rejected`: a first write of a record whose
  token rank differs from the fence is not a hardened step.
- `guard_enabled_iff`: the guard reads only the pre-step fence, the record's token,
  the store delta, and for an unfenced write one live replica holding the bytes.
- `fenced_put_enabled`: a first write whose token has the fence's rank is enabled
  (assumes `encode` injective). `repair_put_enabled`, `ack_unfenced`: a Put or an Ack of
  a record a live replica holds is a hardened step at any fence and any token.
  `no_first_write_step`, `guard_of_fenced_writes`: step-building helpers.
- `Example.fenced_recovery_execution`: a writer commits record `true` under fence 0.
  A replica and the desktop are lost; the fence rotates to 1. A first write of a fresh
  rank-0 record is disabled (the base Put is enabled). `automatic` then selects the
  fenced record (`writtenAt = some 0`).
- `Example.late_ack_and_repair_execution`: record `true` (rank 0) is first written to one
  replica under fence 0. The fence rotates to 1. A repair Put copies it to the other
  replica, then it is acknowledged and committed (base commit under the new epoch). Both
  steps are hardened steps although the token is below the fence; the old
  every-write-fenced guard would reject them. The committed record has `writtenAt = some 0`.
- The examples above recover with the base model's fixed scan `idScan` (record `true`
  decoded and ready), checked against ghost acknowledgement by the base guard. They
  exercise the fence, not readiness; recovery from a scan computed from certificates
  is in `ParaleanHardened.Example`.
- `Example.unfenced_stale_selection` (necessity): in the base protocol the fence is
  rotated to 1, then the rank-0 record is first written and acknowledged; `enumerate`
  adopts it and `automatic` selects it. The hardened `Next` rejects that first write.
  Base steps with the same ghost bookkeeping record `writtenAt = some 1 ≠ some 0`.

## Implementation contract

- The fence is a single linearizable register. A first write must be a transactional
  conditional write that checks the fence item and writes the record in one atomic
  operation, for example an etcd `Txn` comparing the fence key, DynamoDB
  `TransactWriteItems` with a `ConditionCheck` on the fence item, or a FoundationDB
  transaction reading the fence key. A plain S3 conditional put (`If-None-Match` or
  `If-Match` on the object itself) does not suffice: it cannot condition one key on
  another.
- Fence rotation is a linearizable write to the fence register.
- Record bytes carry their token unforgeably (signature or integrity contract), so a
  repair cannot alter the embedded token.
- The check compares ranks. Distinct tokens of equal rank would both pass; the ownership
  service must issue at most one token per rank.

## Not established

- First-write fencing alone does not stop adoption of a stale record. A record first
  written before a rotation can be repaired, acknowledged and committed after it
  (`late_ack_and_repair_execution`). The fix is a fenced commit record:
  [CatalogCertificates](CATALOG-CERTIFICATES.md). There, adoption and commit need
  certificates, and the record's commit certificate is a conditional write on the
  fence. `ParaleanHardened` composes both layers.
- The unfenced branch needs the writer to have read the bytes from a live replica
  (`CopySource`). Whether that read happened is not separately modelled: the guard
  takes the replica as a witness. The TLA model has the same shape (a fenced `Put` and a
  `Repair` from a named live source replica).
- The base `enumerate` readiness (`StorageReady`) reads ghost acknowledgement. The
  hardened path reads certificates instead (`CatalogCertificates.certScanValue`), and
  recovery's implementation step (`CatalogCertificates.ScanEnumerate`) is lifted into
  a hardened step by `ParaleanHardened.scan_enumerate_hardened`.
- Per-process tokens are not modelled. "Stale" means a token rank that differs from
  the stored fence. The recovery component's `writer` flag is local authorisation;
  it is not store state and the guard does not read it.
- Catalogue objects `.catalog n` with `n` outside the range of `encode` are not records
  and are unconstrained. `fenced_put_enabled`, `repair_put_enabled` and `ack_unfenced`
  assume `encode` is injective.
- A physical state cannot show when bytes were first written; both systems can reach the
  same final store. Only histories with a post-rotation first write are excluded.

TLA: `verification/tla/Fencing.tla`. Three replicas, majority quorums, a fence
register in the store, two writers that acquire the fence by rotating it (fence
1..3, so a writer can re-acquire under a fresh token). Steps: fenced first-write
`Put`; `Repair` from a named live source replica; unfenced `Ack`; fenced `CommitCert`;
`Scan` adopting records whose certificates are durable on live replicas. Ghost
`writtenAt` is reset when a record's last copy is lost. 922,366 distinct states
(replica symmetry), no violation. Invariants: `StaleNeverStored`, `CertFenced`,
`KnownFenced`, `SelectedFenced`, `NoLateAckedKnown`, `ScanFindsCertified`.

Mutations:

- `fencing_unfenced_put`: no fence check on `Put`; `StaleNeverStored` fails.
- `fencing_repair_disguised`: `Repair` without a source copy; `StaleNeverStored` fails.
- `fencing_unfenced_commit`, `fencing_unfenced_commit_selected`: no fence check on
  `CommitCert`; `CertFenced`, `SelectedFenced` fail.
- `fencing_stale_selected`: `Scan` adopts on a live byte quorum; a record written
  before rotation and acknowledged after it is adopted (`NoLateAckedKnown` fails).
- `fencing_cert_unacked`: `CommitCert` before the Ack; `ScanFindsCertified` fails.

Witnesses (expected to be reachable): recovery after rotation, replica loss and
desktop loss selects the old fenced record (`NeverRecoveredAfterRotation`); a writer
re-acquires the fence and its new record is recovered (`NeverReacquiredRecovered`);
an old-token Ack (`NeverLateAck`) and an old-token repair (`NeverLateRepair`) after
rotation.
