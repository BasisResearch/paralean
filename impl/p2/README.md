# P2 storage (FoundationDB 7.3 + Garage)

Implements [docs/store.md](../../docs/store.md): FoundationDB metadata (API 730), an
S3-compatible payload store (Garage 2.4.1 behind `s3-guard`, which refuses deletes),
transactions T1–T7, recovery by certificates, an audit and client-side fault injection;
tombstones (§11.4, T8) and anti-entropy between deployments (T9, T10); fault runs inside
and beyond FoundationDB `triple` and Garage replication 3.
Log, findings, deviations and store.md deltas: [docs/p2-log.md](../../docs/p2-log.md).

## Reproduce

```
scripts/bootstrap.sh     # user-space FDB 7.3.79 + Garage 2.4.1 under $PARALEAN_P2_PREFIX, rustup if missing
scripts/up.sh            # fdbserver (ssd, port 4689), Garage (18439-18441), s3-guard (18433)
scripts/test.sh          # cargo test --workspace against the live services
scripts/check-mutations.sh   # guard-removal mutations; the listed tests must fail
scripts/fdb-kill-test.sh     # SIGKILL fdbserver under stress workers, restart, audit
scripts/p1-golden.sh [STORE…] # P1 declId = P2 group ID for every group of P1 stores (default: captures F01–F13)
scripts/down.sh
```

Instances: with `PARALEAN_INSTANCE=<name>` every script works on a separate cluster under
`$PARALEAN_P2_PREFIX/inst/<name>` (own data, credentials, run directory and ports from
`PARALEAN_PORT_BASE`, saved in its `instance.sh`); without it, the default cluster above,
unchanged. The runs in docs/p2-log.md use three:

```
# two independent single-process deployments for anti-entropy
PARALEAN_INSTANCE=ae-a PARALEAN_PORT_BASE=21200 scripts/up.sh
PARALEAN_INSTANCE=ae-b PARALEAN_PORT_BASE=21300 scripts/up.sh
PARALEAN_INSTANCE=ae-a PARALEAN_PEER_INSTANCE=ae-b scripts/test.sh     # second deployment on ae-b
PARALEAN_INSTANCE=ae-a PARALEAN_PEER_INSTANCE=ae-b scripts/check-mutations.sh
# FDB triple (6 fdbservers in 6 zones, 5 coordinators, behind netsplit) + Garage 3 nodes, replication 3
PARALEAN_INSTANCE=ft PARALEAN_PORT_BASE=21100 PARALEAN_FDB_PROCS=6 PARALEAN_FDB_REDUNDANCY=triple \
  PARALEAN_FDB_COORDINATORS=5 PARALEAN_NETSPLIT=1 PARALEAN_GARAGE_NODES=3 PARALEAN_GARAGE_REPLICATION=3 scripts/up.sh
PARALEAN_INSTANCE=ft PHASE=stress   scripts/fault-redundancy.sh   # stress workers under faults within tolerance
PARALEAN_INSTANCE=ft PARALEAN_PEER_INSTANCE=ae-b PHASE=fixtures scripts/fault-redundancy.sh  # tests under chaos
PARALEAN_INSTANCE=ft PHASE=beyond   scripts/fault-redundancy.sh   # beyond tolerance: outage, then recovery
scripts/proc.sh fdb kill|pause|resume|start|wipe <i>; scripts/proc.sh garage ... <j>; scripts/proc.sh split <i>...|heal
```

`proc.sh split` partitions fdbservers through `netsplit`, a user-space proxy on each
process's public port (no root or iptables on the shared box): it identifies the connecting
process from FDB's ConnectPacket and blackholes every link across the cut until `heal`.
`up.sh` lowers FDB's operating-space reserve (`min_available_space_ratio`), because /data on
the shared box is ~98% full and the default 5% reserve throttles all writes.

## Layout

| Path | Contents |
|---|---|
| `crates/store` | library `paralean_store` |
| `crates/cli` | `paralean-p2` CLI (status, assign, rotate, put/get, publish-demo, checkpoint-demo, tombstone-demo, discover, recover, audit, check-p1, import-p1, sync, stress, verify-acks) |
| `crates/s3-guard` | S3 passthrough refusing DELETE, DeleteObjects and bucket-config changes; several upstreams with failover |
| `crates/netsplit` | partitions between local fdbservers (proxy per process, ConnectPacket source identification) |

## Module → transaction → guard

| Module / function | Transaction | Lean / TLA guard |
|---|---|---|
| `writer::publish`, `meta::t1_body` | T1: owner, epoch and head CAS on every target record; marker, revisions, receipt, heads and the publisher's `cert` in one transaction; payloads and the staged marker acknowledged by S3 first | TargetNames `PrepareOk`/`PublishOk`/`advance`; AckCertificates `PublishWrite`; TLA `target_no_epoch_fence`, `target_no_head_update`, `target_stranded_head`, `cert_stranded_publication`; PublicationReceipts (receipt checked before T1) |
| `writer::certify`, `meta::t2_certify` | T2: needs `marker/<g>` and an existing certificate | AckCertificates `put` (`known n d`); TLA `cert_put_unknown`, `cert_scan_raw_marker` |
| `Controller::rotate`, `meta::t3_rotate` | T3: read-modify-write of `fence`, `token/<k+1>` signed by the authority; never an atomic add | CatalogFencing rotation; "each rank issued once" |
| `Controller::reassign`, `meta::t4_reassign` | T4: owner := new, epoch+1, head kept | TargetNames `reassign` |
| `writer::commit_record`/`stage_record`, `meta::t5_body` | T5: `token.rank = fence`, token issued to holder, snapshot `ocert`, predecessor's `rcert` and snapshot `ocert`; record + `rcert` | CatalogFencing first write; CatalogCertificates `CertStep.record`; TLA `fencing_unfenced_commit`, `fencing_commit_orphan` |
| `writer::certify_object`, `meta::t6_object` | T6: only with an `Acked` proof (own PUT echo or verified GET) | CatalogCertificates `CertStep.object`; TLA `fencing_cert_unacked` |
| `writer::repair_cert`, `meta::t7_repair` | T7: unconditional, unfenced copy; signature verified; the certificate names this store's replica σ; certified bytes must already exist | CatalogCertificates `repairRecord`/`repairObject`; TLA `fencing_no_cert_repair` |
| `writer::tombstone`, `meta::t8_body`, `meta::tombstone_guards` | T8: staged S3 copy acknowledged first; tombstone and the publisher's tombstone certificate (`v0/tcert`) in one transaction; target published *and certified*, same file, older, deleted by its author (OPEN-19 default), not a target-name group, named receipt present | Workspaces tombstone = revision of its target (`ancestors_closed`, `StageGuard`); AckCertificates `PublishWrite`, `guard_necessity` applied to tombstones |
| `antientropy::import`, `meta::t9_body`, `meta::t10_body` | T9/T10: receive a group or tombstone from another deployment: hashes and signatures verified, payloads acknowledged here, parents/target present, then the receiver's own certificate (its replica, its key) with the sender's certificates kept as `xcert/` evidence; one marker per group (conflicts reported); names homed here as targets refused | AckCertificates `put` (`known n d`); §8.3 "receiving requires a live certificate"; Groups `receive` |
| `recovery::discover` | paginated `cert/` and `tcert/` scans; raw markers and tombstones ignored; heads per name; rendered files | AckCertificates `scan_between`; Recovery `reconstruction_iff`; Workspaces `render`, `Live`, `PosLt`, `render_carried` |
| `recovery::recover_catalog` | paginated `catalog/` scan; ready = rcert + snapshot/payload/manifest ocerts; admissible = ready ∧ buildable ∧ workspace ∧ predecessor admissible; unique head | CatalogCertificates `ScanEnumerate`, `selected_fenced`, `orphan_not_adopted` |
| `audit` | published ⇒ certified, cert ⇒ marker, metadata ⇒ S3 object, one head per target, fenced rcerts, no orphan commits, ranks 1..fence; the same for tombstones; `xcert/` evidence verifies | HARDENED `hardened_safe` conjuncts |
| `s3` | PUT with `x-amz-checksum-sha256` = ID, echo required; GET re-hashed, mismatch = missing | store.md "Content-addressed writes" |
| `faults` | unknown commit results (landed or not), interleaved actions, crashes, S3 timeouts, corrupt reads | store.md "P2 obligations" |

## Tests (all against the live FDB and Garage)

library unit tests (PCE strictness, domains, objects, P1 golden vectors), `guards.rs` (13: one
per transaction guard and S3 rule, plus partial-batch scans), `fixtures.rs` (9 regression
fixtures), `faults.rs` (10 fault-injection scenarios), `property.rs` (proptest interleavings
with faults and tombstones, invariants after each step), `tombstones.rs` (5: rendering after
recovery, uncertified tombstones ignored, T8 guards, T8 faults, concurrent revision and
tombstone), `antientropy.rs` (8, two clusters: convergence, rejection of corrupt, forged and
untrusted items, deferral, receive faults, rot repair, marker conflicts, foreign target names;
plus a proptest over delivery orders with drops, duplicates, corruption and truncation),
`crates/cli/tests/multiprocess.rs` (12 worker processes with injected aborts and SIGKILLs).
