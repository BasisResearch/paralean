# P2 storage (FoundationDB 7.3 + Garage)

Implements [docs/store.md](../../docs/store.md): FoundationDB metadata (API 730), an
S3-compatible payload store (Garage 2.4.1 behind `s3-guard`, which refuses deletes),
transactions T1–T7, recovery by certificates, an audit and client-side fault injection.
Log, findings and deviations: [docs/p2-log.md](../../docs/p2-log.md).

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
`up.sh` lowers FDB's operating-space reserve (`min_available_space_ratio`), because /data on
the shared box is ~98% full and the default 5% reserve throttles all writes.

## Layout

| Path | Contents |
|---|---|
| `crates/store` | library `paralean_store` |
| `crates/cli` | `paralean-p2` CLI (status, assign, rotate, put/get, publish-demo, checkpoint-demo, discover, recover, audit, check-p1, import-p1, stress) |
| `crates/s3-guard` | S3 passthrough refusing DELETE, DeleteObjects and bucket-config changes |

## Module → transaction → guard

| Module / function | Transaction | Lean / TLA guard |
|---|---|---|
| `writer::publish`, `meta::t1_body` | T1: owner, epoch and head CAS on every target record; marker, revisions, receipt, heads and the publisher's `cert` in one transaction; payloads and the staged marker acknowledged by S3 first | TargetNames `PrepareOk`/`PublishOk`/`advance`; AckCertificates `PublishWrite`; TLA `target_no_epoch_fence`, `target_no_head_update`, `target_stranded_head`, `cert_stranded_publication`; PublicationReceipts (receipt checked before T1) |
| `writer::certify`, `meta::t2_certify` | T2: needs `marker/<g>` and an existing certificate | AckCertificates `put` (`known n d`); TLA `cert_put_unknown`, `cert_scan_raw_marker` |
| `Controller::rotate`, `meta::t3_rotate` | T3: read-modify-write of `fence`, `token/<k+1>` signed by the authority; never an atomic add | CatalogFencing rotation; "each rank issued once" |
| `Controller::reassign`, `meta::t4_reassign` | T4: owner := new, epoch+1, head kept | TargetNames `reassign` |
| `writer::commit_record`/`stage_record`, `meta::t5_body` | T5: `token.rank = fence`, token issued to holder, snapshot `ocert`, predecessor's `rcert` and snapshot `ocert`; record + `rcert` | CatalogFencing first write; CatalogCertificates `CertStep.record`; TLA `fencing_unfenced_commit`, `fencing_commit_orphan` |
| `writer::certify_object`, `meta::t6_object` | T6: only with an `Acked` proof (own PUT echo or verified GET) | CatalogCertificates `CertStep.object`; TLA `fencing_cert_unacked` |
| `writer::repair_cert`, `meta::t7_repair` | T7: unconditional, unfenced copy; signature verified; certified bytes must already exist | CatalogCertificates `repairRecord`/`repairObject`; TLA `fencing_no_cert_repair` |
| `recovery::discover` | paginated `cert/` scan; raw markers ignored; heads per name | AckCertificates `scan_between`; Recovery `reconstruction_iff` |
| `recovery::recover_catalog` | paginated `catalog/` scan; ready = rcert + snapshot/payload/manifest ocerts; admissible = ready ∧ buildable ∧ workspace ∧ predecessor admissible; unique head | CatalogCertificates `ScanEnumerate`, `selected_fenced`, `orphan_not_adopted` |
| `audit` | published ⇒ certified, cert ⇒ marker, metadata ⇒ S3 object, one head per target, fenced rcerts, no orphan commits, ranks 1..fence | HARDENED `hardened_safe` conjuncts |
| `s3` | PUT with `x-amz-checksum-sha256` = ID, echo required; GET re-hashed, mismatch = missing | store.md "Content-addressed writes" |
| `faults` | unknown commit results (landed or not), interleaved actions, crashes, S3 timeouts, corrupt reads | store.md "P2 obligations" |

## Tests (all against the live FDB and Garage)

library unit tests (PCE strictness, domains, objects, P1 golden vectors), `guards.rs` (13: one
per transaction guard and S3 rule, plus partial-batch scans), `fixtures.rs` (9 regression
fixtures), `faults.rs` (10 fault-injection scenarios), `property.rs` (proptest interleavings
with faults, invariants after each step), `crates/cli/tests/multiprocess.rs` (12 worker
processes with injected aborts and SIGKILLs).
