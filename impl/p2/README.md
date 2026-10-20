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
a nearly full shared disk can otherwise throttle writes; check `df -h /data` before runs.


## Scheduled network anti-entropy

New federated deployments pin identical public membership and target homes before
any publication with `paralean-p2 federation-init federation.json`. Each deployment
has distinct writer IDs, replica ID and transport key. Generate the transport seed
with `paralean-p2 ae-keygen /private/path/ae.seed`; use its printed public key with
`paralean-p2 federation-member A PUBLIC_KEY` to produce the public member object
from that deployment's `PARALEAN_KEYS`. Never copy the private seed to a peer.

A configuration has this shape (replace the placeholder member objects with the
command output, including every deployment's own entry):

```json
{
  "deployment": "A",
  "members": {"A": {"...": "public member fields"}, "B": {"...": "public member fields"}},
  "target_homes": {"Example.target": "A"},
  "trusted_validators": ["64 hexadecimal characters per trusted validator public key"],
  "signing_seed_file": "/private/path/ae.seed",
  "listen": "127.0.0.1:25001",
  "peers": {"B": "127.0.0.1:25002"},
  "sync_writer": "w0",
  "interval_ms": 5000
}
```

Run `paralean-p2 ae-service federation.json` on each deployment. It serves signed
TCP requests and schedules incremental pulls with jitter and retry backoff. Peers
need public keys and service addresses; they need no remote FDB or S3 credentials.
The transport authenticates bytes but does not encrypt them. Normal local publish
and audit commands use `PARALEAN_DEPLOYMENT=A` and
`PARALEAN_FEDERATION_CONFIG=/path/federation.json` to load the same public trust.
The persisted home rules apply even to handles opened before federation pinning.
`ae-service federation.json --once` performs one bounded round per configured peer;
it does not promise that the entire backlog is drained. `ae-status federation.json`
prints durable progress and pending diagnostics. SIGINT/SIGTERM drain service tasks
before the CLI shuts down its FDB network thread.
Terminal conflicts are archived separately, freeing their active pending slots and
fragments. `ae-status` lists the first 64 archived diagnostics per peer; `--once`
continues to report a conflict while any archived diagnostic exists. Its terminal
statistic is a lower bound, not the total archive size.

The service uses atomic commit-versionstamp events, durable cursors and pending
fragments, 1 MiB metadata frames, 64 KiB fragments, an 8 MiB metadata limit per
event, and 64 MiB objects buffered in memory. At most two peers pull concurrently;
missing objects/dependencies remain retryable without blocking unrelated events.
Generation changes require a verified bootstrap; v1 provides neither migration of
an existing deployment nor log compaction. New chunked group envelopes bind ordered
chunk IDs and lengths into the group hash; old opaque groups retain their IDs and
have unknown chunk coverage. Catalogue records retain source-qualified certificates
and never advance the receiver's local fence. Receipt-only marker variants converge;
placement or revision conflicts retain a precise terminal diagnostic.
See [the protocol and store delta](../../docs/p2-antientropy-design.md).

For Garage RPC partitions, start an instance with `PARALEAN_GARAGE_NETSPLIT=1`, then
use `scripts/proc.sh garage-split 2` and `scripts/proc.sh garage-heal`. The proxy
identifies Garage peers by their configured private loopback source address and
cuts existing as well as new cross-partition connections.

On a shared box, split fault runs into `FAULT_SCOPE=fdb` (six FDB processes,
`triple`, one Garage) and `FAULT_SCOPE=garage` (one FDB, three Garage nodes,
replication 3). Set `STRESS_WORKERS=1`, prebuild with one Cargo job, then use
`SKIP_BUILD=1 PHASE=stress|fixtures|beyond` with `fault-redundancy.sh` for each scope.
The destructive `PHASE=dataloss` additionally requires
`I_KNOW_THIS_DESTROYS_THE_INSTANCE=1` and runs last on a disposable own instance.
`PARALEAN_TEST_WORKER_LIMIT=3` runs all multiprocess worker configurations in waves.
The default combined cluster example above needs a larger process budget.
`scripts/ae-cli-smoke.sh` checks two running instances using distinct private keys,
public peer configuration, service restart and graceful SIGTERM. Set
`PARALEAN_A_INSTANCE` and `PARALEAN_B_INSTANCE` explicitly.

For the P3 remote gate on a busy shared host, run
`python3 scripts/remote-gate.py RUNDIR` with the usual P3 environment. This loads
the unchanged `impl/p3-remote/scripts/gate.py` scenario and replaces only its
fixed validator startup sleep with a bounded readiness wait.

## Layout

| Path | Contents |
|---|---|
| `crates/store` | library `paralean_store` |
| `crates/cli` | `paralean-p2` CLI (status, assign, rotate, put/get, publish-demo, checkpoint-demo, tombstone-demo, discover, recover, audit, check-p1, import-p1, sync, stress, verify-acks) |
| `crates/s3-guard` | S3 passthrough refusing DELETE, DeleteObjects and bucket-config changes; several upstreams with failover |
| `crates/netsplit` | partitions between local fdbservers (proxy per process, ConnectPacket source identification) |
| `crates/garage-netsplit` | Garage RPC partitions, source-bound private loopback addresses |
| `crates/ae-wire` | bounded signed TCP request/response framing |
| `crates/ae-service` | scheduled incremental pulls and durable retry handling |

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
| `writer::tombstone`, `meta::t8_body`, `meta::tombstone_guards` | T8: staged S3 copy acknowledged first; tombstone and the publisher's tombstone certificate (`v0/tcert`) in one transaction; target published *and certified*, same file, older, deleted by its author (OPEN-19 default), not a target-name group, named receipt present and its validator not revoked | Workspaces tombstone = revision of its target (`ancestors_closed`, `StageGuard`); AckCertificates `PublishWrite`, `guard_necessity` applied to tombstones |
| `antientropy::import`, `meta::t9_body`, `meta::t10_body` | T9/T10: receive a group or tombstone from another deployment: hashes and signatures verified, the receipt and job envelope pass P3 binding checks; in pinned federation mode, target groups require their home controller and original home certificate, the validator not revoked here (read in T9), payloads acknowledged here, parents/target present, then the receiver's own certificate (its replica, its key) with the sender's certificates kept as `xcert/` evidence; receipt-only variants converge while placement conflicts are diagnosed; foreign observations never advance local target records | AckCertificates `put` (`known n d`); §8.3 "receiving requires a live certificate"; Groups `receive` |
| `recovery::discover` | paginated `cert/` and `tcert/` scans; raw markers and tombstones ignored; heads per name; rendered files | AckCertificates `scan_between`; Recovery `reconstruction_iff`; Workspaces `render`, `Live`, `PosLt`, `render_carried` |
| `recovery::recover_catalog` | paginated `catalog/` scan; ready = rcert + snapshot/payload/manifest ocerts; admissible = ready ∧ buildable ∧ workspace ∧ predecessor admissible; unique head | CatalogCertificates `ScanEnumerate`, `selected_fenced`, `orphan_not_adopted` |
| `audit` | published ⇒ certified, cert ⇒ marker, metadata ⇒ S3 object, one head per target, fenced rcerts, no orphan commits, ranks 1..fence; the same for tombstones; `xcert/` evidence verifies | HARDENED `hardened_safe` conjuncts |
| `s3` | PUT with `x-amz-checksum-sha256` = ID, echo required; GET re-hashed, mismatch = missing | store.md "Content-addressed writes" |
| `faults` | unknown commit results (landed or not), interleaved actions, crashes, S3 timeouts, corrupt reads | store.md "P2 obligations" |

## Tests (all against the live FDB and Garage)

library unit tests (PCE strictness, domains, objects, P1 golden vectors), `guards.rs` (13: one
per transaction guard and S3 rule, plus partial-batch scans), `fixtures.rs` (9 regression
fixtures), `faults.rs` (10 fault-injection scenarios), `property.rs` (proptest interleavings
with faults and tombstones, invariants after each step), `tombstones.rs` (6: rendering after
recovery, uncertified tombstones ignored, T8 guards, T8 faults, concurrent revision and
tombstone, revoked named receipt), `antientropy.rs` (9, two clusters: convergence, rejection of
corrupt, forged and untrusted items, deferral, receive faults, rot repair, marker conflicts,
foreign target names, receipts and revocations under the receiver's key ring;
plus a proptest over delivery orders with drops, duplicates, corruption and truncation),
`crates/cli/tests/multiprocess.rs` (12 worker processes with injected aborts and SIGKILLs).
The network service suite has 14 cases covering authenticated relay, source
certificates/catalogues, home targets, chunks, incremental pages, durable fragment
restart, missing-object repair, compatible variants and archived conflict diagnostics.
