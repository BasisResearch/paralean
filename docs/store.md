# Store choice and refinement argument

Status: decided for the P0 gate ([plan](plan.md) P0), signed off 2026-10-05. It
resolves OPEN-9 of [p0-interfaces.md](p0-interfaces.md). The argument
below is written, not mechanised: it maps the store operations of the
[hardened protocol](../verification/veil/HARDENED.md) to concrete operations and
argues that every concrete behaviour is a behaviour of the model.

## Decision

- **Self-hosted by default.** Both stores run on machines we operate (for P2, the
  aws-dev box); no managed cloud service is required. Moving to a managed
  S3-compatible service later changes only an endpoint.
- **Metadata store: FoundationDB** (7.3 series; P2 pins 7.3.79, client API version 730), one
  self-hosted cluster in one region. FoundationDB is itself replicated with
  consensus; it is the only coordinated component. It holds markers, revisions, receipts, tombstones,
  publication certificates, catalogue records, commit and object certificates, the
  catalogue fence, issued tokens and target owner/epoch/head records.
- **Payload store: a self-hosted S3-compatible store** with strong
  read-after-write consistency and durable PUT acknowledgement. P2 runs Garage
  (AGPL-3.0, the preferred licence), single node, replication factor 1, consistent
  mode; MinIO community binaries are no longer distributed. Garage checks
  `x-amz-checksum-sha256` and echoes it. Clients use only the plain S3 API, so another
  store is a change of endpoint. Amazon S3 (one bucket, one region, no cross-region
  replication) is a drop-in alternative. Payloads are immutable and
  content-addressed, so any copy with the right hash is valid. It holds group
  manifests and term chunks, capsules, export/snapshot manifests and build logs.
- **Write order**: payload first, verify its hash, then the metadata transaction
  that references it. Metadata never names an object the writer has not seen
  acknowledged.

This is option (a) of the plan. Option (b), self-managed replicas implementing the
quorum interface directly, stays available for deployments that put storage on the
workers; nothing below depends on it.

## Candidates

Requirements from the models: a transaction that checks one key (fence, target
epoch) and writes others atomically; linearizable reads for guards and recovery;
enumeration of every key of a kind; limits that fit Mathlib-scale use; an operating
cost a small team can carry.

Sizing. Mathlib at the pin is about 10^5 commands; a long multi-agent project may
reach 10^6 groups. Per group the metadata is a marker (about 200 B plus `rootPath`,
which is O(anchor depth) at roughly 60 B per level), one revision per public name
(about 150 B), a receipt (about 300 B) and a certificate per writer (about 150 B
with an Ed25519 signature). Taking 2 KB per group, 10^6 groups is about 2 GB before
replication. A publication transaction writes 1 to 10 KB. A catalogue commit for a
snapshot of 10^5 groups would need 10^5 object certificates if written at once
(15 MB); see [Monotone checks](#monotone-checks-across-transactions).

| | FoundationDB | etcd | DynamoDB |
|---|---|---|---|
| Write conditional on another key | Yes. Any key read in the transaction is in its read-conflict set; commit fails if it changed. Arbitrary read and write sets | Yes. `Txn` compares any keys, then puts | Yes. `TransactWriteItems` with a `ConditionCheck` on the fence item; up to 100 items, 4 MB |
| Consistency | Strict serializability; reads at a read version from the proxies are linearizable (do not set `causal_read_risky`) | Linearizable reads by default (not `serializable`) | Serializable transactions; `ConsistentRead` on the base table only; global secondary indexes are eventually consistent |
| Limits | value 100 kB, key 10 kB, transaction 10 MB, 5 s per transaction | request 1.5 MiB; storage quota 2 GB by default, about 8 GB recommended maximum; whole keyspace in one bbolt file per member | item 400 KB; 100 items per transaction |
| Fit at 10^6 groups | Yes, with paginated scans and spill of oversized values | No: a few GB of keys plus MVCC history exceeds the recommended size | Yes, with paginated `Scan` and no index reads on guarded paths |
| Unknown outcome | Explicit `commit_unknown_result` error; transactions are written to be idempotent | Client timeout; no explicit status | `ClientRequestToken` makes a `TransactWriteItems` idempotent for 10 minutes |
| Operating cost | Highest: cluster file, coordinators, redundancy mode, backups, client multi-version upgrades | Low | Lowest (managed); AWS only; per-request pricing |
| Fault injection in P2 | Runs locally and in CI; processes can be killed and partitioned | Same | Not reproducible locally: DynamoDB Local does not model failures |

etcd fails on size. Both FoundationDB and DynamoDB fit. FoundationDB is chosen
because its transaction model is the model's primitive (condition on any key read),
it states unknown outcomes explicitly, it runs anywhere including the P2 fault
injection rig, and it ties the project to no cloud. Its cost is operational. If that
cost is unacceptable, DynamoDB is the fallback under the same mapping, with these
changes: no global secondary index reads on any guard or scan; fence rotation as a
conditional update (`fence = k`, set `k+1`); a `ClientRequestToken` on every
transaction; revisions stored inside the marker item to stay under 100 items.

Linearizable reads matter in four places: the target record read before preparing,
the fence read inside a fenced write, the certificate reads of discovery, and the
readiness reads of recovery. All four use FoundationDB read versions, never a cache.

## Layout

FoundationDB keys use the tuple layer; `id` is the 32-byte ID of §1.2. One prefix
per kind keeps kinds apart, and IDs are domain-separated hashes, so a key of one
kind cannot be read as another.

| Key | Value | Written by |
|---|---|---|
| `marker/<group>` | Marker (§8.2, §11.1) | publication transaction |
| `revision/<id>`, `receipt/<id>`, `tombstone/<id>` | the object bytes | publication or staging |
| `cert/<group>/<writer>` | Cert (§8.3) | publisher, receivers, committers |
| `target/<name>` | `{owner, epoch, head}` (§7) | controller (assign), owner (publish) |
| `catalog/<id>` | CatalogRecord (§9) | fenced catalogue write |
| `rcert/<catalog id>` | CommitCert | fenced commit-certificate write |
| `ocert/<kind>/<id>` | ObjectCert | after the object's acknowledgement |
| `fence` | current rank | controller (rotation) |
| `token/<rank>` | signed token `{rank, holder}` (domain `v0/token`, signed by the fence authority) and the issuing request ID | rotation transaction |
| `treq/<request>` | the rank T3 issued for this request | rotation transaction |
| `assign/<name>/<epoch>` | `{owner, request}` of the assignment that set this epoch | reassignment transaction |
| `areq/<name>/<request>` | the epoch T4 set for this request | reassignment transaction |
| `lamport/<agent>` | last issued Lamport time (optional; a local fsynced file also suffices) | the agent |

`treq/`, `assign/` and `areq/` are grow-only request indexes. They make the
effect of T3 and T4 recognisable for any retry, including a late duplicate that
arrives after other rotations or reassignments; the request ID in `token/<rank>` or
in the target record alone recognises only a retry before the next change.

Values of unsigned objects (markers, revisions, tombstones) are wrapped in an
envelope: `0x00 ‖ stored bytes`, or, for a value over 64 kB (in practice only a deep
`rootPath`), `0x01 ‖ object ID ‖ blob ID`. The blob is a content-addressed S3 object
(domain `v0/blob`) holding the stored bytes, PUT and acknowledged before the
transaction. The object's bytes and ID are unchanged; only where the bytes live
differs.

Signed objects (receipts, catalogue records, `cert`, `rcert`, `ocert`, tokens) have
`ID = H(domain, body)` with the signature outside the ID (§6), so they cannot be
stored as their preimage alone. Their value is the PCE pair
`bytes(preimage(body)) ‖ bytes(signature)`, where the signature is Ed25519 over the
ID. Readers verify both the body's domain and the signature.

S3 keys are `obj/<kind>/<hex id>`, one kind per domain: `group` (`v0/group`),
`chunk`, `capsule`, `snapshot`, `manifest` (new domain `v0/manifest`: a snapshot's
`sourceRoot` and `buildReceipt`), `blob`, and `marker` (the acknowledged marker
copy, below). Object certificates use the same kind names: the certificate of the
snapshot a catalogue record names is `ocert/snapshot/<m>`.

## Content-addressed writes

1. Encode the object and compute `ID = SHA-256(preimage)`, where the stored bytes
   are the preimage `"paralean\x00" ‖ domain ‖ "\x00" ‖ PCE(x)` (§1.2). Storing the
   preimage makes the object's own SHA-256 equal its ID.
2. `PUT obj/<kind>/<hex id>` with `x-amz-checksum-sha256` set to the ID. S3 rejects
   a body whose digest differs. Objects are at most 64 MiB (larger term tables are
   chunked, §1.3), so a single PUT and a full-object checksum always apply.
3. The writer treats `200 OK` with the echoed checksum equal to the ID as the
   acknowledgement. A timeout or error is not an acknowledgement; the PUT is
   retried, which is harmless because the key determines the bytes.
4. Only then does the writer run a metadata transaction naming the ID.

Readers always re-hash fetched bytes. With content addressing a verified read
returns the right bytes or nothing; corrupt bytes fail the hash and count as
nothing. With metadata
after payload, every ID named in committed metadata was acknowledged by S3 before
the metadata committed. S3 provides strong read-after-write consistency, so a GET
after the acknowledgement finds the object. On a store with only eventual
consistency the same two rules still give safety: a missing object is a delayed
read (the model's network isolation), never a wrong one. That store must still make
a `200 OK` durable.

## Transactions

Each concrete operation is one FoundationDB transaction. Every transaction is
idempotent: it reads whether its effect is already present and, if so, succeeds
without writing. For T3 and T4, which bump a counter, the effect is recognised by a
request ID: `token/<rank>` names the holder and request, the target record stores
the last reassignment's request ID, and the request indexes `treq/` and `areq/`
recognise any earlier request (see Layout).

| # | Transaction | Reads | Writes |
|---|---|---|---|
| T1 | Publish group `g` | `target/<x>` for each target name `x` of `g`; `marker/<g>` | `marker/<g>`, revisions, receipt if absent, `target/<x>.head`, `cert/<g>/<self>` |
| T2 | Certify `g` | `cert/<g>/<self>`; `marker/<g>`; one key of `cert/<g>/*` | `cert/<g>/<self>` |
| T3 | Rotate fence | `treq/<request>`; `fence` | `fence := k+1`, `token/<k+1>`, `treq/<request>` |
| T4 | Reassign target `x` | `areq/<x>/<request>`; `target/<x>` | `owner`, `epoch := epoch+1`, `head` unchanged; `assign/<x>/<epoch>`, `areq/<x>/<request>` |
| T5s | Stage catalogue record `c` (optional) | `catalog/<c>`; `fence`; `token/<rank>` | `catalog/<c>` if absent and `token.rank = fence`; succeeds without writing if present |
| T5 | Write and commit catalogue record `c` | `rcert/<c>`; `fence`; `token/<rank>`; `catalog/<c>`; `ocert/snapshot/<m>`; for each parent `p` of `c`: `rcert/<p>`, `ocert/snapshot/<image p>` | `catalog/<c>` if absent, `rcert/<c>` |
| T6 | Certify object `o` | none | `ocert/<kind>/<o>` |
| T7 | Repair certificate | an existing `cert`, `rcert` or `ocert` key | the same key on a replacement replica (unconditional, unfenced) |

Before T1 the publisher PUTs the marker's preimage to `obj/marker/<hex id>` and
waits for the acknowledgement. This is §8.2 step 2 ("the marker is durably
acknowledged"); T1 then writes `marker/<g>`. A copy whose T1 never commits stays
staged in S3, and discovery never reads it. T2 aborts unless `marker/<g>` exists
*and* at least one `cert/<g>/*` key exists: the writer must know `g` as published,
and a marker key alone is not evidence of publication (§8.3; AckCertificates
`guard_necessity`, TLA `cert_scan_raw_marker`).

T1 aborts unless, for every target name, `owner = self`, `epoch` equals the epoch
the proof was prepared under and `head` equals the head the proof revises. The last
condition is the compare-and-swap variant of TargetNames' atomicity note; with it
the owner need not serialize prepare and publish. T1 runs only after every object
of the package (manifest, chunks, capsule) is acknowledged by S3 and the receipt
signature has been checked. T5 aborts unless `token(c).rank = fence` and every
parent of `c` is itself committed (its `rcert` and snapshot certificate exist), so a
record is never committed over an acknowledged but uncommitted parent that recovery
could not adopt. T6 runs only after S3 acknowledged `o`. T7 applies only to
deployments that replace a metadata replica: a replacement must receive copies of
existing certificates before it counts towards a write quorum. With FoundationDB as
the single abstract replica, its own recovery provides this and T7 is not issued.
Where T7 is used (copying into a replacement cluster or namespace), the replacement
is a new physical copy of the same abstract replica σ. Certificate bodies name σ in
their `replica` field and are signed by their writers, so a copy keeps its bytes and
its `replica` field unchanged. A copy is accepted only if its signature verifies and
the certified object's bytes already exist at the target (the marker or record key,
or a verified S3 object).

## Refinement

### Abstraction

The model's store is one quorum system over replicas `ρ` with write quorums `W`,
recovery quorums `R` and `meet`. Instantiate it with **one abstract replica** `σ`,
the pair (FoundationDB cluster, S3 bucket), and `W = R = {{σ}}`, `meet = σ`. The
quorum assumptions hold trivially. The failure envelope (some recovery quorum
survives) becomes: the stores do not lose committed data. That is FoundationDB's
guarantee within its configured redundancy mode (`triple`, or `three_data_hall`
across three availability zones of one region) and S3's durability design.
Machine failures inside those bounds, and the stores' internal re-replication, are
invisible stuttering steps. Under this instantiation `Lose σ` is never enabled, so
the models' loss-tolerance results hold but are carried by the stores, not by the
protocol.

The abstraction function maps a concrete state (committed FoundationDB state at the
latest version, S3 contents, each process's local state) to an abstract hardened
state:

- `stored σ o` iff `o`'s key is present (FoundationDB) or `o`'s object is present
  (S3). `live σ` always.
- `acknowledged o` (ghost) iff some writer observed a successful commit or a
  verified `200 OK` for `o`.
- `cert σ g` iff some `cert/<g>/<w>` key exists. `certReply n g σ` iff
  `cert/<g>/<n>` exists.
- `ocert σ o` iff `ocert/<kind>/<o>` exists; `rcert σ c` iff `rcert/<c>` exists.
- `fence` is the `fence` key; `owner x`, `epoch x`, `head x` are the fields of
  `target/<x>`.
- `published g` iff `marker/<g>` exists. Each process's index, pending set and
  Lamport clock map to its `known`, `pending` and clock.
- History ghosts (`writtenAt`, `certFence`, `preparedEpoch`) are defined from the
  concrete history, as history variables.

Simulation relation: a committed transaction corresponds to a quorum of replicas
all holding each item it wrote (here the single quorum `{σ}`); an aborted
transaction corresponds to no write; a transaction with unknown outcome corresponds
to either all of its writes or none, with no acknowledgement observed.

### Atomic transactions as step sequences

A committed transaction maps to a fixed finite sequence of abstract steps, taken at
its commit version. Two facts make this sound. First, strict serializability makes
the transaction equivalent to executing alone at its commit version: every key it
read (including the fence and target records) has the value it read at that
version, because otherwise the commit fails. Second, no process observes the
abstract intermediate states, so each step only has to be enabled in the state the
previous step produced. The sequences are:

| Transaction | Abstract steps, in order |
|---|---|
| S3 PUT acknowledged | `Put σ o`; `Ack o {σ}` |
| T1 publish | one hardened step: `Put σ marker`; `Ack marker {σ}`; publish (TargetNames `PublishOk`, `advance` sets `head`) together with the publisher's certificate quorum (AckCertificates `PublishWrite`) |
| T2 certify | `CertStep.put n σ g` |
| T3 rotate | fence rotation (the fence register write) |
| T4 reassign | `reassign e x n` |
| T5s stage | `Put σ c` (a first write, fenced) and `Ack c {σ}`; when the bytes are present, `Ack c {σ}` only (unconditional) |
| T5 catalogue | `Put σ c` (a first write when `catalog/<c>` was absent, fenced); `Ack c {σ}`; `CertStep.record σ c` (fenced; parents ready) |
| T6 certify object | `CertStep.object σ o` |
| T7 repair | `CertStep.repairRecord` / `CertStep.repairObject` |

Each guard holds where it is taken. T1's publish is fenced by the epoch read in the
same transaction, and its certificate is written by a node that knows `g` as
published, which is AckCertificates' `known n d` premise; if the epoch check fails
the whole transaction aborts, so a failed publish never certifies (§8.2). T5's
first write and commit certificate both see `token.rank = fence`, and the
certificate follows the writer's acknowledgement of the record bytes, which is
CatalogCertificates' `acknowledged` premise. T6 follows the S3 acknowledgement of
`o`. After T1, `CertQuorumBy n g` holds, because `W = {{σ}}` and `certReply n g σ`.
Writing the certificate inside T1, not in a later T2, is required: TLA
`target_stranded_head` shows a published head can otherwise become undiscoverable
and block its target name forever (Lean `published_certified`).

### Abstractions one by one

**Per-replica storage, W and R.** One abstract replica, as above. Quorum
intersection is trivial; retention is the stores' guarantee.

**Durable acknowledgement.** For metadata, a FoundationDB commit returns only after
the mutation is durable on the transaction logs, so a returned commit is `Ack o {σ}`.
For payloads, a verified `200 OK`. A failed or timed-out PUT is `Put` without `Ack`
or nothing, both model behaviours (a partial upload stays staged).

**Acknowledgement certificates and reply logs.** A certificate is a key, separate
from the marker, never inferred from marker bytes. The writer's reply log is the
presence of its own `cert/<g>/<n>` key, which the store retains, so
`reply_survives` holds without a local log. Checkpoint commit requires the
committer's own certificate for every group (T2 before, or in, the commit
transaction).

**Physical scan and enumeration.** A fully live read quorum is an available
cluster. Discovery is a range read of `cert/`; catalogue recovery is a range read
of `catalog/` followed by point reads of `rcert/` and `ocert/` per record. At
10^6 keys a scan spans many transactions (5 s limit). It is still a model scan
because these key spaces only grow: nothing deletes a certificate, record or
marker. A paginated scan therefore returns a set `S` with every key committed
before the scan started in `S`, and every key in `S` committed at some version. So
`CertQuorum ⊆ S ⊆ published` (`scan_between`) holds, and the catalogue scan covers
every committed record (`certScanValue_covers`), exactly as for a single-version
scan. Readiness (`CatReady`) is likewise read per record and is monotone.

Refinement obligation: a page ends only where FoundationDB says the range is
exhausted. A scan continues from the last returned key while the range read reports
`more`, and never stops because a batch is shorter than the requested page size.
FoundationDB returns short batches when byte limits apply. A scan that treats a short
batch as the end returns a strict subset of the committed keys, which falsifies
`scan_between` and `certScanValue_covers`; recovery could then select an older
record. P2 found exactly this bug at 445 markers; regression test
`paginated_scan_follows_partial_batches`.

**Fence register and fenced first writes.** `fence` is one key. T5 reads it and
writes the record in one transaction, so it is the model's atomic check-and-write.
The implementation fences every catalogue write, not only the first. That only
removes behaviours (a repair or rewrite that the model allows unconditionally), and
removing behaviours preserves every safety property.

**Unfenced repair and acknowledgement.** With one abstract replica there is no
repair step: the stores' internal re-replication is invisible. A re-PUT of an S3
object is allowed at any fence; content addressing discharges the
existing-bytes rule, because the key fixes the bytes. An acknowledgement is a
client observation, not a write. The late-acknowledgement case of CatalogFencing
needs the record's bytes to exist without a commit certificate, which a single T5
(record and `rcert` in one transaction) never produces. If an unknown-outcome T5
committed before a rotation, it wrote the `rcert` too: the retry finds it and
succeeds, and adopting the record is correct, because it was fenced at its commit
version. The case therefore appears as a fenced staging write followed by the
commit T5. The staging write writes only `catalog/<c>`, conditional on
`token.rank = fence`. Its outcome is unknown and it committed before a rotation. The
writer resolves it after the rotation: the retry finds the bytes, an unconditional
acknowledgement of existing bytes. The commit T5 then reads the new fence and
aborts. The record exists without a commit certificate and is never adopted
(`stale_stays_uncertified`).

**Linearizable fence rotation.** T3 reads `fence = k` and writes `k+1` and
`token/<k+1>`. Two concurrent rotations both read `k`; one fails at commit, so each
rank is issued once. Rotation must not use an atomic add, which carries no read
conflict and would let two rotations both believe they issued a rank. Any T5 that
read `k` and commits after T3 fails.

**Target owner/epoch record.** `target/<x>` holds owner, epoch and head in one key,
so the preparer's single read is atomic. The abstract prepare is linearized at that
read. Between the read and T1 only the owner can move the head (only current
proofs publish), and the owner holds at most one staged proof per target name
(TargetNames conjunct (iii)), so only a reassignment can change the record; T1
then fails the epoch check. T1's head comparison makes this hold even if the owner
misbehaves locally. Groups declaring several target names read all their records in
one T1.

**Typed object constructors.** Each model constructor (`payload`, `manifest`,
`catalog`, `publication`) has its own key prefix and its own hash domain. A key of
one kind is never read as another, and an ID cannot verify as another kind's bytes
without a hash collision, which the models assume away.

### Monotone checks across transactions

FoundationDB bounds a transaction at 10 MB and 5 s, so a guard over 10^5 keys cannot
be checked in the transaction that relies on it. The facts these guards read
(certificates exist, objects acknowledged, records committed) are monotone: once
true at a version they stay true, because nothing is deleted and the stores do not
lose committed data. A guard established by reads at earlier versions therefore
still holds at the commit version of a later transaction. Catalogue commit uses
this: payload `ObjectCert`s are written by T6 when each object is first
acknowledged and reused by every later snapshot; T5 itself checks only the fence,
the record and the snapshot certificate (`ocert/snapshot/<m>`). The same applies to the committer's own
publication certificates before a checkpoint commit. Non-monotone facts (the fence,
target records) are always read inside the transaction that depends on them.

## What the refinement does not cover

- **Unknown commit outcomes.** The mapping is sound only if a writer resolves an
  unknown outcome (`commit_unknown_result`, a client timeout, a lost S3 response)
  before taking any step that depends on it, by retrying the idempotent transaction
  or reading back. A writer that crashes first maps to the model's crash. A writer
  that gives up and continues as if the write failed is outside the argument: its
  local index can disagree with the abstract `known` set.
- **Clocks.** The protocol uses no wall clock; only Lamport clocks. FoundationDB's
  5 s limit and the controller's failure-detection timeouts affect liveness only.
  Reassignment is safe at any time (TargetNames), and no timeout grants ownership.
- **Deletion and GC.** The scan and monotonicity arguments need grow-only key
  spaces. The bucket denies `DeleteObject` (or uses Object Lock); no FoundationDB
  role may clear the protocol's prefixes. Garbage collection needs a new model.
  Garage has neither bucket policies nor Object Lock, and a key with write
  permission may delete. In P2, deletes are refused by `s3-guard`, a byte-for-byte S3
  gateway in front of Garage. It refuses every `DELETE`, `POST ?delete` and every
  change to bucket configuration, and clients reach the store only through it.
  Credentials that reach Garage's own S3 port directly could still delete, so that
  port must be locked down. In P2 it is bound to 127.0.0.1, which still admits other
  users of the same machine. A shared deployment needs a firewall or network policy
  that admits only the gateway, and must keep Garage's S3 keys away from clients.
- **Backup and restore.** Restoring a FoundationDB backup rolls committed state
  back: acknowledged writes disappear and the fence can return to an issued rank.
  That violates the failure envelope. A restore is a new deployment, with the fence
  set above every rank ever issued.
- **Cross-region.** One region only. FoundationDB multi-region configurations, S3
  cross-region replication in the read path and DynamoDB global tables are
  outside the argument.
- **The stores' own claims.** FoundationDB's strict serializability and durability,
  and S3's consistency and durability, are trusted, not proved. S3 durability is
  probabilistic; the model treats it as absolute within the envelope.
- **The quorum-level results.** Under one abstract replica, the model's tolerance
  of losing individual replicas, certificate erasure on loss and the reply-log
  argument are exercised only in degenerate form. They matter again under
  option (b).
- **Encodings and signatures.** Hash collision resistance, signature
  unforgeability (receipts, tokens, certificates) and decoder schema validation are
  assumptions, as in the models.
- **Workspaces.** Placement, rendering and the git projection read only the
  replicated marker set and add no store operation; they are not part of this
  argument.

## P2 obligations from this choice

- Fault injection adds: `commit_unknown_result` on every transaction type; fence
  rotation and target reassignment between a read and a commit; S3 PUT timeouts
  with and without the object landing; killing FoundationDB processes within the
  redundancy mode; a paginated scan running across concurrent publications.
- Regression fixtures from the plan map as follows: a stale writer after rotation
  (T5 aborts); a put before rotation acknowledged after it (fenced staging write with
  an unknown outcome resolved after the rotation; the commit T5 aborts; never
  certified); a repair copy after rotation (S3 re-PUT, no catalogue
  effect); a target published just before a handover (T1 then T4; the head is in
  the record); a surviving marker without certificates (marker key present, no
  `cert/` key; discovery ignores it).
- A test asserts no metadata key names an object absent from S3, after every
  injected fault.
