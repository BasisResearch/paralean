# P2 anti-entropy network service design

Status: implementation design for `m-p2`; the existing in-process T9/T10 exchange on
`p2-rest` remains the receive guard. This document records the intended `store.md`
delta until the integration branch lands. It does not claim that the service exists.

## Baseline and safety boundary

`p2-rest` exports the entire discovered set into a `Vec<Item>` on every round. It
transfers groups, capsules, staged markers and tombstones, but cannot enumerate
chunks from the opaque `v0/group` bytes. It exchanges neither catalogue records nor
their certificates. Its T9/T10 receiver verifies IDs, receipts and foreign
certificates, acknowledges payload locally, checks dependencies, writes its own
certificate, and keeps sender certificates under `xcert/`. These guards remain the
authority for applying a received publication. The network layer must never count
foreign evidence as a local `cert/`, `tcert/`, `rcert/` or `ocert/`.

## Ordered change stream and bounded protocol

Append `aelog/<commit-versionstamp>/<operation>` in the **same FDB transaction**
that first commits T1, T8, T9, T10, or a ready T5 catalogue record. Values name
`Group(groupID)`, `Tombstone(tombstoneID)`, or `Catalogue(recordID)`; the transaction
does not embed payload bytes in the log. FDB's commit versionstamp orders these keys
by commit order. An insertion that commits after a page's read version has a larger
versionstamp than every event in that page. Scanning by object ID or ordinary key
order would be unsound: an insert behind the cursor could be missed forever. The
versionstamp mutation and the publication must succeed or fail together. T2/T6
certificates that appear later get their own `Certificate(kind, ID, signer)` events
when their addition changes transferable evidence. A repair or repeated import
which changes no visible state emits no event. Echoes of imports generate at most
one event per newly received item per deployment.

The server exposes a small authenticated protocol: `Hello` (deployment identity,
protocol version, federation configuration digest and cursor generation),
`Changes(after_cursor, max_items, max_bytes)` (an ordered page and a sealed
`next_cursor`), and `Fetch(kind, ID)` (one content-addressed object, streamed with
a 64 MiB object cap). A page contains event descriptors and certificate/metadata
bundles only; large S3 objects are fetched separately. Clamp the server limits
(initial design: 128 descriptors and 1 MiB encoded metadata per page; client
in-flight object limit 2, object cap 64 MiB). If a single metadata bundle exceeds
the byte limit, page its certificate list and use a continuation for that item;
never silently drop it. Every scan follows FDB's `more()` flag, including a short
partial batch. The server never first calls full `discover()` or builds a full
`export()` vector to serve a page. It reads only the log range and materializes
the selected items. A finite page is a consistent snapshot at one FDB read version;
the cursor advances only across completely enumerated events.

Each configured peer has a periodic client task (default interval 5 s with jitter,
one immediate round on startup, bounded retry backoff). One direction is a pull
from a peer's server; each side schedules its own pull. A supervisor keeps one
active pull per peer. Transport must authenticate peer deployment identity and
limit request size, frame size, concurrent fetches and timeouts. The existing CLI
`sync` may use the same protocol for a forced round. The service runs independently
of controller and validator processes, with a dedicated sync writer whose key is
trusted by participants. It must avoid storing peer Garage/FDB credentials and
must work over an ordinary network address.

The receiver stores `aecursor/<source-id>/<generation>` with the last fully
processed event and a bounded, durable `aepending/<source-id>/<event-key>` entry
for any item that cannot yet be applied. A cursor may advance past a deferred item
only after its pending entry is committed, with its authenticated metadata bundle,
missing dependency IDs, and a source address for retry. Do **not** persist whole
64 MiB payloads in FDB. Fetch each object by ID again after restart. Persist
`Applied`, `Present`, and terminal diagnostic outcomes, so a poison event does not
stall all later events; preserve the evidence and reason for operator inspection.
Replay the pending queue on startup, after each page, and when an observed
dependency arrives; bound attempts and use retry backoff. A transient missing
payload or parent stays pending. If the process crashes between import and cursor
commit, retry is safe because T9/T10 and object PUTs are idempotent. Cursor write
and pending insertion must be atomic; application may precede them. The source log
is retained until every peer has acknowledged a cursor, or indefinitely in P2.
Compaction requires a separately verified snapshot/bootstrap protocol. A changed
generation without a bootstrap is a hard error, never an empty continuation.

The receiver requests a group's group object, capsule(s), staged marker, and
every enumerated chunk before T9. It re-hashes each body and gets a local S3
acknowledgement before metadata. A corrupt object at the sender keeps the event
pending and reports the exact `(source, kind, ID)`. A missing object at the
receiver is repaired by a later ID fetch, even if the publication is already
`Present`; periodic object scrubbing is separate from change stream replay.

## Group chunk metadata

The published `GroupManifest` specification already has `terms: TermTable | list
chunk`, but the P2 store's `Opaque(Kind::Group)` API does not decode that field.
For a group encoding whose terms field carries chunk references, define the
canonical list of chunk IDs as the sorted, duplicate-free references parsed from
the **hashed group bytes**. The writer must reject missing or unacknowledged
referenced chunks before T1. Store a derived `gchunks/<groupID>` index (chunk IDs,
optionally sizes/checksums for batching) in T1 and T9, but treat it as a cache:
readers reconstruct and compare it against the group bytes before using it.
Derived metadata does not change an existing group ID. A versioned group format
with explicit tagged inline/chunk terms is required if the current P1 encoding
does not expose those references unambiguously; the format change must be
coordinated with P1/P3 owners. Old or unknown group formats remain opaque and
continue to replicate by group object ID. They may be marked `chunks unknown`,
never falsely advertised as having zero chunks. If the sender's package did
carry chunks but its immutable group bytes do not bind their IDs, full chunk
replication cannot be proven; report that limitation rather than guessing from
S3 listing. A signed sidecar alone is insufficient to prove completeness.

## Catalogue exchange

A `Catalogue(recordID)` bundle contains the signed `CatalogRecord`, its
`CommitCert`, token and source fence evidence, the snapshot and source/build
manifests, plus every `ObjectCert` required for that source record's readiness.
All signatures and IDs are verified against the **source deployment's** trusted
authority and writers. Referenced S3 objects are transferred by ID with local
acknowledgement. Parent catalogue records are fetched or queued first. The
receiver stores the bundle under a source-qualified foreign namespace such as
`xcatalog/<source>/<id>`, `xrcert/<source>/<id>`, and
`xocert/<source>/<kind>/<id>/<writer>`. This preserves source fence order and
certificate provenance. Foreign ranks cannot be compared with the local `fence`
or used to write local `rcert/`; local `recover_catalog` keeps its current
meaning. A read API can enumerate verified foreign catalogues by source and
report source-ready versus missing dependencies. Promoting a foreign snapshot
to a local checkpoint requires a separate, locally fenced T5 commit by a local
holder; it is not an anti-entropy side effect.

Do not equate receipt verification with catalogue readiness. A source record is
accepted as source-ready only when its source commit certificate and every
required source object certificate verify, its predecessor chain is complete,
and every named object is acknowledged locally. An incomplete record stays in
`aepending/`. Invalid source certificates get a precise diagnostic and do not
become local certificate keys.

## Target names and marker conflicts

Federated mode uses a pinned, identical `FederationConfig`: a total mapping
`home(target name) -> deployment`, an immutable config digest, trusted deployment
identity and writer-to-deployment binding. The deployment must be identified by
authenticated peer credentials and trusted writer membership; a certificate's
`replica` field alone is an assertion by its signer. A target can be assigned,
prepared, published and reassigned only at its home, where one linearizable
`target/<name>` record preserves TargetNames' owner/epoch/head chain. Every
target name declared by one group must have the same home. On receive, a group
declaring a target name is accepted only with valid publication evidence from
that home; it is copied as a publication but does **not** update the receiver's
target record. A missing, mismatched or unknown home mapping is rejected before
mutation, including when the receiver currently has no local target record.
Persist and pin the config under the deployment's FDB root before enabling the
service. T1 and T4 read its digest and home assignment in their own transaction;
`prepare_target` checks the same pinned config before returning a binding. A
network service configured for federation refuses to start if the store has no
matching pinned config. The deployment cannot silently switch from federated to
unconfigured mode while serving writes. The mapping is immutable for this
protocol version; migration needs a separately modelled handover. Ordinary
non-target names keep Workspaces' deterministic collision rendering. Existing
single-deployment API constructors remain usable on stores which have never
joined a federation; they do not authorize a federated peer. This is a protocol rule beyond the
current single-store TargetNames model and must pass a TLA model with a guard
removal mutation before implementation.

One immutable `marker/<group>` key fixes one position per group in Workspaces'
`Layout`. If two deployments validly publish the same group with different
marker IDs, T9 cannot replace either without violating that model. Report
`MarkerConflict {group, local marker, remote marker, source}` and retain the
remote signed bundle for diagnosis; cursor processing may record this as terminal
until an explicit resolution protocol exists. Multiple marker positions or a
tie-break would be a new layout model and storage schema, so neither is inferred
from ordinary name conflict rules. A same-name conflict between **different**
non-target groups remains convergent under the existing deterministic render.

## Exact `store.md` delta to apply after integration

1. In **Layout**, add `aelog/<versionstamp>/<operation>`,
   `aecursor/<source>/<generation>`, `aepending/<source>/<event>`, and
   `gchunks/<group>`. Add source-qualified `xcatalog/`, `xrcert/`, `xocert/`
   namespaces. State that foreign certificates are evidence and cannot satisfy
   a local quorum. Document the persisted federation config digest, source
   identity, and the T1/T4/prepare home checks.
2. In **Transactions**, require T1/T8/T9/T10 and ready T5 to append their
   change event atomically. Add a transaction for durable cursor/pending
   advancement and one for importing a verified foreign catalogue bundle;
   neither changes the local fence or target records. T1/T9 validate and
   record derived chunk references when the group encoding exposes them.
3. In **Content-addressed writes**, require acknowledgement for every
   group-referenced chunk before publication/receive. A fetched chunk is
   verified by SHA-256 and acknowledged locally before any metadata names it.
4. In **Refinement**, explain why commit-versionstamp pagination covers every
   committed publication despite concurrent inserts, why a deferred event is
   durably queued before cursor advancement, and why a foreign catalogue is
   source-qualified and cannot be a local fenced commit. Preserve FDB's
   `more()` rule. State the old opaque group limitation explicitly.
5. In **What the refinement does not cover**, record cross-deployment target
   homing and immutable marker conflict handling. Link the new TLA target-home
   model and its mutation case once they pass.
