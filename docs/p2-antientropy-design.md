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

There is also a relay gap: `export()` reads only the sender's local `cert/` and
`tcert/`. If A publishes a tombstone and B receives it, B's receiver certificate
does not prove that B was the target's original author. A later B→C push can
fail T10 even though A→B succeeded. Verified origin evidence must remain
forwardable across any number of relays.

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
when their addition changes transferable evidence. A new verified foreign
certificate, including one attached to an item already `Present`, also gets an
evidence event. A repair or repeated import which changes no visible state emits
no event. Echoes of imports generate at most one publication event and one event
per distinct certificate per deployment.

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

Publication bundles include **all** relevant verified certificates: this
deployment's own `cert/` or `tcert/` plus original certificates retained in
`xcert/`. An `xcert` is forwarded byte-for-byte with its original signer,
replica and object binding; relay identity is transport metadata, never a
replacement signer. The receiver re-verifies every signature, maps writer and
replica to a configured origin deployment, and stores each distinct certificate
under its original provenance key. A certificate from a relay is insufficient
as proof of the origin when an origin constraint applies. For a tombstone,
T10's author check selects a verified **original publisher** certificate whose
writer is the target revision's author workspace; a relay's local receiver
certificate is only additional acknowledgement evidence. For a target-name
group, the evidence must include a trusted publisher certificate from that
target's configured home; the relay's own certificate cannot confer target
ownership.

An item already present locally still processes and commits newly received
valid evidence. The new `xcert` key and its change event are written atomically;
the original publication and local certificate remain untouched. If a key
exists with identical bytes, return `Present` without a log event. If the same
provenance key holds different bytes, report a certificate conflict and leave
it unchanged. Because each immutable certificate is recorded once per
deployment, repeated A↔B relays settle without an echo storm. The receiver
cursor advances only after this evidence update is durable.

## Group chunk metadata

The published `GroupManifest` specification has `terms: TermTable | list chunk`,
but P2 currently holds `Opaque(Kind::Group)` and cannot enumerate references.
Add one explicit, self-identifying encoding for **new** chunked groups. The PCE
body inside the existing `v0/group` hash preimage is:

```
string "paralean-group-chunked-v1"
uvarint 1                         // envelope format
bytes core                        // producer's canonical group core, opaque to P2
list ChunkRef                     // logical term-table order, may repeat an ID
ChunkRef := Id (PCE bytes[32]) ; uvarint byte_length
```

The full PCE body, including every ordered chunk ID and length, is hashed with
the existing `v0/group` domain. The object is still an `Opaque { kind: Group,
pce }`, so the current `Package.group` field and P3 struct literals need no
change. `Package.chunks` already carries the bytes for upload. A new P2 helper
can build this wrapper from `(core, ordered chunk objects)` and return `Opaque`.
P2 validates the wrapper's exact PCE, nonempty core, bounded reference count,
each chunk length in `1..=64 MiB`, and absence of trailing bytes; it does not
interpret the core's Lean declarations. An unsupported `paralean-group-chunked-*`
magic or malformed v1 wrapper is a precise `UnsupportedGroupEncoding` or
`InvalidGroupEncoding` error, never an empty chunk list.

At publish, derive the set of `(ID, length)` from `Package.group.pce`; require
that `Package.chunks` contains exactly those IDs (duplicate logical references
need only one object), and that each chunk hashes to its ID and has the declared
length. Upload all chunks, then verify local S3 acknowledgement of every
referenced ID before T1. The order of group and chunk PUTs is immaterial because
T1 follows all acknowledgements. The same parser on receive drives `Fetch` of
every chunk and local acknowledgement before T9. Store a derived
`gchunks/<groupID>` index in T1/T9 for cheap enumeration, but reparse the
authenticated group object and compare it to the index when serving or auditing;
the index cannot add or omit a reference silently. The network service can
stream the deduplicated set in ID order while preserving logical order in the
group bytes. Since `gchunks` is set in the publication transaction, a cursor
event never observes a published group without its chunk index.

Existing P1 `paralean-group-v3` bytes and IDs remain unchanged. They are the
`LegacyOpaque` case: P2 transfers the group object exactly as before and marks
its chunk coverage `unknown`, even if a caller supplies additional unbound
`Package.chunks`. No S3 bucket listing or signed sidecar can prove their
completeness. This keeps old fixtures and P3 remote imports working. New
producers and consumers may adopt the chunked wrapper later; P2's metadata and
anti-entropy path can be implemented and tested without editing P1 or P3.

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

A relay forwards the source's signed record, token, fence history, commit and
object certificates with their source deployment identity, even if it learned
the record through another relay. The relay's `xcatalog/` copy is only a cache
of that source evidence. The destination validates the original source
authority and certificate writer bindings, then writes the same
source-qualified keys. A relay cannot relabel its copy as a locally fenced
record or strip source identity from a certificate.

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
Persist and pin the config under `federation/config` in the deployment's FDB
root **only while the deployment is new**: no published markers, tombstones,
target assignments, or committed catalogue records. The pin transaction scans
these prefixes and writes the config in one serializable transaction. Joining
an existing local deployment requires a separate migration with an explicit
write barrier and complete state validation; P2 refuses it. Stop all old
binary writers before pinning. The trusted-store implementation assumption is
that every writer thereafter runs the upgraded code; an old binary that writes
the FDB keys directly is outside this protocol's enforcement.

T1, T4, T8, T9 and T10 read the persisted config in **their own FDB transaction**,
even when their `Store` handle was opened before the config was pinned. No
cached or optional handle field may bypass it. T1 classifies every revision
name against the configured target-home map *before* looking for a local
`target/<name>` record. If the name is a configured target, T1 requires this
deployment to be its home and requires the target record, owner, epoch and
head guards; absence of a record is an error, never ordinary-name publication.
T4 rejects assignment or reassignment of a name not declared as homed here.
T9 checks the same map for every received revision name and requires origin
evidence from that home for target groups. T8 and T10 reject a tombstone of a
group declaring any configured target name, even when no local
`target/<name>` record exists on this deployment. Their tombstone guards use
the pinned name classification in addition to the local target-key check.
These transactions avoid an old handle's local-mode path.
`prepare_target` reads the pinned config from FDB before returning a binding;
T1 repeats the transactional check at commit. A network service configured for
federation refuses to start if its own store or any peer has no matching
pinned config. The deployment cannot silently switch from federated to
unconfigured mode while serving writes. The mapping is immutable for this
protocol version; migration needs a separately modelled handover. Ordinary
non-target names keep Workspaces' deterministic collision rendering. Existing
single-deployment APIs remain usable on stores which have never joined a
federation; they do not authorize a federated peer. This is a protocol rule
beyond the current single-store TargetNames model and must pass a TLA model
with a guard removal mutation before implementation.

In federated mode, configure source-bound writer sets: a writer ID may certify
for its configured origin deployment, and its certificate's replica must match
that origin's pinned replica ID. The existing two-instance demo may reuse a
writer ID on both sides; it remains a non-federated local test, not evidence of
home authentication. New federation tests use distinct writer identities (or
an explicit unambiguous writer-to-source binding) across deployments.

One immutable `marker/<group>` key fixes one position per group in Workspaces'
`Layout`. If two deployments validly publish the same group with different
marker IDs, T9 cannot replace either without violating that model. Report
`MarkerConflict {group, local marker, remote marker, source}` and retain the
remote signed bundle for diagnosis; cursor processing may record this as terminal
until an explicit resolution protocol exists. Multiple marker positions or a
tie-break would be a new layout model and storage schema, so neither is inferred
from ordinary name conflict rules. A same-name conflict between **different**
non-target groups remains convergent under the existing deterministic render.

## Relay verification cases

- A publishes a group and tombstone; B pulls from A; C pulls only from B.
  C receives A's original group and tombstone certificates inside B's bundles,
  verifies the tombstone author against the target revisions, and ends with
  the same published set as A and B. B's receiver certificate alone must fail
  the author check.
- A is the pinned home of target `x`; A publishes its target group; B pulls
  from A; C pulls only from B. C accepts the group only with A's original
  certificate and its configured home proof. Dropping A's certificate or
  replacing it with B's local certificate fails closed, even if C has no
  `target/<x>` key.
- A commits a catalogue record; B pulls it and C pulls from B. C retains the
  exact A-signed record, source token/fence evidence and source certificates
  under `xcatalog/A`, `xrcert/A` and `xocert/A`; its local `rcert/` remains empty.
- A and B exchange the same evidence repeatedly after convergence. Cursor and
  log counts stop changing. Deliver an additional valid original certificate
  for a group already present at B: B stores and forwards that evidence exactly
  once; a crash before cursor advancement replays without duplicates.

## Exact `store.md` delta to apply after integration

1. In **Layout**, add `aelog/<versionstamp>/<operation>`,
   `aecursor/<source>/<generation>`, `aepending/<source>/<event>`, and
   `gchunks/<group>`. Add source-qualified `xcatalog/`, `xrcert/`, `xocert/`
   namespaces. State that foreign certificates are evidence and cannot satisfy
   a local quorum. Document the persisted federation config digest, source
   identity, original writer-to-deployment/replica binding, the new-only config
   pin transaction, and transactional T1/T4/T8/T9/T10 home checks. `xcert/`
   evidence is exportable after any relay.
2. In **Transactions**, require T1/T8/T9/T10 and ready T5 to append their
   change event atomically. T9/T10 also accept new foreign evidence for an
   existing publication, appending only a new-evidence event when the bytes
   were absent. Add a transaction for durable cursor/pending
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
