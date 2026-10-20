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
active pull per peer. The signed TCP framing layer authenticates peer deployment
identity against the pinned transport public key, and limits frame size,
concurrent fetches and timeouts. The existing CLI
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

### Store API and wire metadata contract

The store exposes transport-independent, PCE-encoded types. All wire types have
a leading `uvarint format = 0`; enum tags are one byte, IDs are PCE `bytes[32]`,
and cursors are opaque bytes returned by the source. The transport authenticates
the peer and carries these bytes without rewriting them.

```
AeKind = GroupVariant(groupID, markerID) | Tombstone(tombstoneID)
       | Catalogue(sourceDeployment, recordID)
       | Evidence(kind, objectID, certificateID)
AeEvent = { key: bytes, kind: AeKind }       // key is commit-versionstamp order
AePage = { generation: Id, events: list AeEvent,
           next: option bytes, more: bool }

AePart = MetaFragment(metaKind, id, offset, totalLength, bytes)
       | ObjectRef(s3Kind, id, storedPreimageLength)
       | CertificateFragment(certKind, id, offset, totalLength, bytes)
AeBundlePage = { eventKey: bytes, afterPart: option uvarint,
                 parts: list (sequence:uvarint, AePart),
                 nextPart: option uvarint, complete: bool }

AePending = { sourceDeployment, generation, event: AeEvent,
              nextPart: option uvarint, missingCount: uvarint,
              state: Collecting | Deferred(reason) | Terminal(reason) }
AeProgress = { generation, cursor: option bytes }
AePendingPage = { entries: list AePending, next: option bytes, more: bool }
AeObjectPage = { refs: list (s3Kind, id, storedPreimageLength),
                 next: option bytes, more: bool }
```

`GroupVariant` materializes exactly one marker, its revision bytes, receipt,
signed job envelope, source publisher certificate, and S3 references for its
group, capsules, staged marker and chunks. Later certificates are separate
`Evidence` events, each pointing to exactly one immutable certificate;
materialization never gathers every certificate of a group. `Tombstone` does
the analogous work with its source publisher certificate. `Catalogue` includes
one signed record and source commit certificate; each additional object
certificate is an `Evidence` event. This event granularity ensures that an
evidence change for an already present item is delivered once without
re-exporting its whole publication. The part stream is deterministic for a
given event key; newly added evidence creates a new event, not new parts on an
old event. Fragment bytes are capped at 64 KiB, so oversized marker, receipt,
job or certificate metadata can be paged without a single unbounded frame.
Object bytes are fetched separately by `(kind, ID)` and have a 64 MiB cap.

The Rust API boundary for the service is:

```
Store::ae_identity() -> Result<AeIdentity>       // own deployment, replica, config digest
Store::ae_page(after, max_items, max_bytes) -> Result<AePage>
Store::ae_materialize(event, after_part, max_bytes) -> Result<AeBundlePage>
Store::ae_progress(source) -> Result<AeProgress>
Store::ae_pending_page(source, after, max_items) -> Result<AePendingPage>
Store::ae_missing_objects(source, event_key, after, max_items) -> Result<AeObjectPage>
Store::ae_save_progress(source, generation, cursor,
                        pending_upserts, pending_deletes, part_upserts) -> Result<()>
Writer::ae_import_staged(source, event) -> Result<Outcome>
```

`ae_page` bounds **encoded descriptors**, not materialized payloads; clamp
`max_items` and `max_bytes` server-side. Its `after` is exclusive, `next` is
the last returned key (or the input cursor for an empty page), and `more`
reflects the range's `more()` at the same FDB read version. A later commit has
a greater versionstamp, so another page will see it even if `more` was false.
`ae_pending_page` is likewise bounded and uses its own exclusive key cursor;
startup replay never loads the whole deferred queue at once.
`ae_missing_objects` pages the staged `ObjectRef` parts and returns only refs
whose local S3 GET is absent or corrupt. Its `after` is exclusive over the
stable part key. The client fetches these refs by ID from the peer, verifies
the stored preimage length and SHA-256, and obtains local S3 acknowledgements
before `ae_import_staged`. The import repeats the acknowledgement check, so a
concurrent loss yields `Deferred` without a metadata write. The structured
missing-object page is the scheduler's recovery path; it need not parse the
free-text `Outcome::Deferred(String)` reason.
`ae_materialize` caps the encoded part page and advances by stable sequence
number; a part never changes under the same event key. If a single metadata
object exceeds the store's object-size limit, report an explicit terminal
diagnostic. The receiver stores fragments under
`aepart/<source>/<event-key>/<sequence>` with an idempotent compare; it can
resume collection after a crash. `ae_save_progress` commits cursor advancement,
pending state and received fragments atomically for each bounded page. A fully
collected event calls `ae_import_staged`, which validates all assembled
metadata and locally acknowledged S3 refs; the following progress transaction
deletes its pending fragments. An import committed before that cleanup is
replayed idempotently. Root's scheduler owns signed TCP framing and retry policy; these
functions own FDB consistency and the receive guards.

`Hello` compares the authenticated deployment identity, pinned transport
public key and config digest with `ae_identity()` on **both** peers. It refuses
any unconfigured peer in federated mode. The response generation is a
persisted source UUID/ID, not a process-start nonce. V1 network service starts
only on a new deployment that pinned federation config before its first
publication, so every transferable write has an `aelog` event. An existing
local deployment with publications cannot enable this service; moving it into
a federation needs a separately designed write barrier, state validation and
backfill migration. V1 performs no hidden full scan. A changed generation
without a verified bootstrap resets no cursor silently.

The **union of publication and `Evidence` events** carries every relevant
verified certificate. A publication event carries only its initial publisher
certificate; each later local or foreign certificate has one immutable
`Evidence` event. A `GroupVariant` event carries that variant's receipt and
the signed job envelope it answers; without the job, the full P3 binding
cannot be checked. Each evidence certificate is forwarded byte-for-byte with
its original signer,
replica and object binding; relay identity is transport metadata, never a
replacement signer. The receiver re-verifies every signature, maps writer and
replica to a configured origin deployment, and stores each distinct certificate
under its original provenance key. Use `xcertv/<kind>/<object>/<certID>` for
new evidence: the existing `xcert/<kind>/<object>/<replica>/<writer>` cannot
hold two certificates by one writer for different marker IDs. Read old
`xcert/` entries for compatibility, then deduplicate by certificate ID. A
certificate from a relay is insufficient
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
identity, one Ed25519 transport public key per deployment, and
writer-to-deployment binding. The signed TCP handshake proves possession of the
matching private key over fresh nonces, deployment identities and the config
digest in both directions. The deployment must be identified by
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

Workspaces' `Layout` fixes one position and one carried record per group. It
does **not** require that the group have only one valid validator receipt;
PublicationReceipts needs an intact verified receipt for the group, and the
abstract AckCertificates relation certifies the group. P2's physical
certificate additionally binds a marker ID. Two markers for the same group
can therefore converge when their **only** difference is `receiptID`, provided
both receipts pass the full P3 bound check against their own signed job,
target epochs, pins and accepted verdict. Require byte equality for
`filePath`, `anchor`, `lamport`, `author`, `rootPath`, `lineageKeys`, and the
entire sorted revision-ID set; verify the revision bytes agree as well. These
are the fields that determine Workspaces' placement, carried ancestry,
names and dependency view. A receipt-only variant changes no modelled view.

Keep the original `marker/<group>` and `cert/<group>/<writer>` keys immutable.
Store additional valid markers under `mvariant/<group>/<markerID>` and local
certificates under `vcer/<group>/<markerID>/<writer>`; keep the original
publisher certificates byte-for-byte as foreign evidence under `xcertv/`.
Discovery and audit enumerate the legacy marker plus variants, verify each
variant's staged S3 copy and at least one matching local certificate, and
select the **lowest marker ID** among eligible receipt-only variants. The
selection is a deterministic physical representation of the same abstract
group, not a new Workspaces position rule. `Store::marker`, rendered files and
network export use the selected variant; export also carries the other valid
variants and their certificates so a later peer can make the same selection.
The receiver certifies each newly admitted variant locally in the transaction
that stores it. A variant already stored can acquire more valid foreign
evidence without replacing its local certificate or emitting repeated events.
Old certificates remain valid for their original variant; no key is rewritten
or cleared. This is necessary because simply replacing `marker/<group>` would
make old certificate signatures refer to a nonexistent current marker and
break the current audit's `cert_sound` check.

If any placement or carried revision field differs, return
`MarkerConflict {group, local marker, remote marker, differing_fields}` and
retain the remote signed bundle for diagnosis. A different revision set can
change Groups' registry meaning; different file, anchor or carried keys can
change Workspaces' render. Neither can be merged under the current models.
The P2 import path must not use `Receipt::admits` alone for this decision: P3's
`receipt::check` also binds the signed job, policy, checker, target names and
epochs. A same-name conflict between **different** non-target groups still
converges under the existing deterministic render.

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
- A and B publish the same group with identical placement and revisions but
  different valid receipt/job pairs. After exchange both retain both marker
  variants, the original and local certificates verify, the lower marker ID is
  selected at both, and audit is clean. A receive with one changed anchor or
  revision ID reports the exact differing field and does not alter selection.

## Exact `store.md` delta to apply after integration

1. In **Layout**, add `aelog/<versionstamp>/<operation>`,
   `aecursor/<source>/<generation>`, `aepending/<source>/<event>`, and
   `gchunks/<group>`. Add `mvariant/<group>/<marker>` and
   `vcer/<group>/<marker>/<writer>` and certificate-ID-keyed `xcertv/`, plus
   source-qualified `xcatalog/`, `xrcert/`, `xocert/`
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
   homing and the precise placement/revision conflicts that the current
   Workspaces and Groups models cannot merge. Explain why receipt-only marker
   variants refine one group and are selected deterministically. Link the new TLA target-home
   model and its mutation case once they pass.
