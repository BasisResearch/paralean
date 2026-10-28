# W4-rest: store GC, dynamic shards and replay horizons

Branch `w4-rest`, a fresh clone of `origin/main` `91784ba` (2026-10-28). It
finishes the three limits that [w4-log.md](w4-log.md) leaves open: physical
P2/S3 object GC, the fixed shard topology (with its per-shard 8 MiB cap as the
reason to move load), and indefinitely retained replay IDs.

## Isolation and resources

Only private instances are used: `PARALEAN_INSTANCE=w4r-a` (port base 32100),
`w4r-b` (32200) and `w4r-c` (32300), selected by `impl/p3/scripts/w4r-env.sh`,
which refuses any instance not named `w4r-*`. Their data lives under
`/data/home/kirancodes/paralean-p2/inst/w4r-*`. At start `/data` had 143 GB
free. Builds use at most six Cargo jobs; TLC uses one or two workers per run,
with at most a few heavy processes at a time. W2's strict verifier and limits
stay on every path: no change below relaxes a signature check, a request bound,
an admission cap or a size limit.

## Design 1: physical store GC

### What is reachable

Roots are: every published marker (its group, chunks, capsule, the staged marker
copy and any blob its envelopes spill to) and every marker variant; revisions;
tombstones and their staged copies (tombstone lineage); committed catalogue
records with their snapshots and manifests, and every record that a committed
record's predecessor chain names; foreign catalogue copies (`xcatalog`); pending
validation jobs (J1 without J2 or J3); objects named by pending anti-entropy
events (`aepending`/`aepart` object references, the receiver's cursor state);
and certificates (`cert`, `tcert`, `rcert`, `ocert`) of any of these.

With these roots every published group is reachable forever: a group is a live
head, an ancestor of one through its revision parents, or tombstone lineage. A
W3 move adds a marker variant of the same group and keeps the old position as a
tombstone, so a move or a revision can never refer to a collected ancestor.
Published protocol content is therefore never collected. What the collector
reclaims is what no committed metadata names:

1. **Staging garbage**: S3 objects whose referencing transaction never
   committed (an aborted or abandoned T1, T5, T8 or anti-entropy import; payloads
   uploaded for validation and never published).
2. **Dead catalogue records**: a staged `catalog/<c>` with no `rcert/<c>` whose
   token rank is below the current fence. T5 requires `token.rank = fence` and
   the fence only grows, so `c` can never commit; recovery never adopts a record
   without a commit certificate. Its snapshot and manifests become staging
   garbage unless another record names them.
3. **Controller metadata** (W4 already collects retired snapshots): replay rows
   of retired request generations (design 3) and the residual keys of removed
   shards (design 2).

### Reference index

Scanning every key space inside one deletion transaction is impossible, so the
collector relies on a transactional reverse index. Every transaction that makes
committed metadata name an S3 object `o` also writes
`gcref/<kind>/<o>/<referrer>` (the referrer is a hash of the naming key, with the
key as the value) and reads `gcobj/<kind>/<o>`:

- if `gcobj` is `Doomed` or `Deleting`, the transaction aborts with
  `Collected`; the writer waits for `Gone`, re-PUTs and retries;
- if `gcobj` is `Gone`, the writer must have re-PUT `o` after reading `Gone`
  (the revival path); the transaction then clears `gcobj`;
- if `gcobj` is `Sighted`, the transaction clears it (a new reference restarts
  the grace period).

The referencing transactions are T1 (group, chunks via the chunk index, capsule,
staged marker, blobs), T11 moves (staged marker), T8/T10 tombstones (staged
tombstone, blobs), T5s/T5 (snapshot, both manifests), J1 issue (group, capsule
and dependency payloads, referrer `job`), anti-entropy part persistence (object
references of a pending event, referrer `aepending`) and anti-entropy import
(the imported metadata). T6 (`ocert`) is not a reference, but it reads `gcobj`
and refuses a doomed, deleting or gone object, so a certificate never vouches
for an object about to disappear.

Releasing a reference clears its `gcref` key in the same transaction that
removes the reason: archiving or importing a pending anti-entropy event, a job
reaching J2 or J3 (the collector's job-release step reads both), and retiring a
dead catalogue record.

### Logical clock and grace

`gc/clock` is a store-ordered counter advanced by serializable increments, as
W4's shard clocks are; no wall clock is read. A sweep lists `obj/<kind>/` and,
for each object, runs one transaction that reads the `gcref` range for `o`
(limit one; FDB adds the whole range to the read-conflict set) and `gcobj/<o>`:

- a reference exists: clear any `Sighted` state; done;
- no reference and no state: write `Sighted{clock}`;
- no reference and `Sighted{t}` with `clock - t >= Grace`: write
  `Doomed{clock}`, clear `ocert/<kind>/<o>`, increment `gc/dooms`.

Because every new reference writes the `gcref` range or clears `Sighted`, a
doomed object had no reference for at least `Grace` ticks and has none at the
doom's commit version. A reference transaction racing the doom conflicts on
the `gcref` range or on `gcobj`, so exactly one of them commits first.

Multi-transaction monotone checks (T5's per-payload `ocert` reads in
`commit_checkpoint`, recovery's readiness reads) depend on `ocert` keys staying
put. Payload `ocert`s of published content are never cleared (those objects are
roots). The only `ocert`s the collector clears are of unreferenced objects, and
T5 re-reads `ocert/snapshot/<m>` inside its transaction, so a doomed snapshot
fails T5 rather than committing a record over a missing object.

### Deletion through s3-guard

The collector's S3 key is s3-guard's GC principal. With
`--gc-fdb-cluster FILE` and `--gc-deployment NAME[=S3PREFIX]` the guard admits a
GC-principal `DELETE` of a content key `<prefix>obj/<kind>/<hex>` only if, in an
FDB transaction, `gcobj/<kind>/<id>` is `Doomed`; it moves it to
`Deleting{nonce}`, forwards the request, and on Garage's success moves
`Deleting{nonce}` to `Gone{clock}`. Every other principal, an unmarked key, a
key in any other state, a bucket or configuration delete, a bulk delete and a
virtual-hosted request stay refused. A content PUT whose key is `Doomed` or
`Deleting` is refused, so a revival cannot land under an in-flight delete. The
former prefix allowlist for non-content keys is unchanged. Garage still verifies
the SigV4 signature; the guard's access-key match is an identity selector, as in
W4.

### Anti-entropy and recovery

A source never advertises or serves a doomed, deleting or gone object: event
materialization drops such a part, and the object endpoint answers `Retired`
rather than `Missing`, so a receiver archives the event instead of retrying.
`gc/retired/catalog/<c>` records each retired dead record, and catalogue export
and import refuse retired IDs, so a peer cannot hand a retired record back.
Receivers protect objects of pending events through the `aepending` referrer.
A receiver that collected a digest as its own garbage may import it again for a
newly published remote group: that is a new committed reference created through
the revival path, not resurrection of the collected incarnation.

Desktop-loss recovery reads `cert/`, `catalog/`, `rcert/` and `ocert/`. None of
the keys it adopts can be cleared: certified markers and committed records are
roots, and the dead records the collector removes were never adoptable. Paginated
scans stay sound: a scan may return a dead record that is cleared afterwards;
it was not adoptable when returned.

### Enabling

Collection is off unless `gc enable` has run. Enabling requires every writer to
be GC-aware (the operator's obligation; legacy binaries do not write `gcref`),
then a backfill pass that walks every referencing key space and writes the
missing `gcref` entries (each write re-reads its referrer key, so a concurrently
retired referrer is not re-added), and finally sets `gc/indexed`. Sweeps refuse
to run without `gc/indexed`.

## Design 2: dynamic shard topology

Legacy fixed deployments keep their 4-byte topology value and behaviour. A
dynamic deployment stores `controller/topology` as a versioned record with a
topology epoch, the member shards (each `Active` or `Retired`) and a fixed bucket
count `NB` (256). A target's bucket is `sha256(name) mod NB`. Bucket records
`controller/bucket/<b>` hold `{shard, epoch, moving}`.

Routing goes through buckets. In dynamic mode a target claim stores a bucket,
not a shard (`0xB0 ‖ u16`); a multi-name group claims the bucket of its first
sorted name, which preserves colocation. Work routes store the bucket and target
hash, validation routes the bucket. The owning shard is the bucket's record. A
move therefore never rewrites claims or routes; only bucket records and the
moved shard-local state change.

Every shard-local durable write keyed by a bucket (work-route reservation, T4
claim, J1 issue with its shard-local index entry, J2 receipt) reads the bucket
record in its transaction and requires `shard = self` and no move in progress.
This is the shard-epoch fence, alongside W4's per-shard lease and term fence.
Snapshot saves additionally compare-and-swap the head generation they loaded.

### Move protocol

`move <id> buckets S from A to B` runs in three fenced steps. Each is one FDB
transaction and is idempotent by the move record's state.

1. **Begin** (authority): requires every bucket in `S` owned by `A` with no move
   in progress; writes the move record `Prepared` and `moving = id` on each
   bucket, and bumps the topology epoch.
2. **Export** (A's leader, under its lease and term, holding the operation lock):
   while `Prepared`, A refuses new submissions and validations for `S` with a
   retryable `moving` answer and waits for its in-flight validations in `S` to
   finish. Then one transaction removes every `S` entry from A's snapshot (work
   in any state, its order, groups), writes them to the move's handoff record,
   moves A's shard-local validation-index entries for `S` to B's index, sets each
   bucket to `{shard = B, epoch + 1, moving = id}`, and marks the move
   `Exported`.
3. **Import** (B's leader, under its lease and term): one transaction merges the
   handoff into B's snapshot (adding unknown workers with a fresh lease in B's
   clock), deletes the handoff, clears `moving` on each bucket and marks the move
   `Done`.

Between export and import B owns the buckets but refuses their requests until it
imports, because `moving` is still set. A job is in exactly one of A's snapshot,
the handoff record or B's snapshot at every commit version. Killing A's leader
before export leaves `Prepared` for A's next leader; killing it after export
leaves `Exported`; killing B's leader before import leaves `Exported` for B's
next leader. The handoff must fit one FDB transaction with A's new snapshot (at
most 9 MiB together); a larger move is refused and must be split.

In-flight work keeps its worker and assignment epoch across a move: a
`Running` job's finish routes to B through its unchanged work route. Replay rows
are read across every shard ever in the topology, so a duplicate submission of
work compacted at A is still recognised at B.

**Add** a shard: add it `Active` to the topology; it owns nothing until a move
gives it buckets. **Remove** a shard: it must own no bucket and have no move in
flight; it becomes `Retired`, its lease key is set to a sentinel that fails every
fenced write, and its remaining keys become collectable controller metadata.
Workers learn endpoints from configuration; a retired shard refuses with a
retryable answer.

Cross-shard dependencies are unaffected: they rely on P2's global T1
certificate and publication checks, not on shard placement.

## Design 3: replay horizons

W4 keeps every replay row forever because a delayed retry of a forgotten request
ID would execute again. Bounding them needs a horizon that a request cannot
outlive. The design scopes client-chosen IDs (work requests, group requests,
validation requests and poll tokens) by a per-shard replay generation `G`.
`controller/shard/<n>/replay-gen` holds `{generation, started_tick}`. A
submission names its generation; generation 0 means legacy and is never retired.

- The shard accepts submissions only in generations `G` and `G - 1`; anything
  older is refused with a definite `Expired`, never executed.
- The leader advances `G` when the shard clock passes `started_tick + H`, under
  its lease and term.
- Replay rows of generations at most `G - 2` are deleted by the controller
  collector, fenced like snapshot GC, after the shard has refused that
  generation for at least `Grace` ticks.

A request `(g, id)` therefore executes at most once: while `g` is accepted its
row deduplicates it, and once `g` is retired every message naming it is refused.
Replay protection stays: a captured or delayed request of a retired generation
is refused, and W2's nonce-bound RPC authentication is unchanged. Retirement only
touches terminal replay rows; active work stays in the snapshot regardless of
its generation, and finishes and cancellations refer to existing jobs by ID.
`--require-replay-generation` makes generation-0 submissions refused, so that a
deployment's replay state is bounded by `H`.

## Verification plan

Models first: `StoreGc` (TLA+, with mutations, and Lean lemmas for the doom and
guard steps), `ShardHandover` (TLA+, with mutations), and `ReplayHorizon`
(TLA+, with mutations). The implementation flags stay off until the models and
tests pass.

## Evidence

(Filled in as checks complete.)
