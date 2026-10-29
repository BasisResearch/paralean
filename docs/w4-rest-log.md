# W4-rest: store GC, dynamic shards and replay horizons

Branch `w4-rest`, a fresh clone of `origin/main` `91784ba` (2026-10-28), rebased
on 2026-10-29 onto `origin/main` `d009100`, which adds atomic multi-group
publication (T12/T13, [atomic-pub-log.md](atomic-pub-log.md)). It finishes the
three limits that [w4-log.md](w4-log.md) leaves open: physical P2/S3 object GC,
the fixed shard topology (with its per-shard 8 MiB cap as the reason to move
load), and indefinitely retained replay IDs.

## Isolation and resources

Only private instances are used: `PARALEAN_INSTANCE=w4r-a` (port base 32100),
`w4r-b` (32200) and `w4r-c` (32300) for the three implementation branches, and
`w4r-d` (32400) for the integrated runs, selected by `impl/p3/scripts/w4r-env.sh`,
which refuses any instance not named `w4r-*`. Their data lives under
`/data/home/kirancodes/paralean-p2/inst/w4r-*`. At start `/data` had 143 GB
free. Builds use at most six Cargo jobs; TLC uses one or two workers per run,
with at most a few heavy processes at a time. W2's strict verifier and limits
stay on every path: no change below relaxes a signature check, a request bound,
an admission cap or a size limit.

The work ran as five branches in sibling clones (`w4r-store-gc`, `w4r-shards`,
`w4r-replay`, `w4r-models-shard`, `w4r-models-gc`), merged into `w4-rest`. Once a
branch was merged and pushed, its clone, its instance data and the regenerable
Cargo build directories were deleted: `/data` reached 95% during the work (about
54 GB free), and the cleanup brought it back to about 190 GB.

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

### Atomic batches (T12/T13)

Main's atomic publication commits several members in one transaction. Each
member runs its unchanged T1 or T8 body (T9 or T10 on a receiver), so each member
writes its own `gcref` entries and refuses an object being collected. Any refused
member aborts the whole batch, so nothing of it is written. In addition, the
batch record `batch/<id>` is a referrer of every member's staged marker or
tombstone and of every published group. It is written in T12 and T13 and indexed
by backfill. Batch records are never removed, so no member of a retained batch
can be collected even without the members' own references. Before T12 the
member payloads are protected the way a single publication's are: by the J1
references of the member envelopes, which the controller binds to the signed
intent, and after J2 by the grace period. `publish_batch` uploads through the
GC-aware put. If T12 aborts with `Collected`, it revives the object and retries,
as the single writer does. The intent itself lives only in the record and the
envelopes, so it names no S3 object.

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

**Batches.** A `ValidateBatch` names several publication members. In a dynamic
topology it goes to the shard that owns every member's bucket:

- **Member buckets:** each member's recorded validation route, else its target
  names' bucket, else the batch's own bucket. The batch's bucket is its first
  publication member's, so target-free members share it, and one shard issues
  and fences every envelope (J1).
- **Refusals:** a batch whose members span shards is refused retryably
  (`batch spans controller shards`) before any J1, and so is one with a moving
  member bucket.
- **Drain:** an in-flight batch counts against every member bucket, as one
  validation does, until its dispatch ends, so an export of any of them waits.
  It runs outside the operation lock, as `Validate` does.

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

### Design 3 implementation (branch `w4r-replay`)

The code is `impl/p3/crates/control/src/replay.rs` plus small touch points in
`controller.rs`, `durable.rs` (the two replay-row key functions), `worker.rs` and
`main.rs`.

**Wire.** A request is its W4 object plus an optional `"generation"` field
(`ControlCall`, the same RPC service as `ControlRequest`). Absent means a legacy
client and generation 0; the RPC layer verifies the server's re-serialization, and a
legacy request re-serializes byte for byte (unit test). A generation-aware client
always sends the field; only it receives `Registered.replay_generation`, so a legacy
client's responses are unchanged. Refusals stay `Refused { reason }` (no new response
variant) and end with `(current replay generation N)`: `expired replay generation g`,
`replay generation g is ahead of this shard`, `replay generation required`. `Status`
reports the generation, its start tick, the horizon, the require flag and the
deleted-row and byte counters.

**Identity.** Request `(g, id)` with `g > 0` has the identity `"\u{1e}" g "/" id`,
which replaces the ID before routing, so the snapshot, the work and validation
routes, the group descriptor, J1-J3 and the assignment request all key on it.
Generation 0 is the ID itself and keeps every W4 key. An ID that already has this
form names its own generation (a worker passes back the work ID it was given; a
legacy client cannot alias a scoped identity), and a malformed one is refused. The
W2-44 length bound still applies to the client's ID before routing; an identity is
at most 22 bytes longer. Replay rows of `g > 0` are
`controller/shard/<n>/replay-rows/<g>/{work,poll}/<sha256(identity)>`.

**Gate.** It runs after routing (so the owning shard answers) and after the snapshot
load, before takeover bookkeeping and before any write, including the work-shard
reservation. Gated: `SubmitWork`, `PollRequest`, `Validate` and `AssignGroup` with a
client request ID. Not gated: `Finish`, `Cancel`, `Poll` without a token, and the
operations without client IDs. A `Validate` of a job that is `Running` on the same
worker passes whatever its generation, so active work of an old generation can still
be validated and finished. The shard's operation lock orders the gate, the dedupe
read and the save with the advance and the collector; a leader that lost its lease
cannot commit what it read.

**Advance.** The monitor, holding the operation lock, runs one transaction under the
lease and term: no record means generation 1 starting now; otherwise, once the clock
reaches `started_tick + H`, `G + 1` starts and `replay-refused/<G-1>` records the
tick at which `G - 1` stopped being accepted.

**Retirement.** One transaction per page reads the lease and term, the clock,
`replay-gen`, the refusal records and the range `replay-rows/[1, G-2]` (at most the
scan limit), clears the rows whose generation has been refused for at least the grace,
stops at the first generation still in its grace, and adds the rows and bytes to
`replay-stats`. A racing advance, takeover or row write conflicts with it.
Generation-0 rows lie outside the range. The current snapshot is never touched. Old
active work compacted after its generation retired writes a row in that generation's
range; a later pass clears it. Collection needs GC on and a horizon.

**Retained.** Routing records keyed by request ID (work-shard routes, group-request
descriptors, validation routes, the shard-local validation index), J1/J2/J3, the
recovery counters and P2's assignment-request keys are not retired. A route of a job
that is still active must survive its generation, because `Finish` and `Cancel` route
by it. Deleting routes safely would need a snapshot-membership check inside the
deleting transaction, and it would have to compose with design 2's bucket moves.
These records therefore still grow with the number of requests, at a few dozen bytes
each; the bound by `H` covers replay rows only.

**Flags and clients.** `controller --replay-horizon-ticks H [--replay-grace-ticks N]
[--require-replay-generation]`. The grace defaults to 8, and the require flag needs a
horizon. The worker keeps each endpoint's generation, learned from `Registered` and
from refusals. It sends poll tokens in that generation and retries once in a reported
one. Validations of a handed-out work ID go in that ID's own generation; other
validation IDs go in the newest generation the worker knows, retried in the one a
refusal reports. `submit`, `assign` and `assign-group` take `--generation G`. Without
it they probe with a generation no shard reaches (the owning shard refuses it before
writing and reports its own) and then resend. `cancel --generation G` names a scoped
request. `plr` (p3-remote) and P5's bridge still send legacy generation-0 requests,
so `--require-replay-generation` refuses their submissions. A pre-existing legacy ID
beginning with U+001E would now be parsed as scoped, or refused.

**Evidence.** `tests/w4r_replay.rs` has eight live tests and one ignored measurement.
`impl/p3/scripts/check-w4r-replay-mutations.sh` detects nine `mutate-replay-*` cases.
`results/w4r/replay.json` holds the measurement: eight phases of 64 cancelled requests
and 16 poll tokens, `H = 4`, grace 1. With a horizon the shard retains 160 replay rows
(about 35.8 KB) from the second phase on; without one it reaches 640 rows (133.6 KB),
growing linearly.

### Integration with dynamic shards (found while merging)

Per-shard generations are unsound once buckets move. Shard A could retire
generation g's rows while shard B still accepts g, and a move then takes the
request to B, where its row is gone, so it executes again. The models found the
same flaw independently (below). In a dynamic topology the implementation
therefore has one deployment-wide generation (`controller/replay-gen`). Only the
lowest active member advances it. Each shard records the tick at which it first
saw a generation refused, and its collector counts the grace from there. Scoped
replay rows are found across shards, as unscoped ones already were. Every
snapshot save re-reads the generation inside its own transaction and aborts if
the request's generation is no longer accepted: the gate's read and the
definite answer it guards must not straddle an advance. A `ValidateBatch` is
scoped like a `Validate`, and so are its members' request IDs, with the batch's
generation. A retry re-scoped to a new generation then issues fresh member
envelopes bound to its fresh intent, instead of colliding with the old ones.

## Verification plan

Models first: `StoreGc` (TLA+, with mutations, and Lean lemmas for the doom and
guard steps), `ShardHandover` (TLA+, with mutations), and `ReplayHorizon`
(TLA+, with mutations). The implementation flags stay off until the models and
tests pass.

## Design changes from the models

The `ShardHandover`, `ReplayHorizon` and `ReplayHorizonShards` models found four
flaws in the design text. The implementation handles each:

1. **J2 fence.** A receipt fenced on "owned and not moving" loses a drained
   validation's receipt. J2 needs only `shard = self`, which the implementation
   already used: receipts are allowed while the move is `Prepared`.
2. **Definite answers.** A definite answer must be fenced: a deposed leader's
   cached answer can contradict the new owner. The implementation re-routes
   under the operation lock and answers definitely only after a lease-fenced
   save; every other answer is retryable.
3. **Commit-time generation check.** The gate's read of `G` and the commit of
   the request it admits can straddle an advance and a retirement. Saves now
   re-check the generation in their transaction (`replay_check`).
4. **Generations across shards.** Per-shard generations are unsound under moves.
   The implementation uses one deployment-wide generation. The model's
   alternative is "every shard has refused g", with added shards starting at the
   maximum generation; `ReplayHorizonShards` checks that variant.

According to the models, five guards are redundant given the others:

- the save compare-and-swap;
- the J2 ownership check (a backstop for the drain);
- the T4 claim fence;
- import's state check;
- the replay grace, given the commit check.

They stay in the code as defence in depth. The mutation scripts still detect
each one in the implementation, where the other guards are weaker than in the
model.

## Implementation deviations from the design text

- **Store GC:**
  - Revival is a separate transaction (`gc_revive`). The referencing transaction
    refuses `Gone`, and revival clears it only if it still holds the same `Gone`
    the writer observed before its re-PUT.
  - A sweep moves `Gone` to `Sighted` only when a listing shows the object
    again, so it never skips the grace period.
  - The guard allows `Deleting → Deleting{nonce}` for a retried delete, and
    admits no query on a GC delete other than `x-id=DeleteObject`.
  - Protective `aepending` references never abort. They keep a doomed object's
    state, and the receiver refetches after `Gone`.
  - P5 bridge task blobs are referenced by their event rows.
- **Shards:**
  - Receipts are allowed while a move is `Prepared`.
  - Every request for a moving bucket is retryable.
  - Export and import are optimistic transactions.
  - Poll tokens of moved work leave as replay rows.
  - The validation index is keyed by bucket.
  - A move whose handoff would not fit one transaction is aborted.
- **Replay:** the generation is deployment-wide in dynamic mode (above).

## Evidence

(Filled in below as the final checks complete.)

## Not done

- **Collected metadata:**
  - `Gone` markers and `gc/retired/catalog/<c>` keys are kept forever. They are
    small, but they grow with the number of collected objects.
  - The delete pass scans all of `gcobj`.
  - An anti-entropy release reads its event's `gcaeref` index without a bound.
  - A writer waits for `Gone` (revival) for up to 30 s.
- **Controller routing records:** routing records keyed by request ID are not
  retired: work and validation routes, group descriptors and the validation
  index. Neither are J1–J3 or a removed shard's residual keys. Topology and
  move records are trusted as FDB contents and are unsigned, like every other
  controller key.
- **Replay generations for other clients:** `plr` (p3-remote) and the P5 bridge
  still send generation-0 requests, so `--require-replay-generation` refuses
  them. The worker and the `controller` CLI are generation-aware.
- **Batches:**
  - A batch on dynamic shards must have all its member buckets on one shard;
    one that spans shards is refused retryably, as a fixed topology refuses it.
    There is no cross-shard batch protocol.
  - The staged multi-transaction batch protocol (designed in atomic-pub-log.md)
    is still unimplemented, and the GC models cover only the single-transaction
    T12.
- **The `auth` test** in `w4r_shards.rs` needs `PARALEAN_BIN`.

## Proposed sentences

For docs/plan.md, "Deferred changes", replacing "Protocol-object GC, changing
membership, …":

> Protocol-object GC and changing controller membership are done for P2/S3
> payloads and controller shards: a transactional reverse-reference index with a
> logical-time grace and a guard-mediated delete (TLA `StoreGc`, Lean
> `Paralean.StoreGc`), and bucket handover fenced by shard epochs and leases (TLA
> `ShardHandover`). Shared-writer failover and Byzantine storage still change the
> protocol assumptions and require new models and proofs.

For README.md, replacing "Controllers support independent fixed shards, …
cannot delete P2 content ([w4-log](docs/w4-log.md))":

> Controllers support fixed or dynamic shard topologies, with online bucket
> moves and adding and removing shards, plus store-ordered leases and
> disabled-by-default history compaction and snapshot GC. Replay rows can be
> bounded by replay generations. Unreferenced P2/S3 payloads can be collected
> by an opt-in store GC, and only s3-guard's GC principal may delete them, and
> only keys the GC marked ([w4-log](docs/w4-log.md),
> [w4-rest-log](docs/w4-rest-log.md)).
