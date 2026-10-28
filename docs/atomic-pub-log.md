# Atomic multi-group publication

Branch `atomic-pub`, from `origin/main` at `91784ba`, started 2026-10-28.
W5's cross-workspace rename of already-published declarations was blocked because
publication is one group at a time (docs/w5-log.md, "Published-rename blocker"). This
work adds a publication that commits several groups and tombstones, by several
workspaces, all or nothing, and builds W5's published rename on it.

## Isolation

Store instances `ap-main` (six fdbservers, triple redundancy, netsplit; ports
33100–33150) and `ap-peer` (one fdbserver; 33200–33250), under
`/data/home/kirancodes/paralean-p2/inst/`. Source `.runs/ap/env-ap.sh` from a fresh
shell. It must set `PARALEAN_INSTANCE` before `env.sh` runs: `env.sh` keeps an
already-exported Garage socket. Two network tests failed only because that socket was
wrong, and passed once it was fixed. TLC, Veil and the P1 build were copied from the W2
clone at the same commit; nothing shared was rebuilt.

## Design

### The problem

A rename replaces published declarations across workspaces. Bob's `use` calls Alice's
`foo`. Renaming `foo` to `bar` publishes `bar`, deletes `foo`'s position and revises
`use` to call `bar`. If readers can see any proper subset of those three effects, they
see a broken state: `bar` without its callers, or `use'` before `bar`. So can
anti-entropy peers, recovery and working copies. The same holds for the target names
the groups declare. T1 publishes one group per transaction, and W5's rename probe
therefore refused published renames.

### Objects

- **Batch intent** (`v0/batch`, signed). `{request, members}`, where each member is
  `Publish {group, writer}` or `Tombstone {target, position, writer}`, in commit order.
  It is signed by the controller, or by a job-issuer key when no member binds a target
  name. These are the same signers that job envelopes allow. Group IDs do not depend on
  the batch, so the intent can name its members before their envelopes exist.
- **Batch binding.** `JobEnvelope` and `Tombstone` gain a trailing optional field
  `batch: intent ID`. An unbound object keeps its bytes and ID, so every existing
  envelope, receipt and tombstone is unchanged. T1, T8, T9 and T10 refuse a bound
  object. Only its own batch's T12 or T13 admits it. A coordinator that holds a
  member's receipt and certificate therefore cannot publish that member alone, and a
  half-applied rename cannot become visible by replay.
- **Batch record** `batch/<intent ID>`. It holds the signed intent and, per member, the
  marker or tombstone ID and that member writer's certificate ID. It is written only in
  the transaction that writes the members. Like every protocol key space, it only grows.
- **Member certificates.** Each member's publisher (or tombstone) certificate is signed by
  that member's own writer (`Writer::sign_batch_publication`, `sign_batch_tombstone`).
  The coordinator needs no member key.

### T12: one transaction

`Store::publish_batch` first writes every member's payloads (groups, chunks, capsules),
then their staged marker and tombstone copies, exactly as T1 and T8 do. It then runs
one FoundationDB transaction:

1. If `batch/<id>` is present with the same bytes, return without writing (idempotent as
   a whole). Different bytes are a conflict.
2. Check the intent: signed by the controller (or a job issuer for a target-free batch)
   through W2's strict verifier; members exactly the signed ones, in order; no subject
   twice; within the size budget.
3. Run each member's **unchanged** T1 or T8 body, in order, in this transaction:
   - the receipt for exactly that group and envelope;
   - the publisher certificate and active agent key;
   - revocation and cancellation;
   - dependency and parent-revision admission;
   - the target owner, epoch and head compare-and-swap for every target name;
   - the pinned statement;
   - W3's tombstone rules: published, certified target, same file, newer, author or
     controller grant, never a target name.

   FDB's read-your-writes makes each member see the members before it. A member may
   therefore depend on, revise, delete or re-head a name of an earlier member. A
   member's own idempotence shortcut is disabled, and its per-member anti-entropy event
   is suppressed.
4. Write the batch record and one `AeKind::Batch` event.

Any guard failure aborts the transaction, so nothing of the batch is written. A stale
owner on one member therefore rejects the whole batch. An unknown commit outcome is
resolved by re-running the body: it either finds the record or re-checks every guard
against current state.

The batch is a sequence of single publications taken at one commit version. That is
store.md's existing argument for multi-step transactions, and the Veil statement
below. W3's moves (T11) are not batch members. A rename is a publication plus a
deletion, and tombstoned positions remain valid anchors. Moves of positions a batch
published are ordinary later T11 transactions.

### Limits

T12 allows at most 128 members, 2 MiB of written metadata and 4096 payload object
references. These are checked before any write.

- **FDB's 10 MB per transaction.** Per member, T12 writes about 1–10 KB (marker,
  revisions, receipt, envelope twice, certificate, chunk index). Values over 64 KiB
  spill to S3 blobs as before. 2 MiB is a fifth of FDB's limit.
- **FDB's 5 s per transaction.** Each member body issues about 25 point reads, so 128
  members are about 3,200 sequential reads, well under the limit on a local cluster.
- **Anti-entropy.** A batch travels as one event. The receiver caps an event at 8 MiB
  of inline metadata and 8,192 parts, and 2 MiB and 4,096 objects fit both.

These bounds concern availability only. If a transaction exceeded FDB's limits, FDB
would abort it whole (`transaction_too_large` is not retryable; `transaction_too_old`
retries until `Unresolved`), and nothing would be written.

### Staged protocol for larger batches (designed and model-checked, not implemented)

A batch that cannot fit one transaction stages its members as rows that no reader
treats as published, in any number of transactions. A single intent transaction,
committed last, then makes them visible. Rules:

1. **Stage.** Write each member's rows under the batch, tagged with the intent ID.
   Staging checks only immutable facts: receipts, certificates, intent membership.
2. **Commit.** The intent transaction requires every member's row to be staged. It
   re-checks every non-monotone guard in that same transaction: target
   owner/epoch/head, revocation, cancellation, agent revocation, freshness, and the
   dependency and tombstone facts. It then sets the status to committed and advances
   the heads.
3. **Abort.** A pending batch whose coordinator gave up is aborted. Its rows never
   become visible, and its intent can never commit.
4. **Readers.** Every reader resolves a staged row through its intent record and
   ignores it unless the intent is committed. Multi-transaction readers also close
   their view under batches (as below).

`AtomicBatch.tla` with `Staged = TRUE` checks that no reader sees a partial batch and
that every single-publication invariant survives. Three mutations show that each rule
is needed:

- a reader that ignores the intent status;
- a commit before every row is staged;
- guards checked only at stage time.

The cost is that every reader of publication state must resolve intents. This work
implements the bounded single-transaction form. The staged form is the path to
lifting the bound.

### Readers that span transactions

- **Discovery and recovery.** `recovery::discover` scans `cert/` page by page, each page
  at its own read version, and scans `tcert/` afterwards. A batch committed during the
  scan can therefore appear partly: only members whose certificate keys follow the scan
  position, plus its tombstone from the later scan. Discovery now closes its view under
  batches. If any member of a batch is in the view, its record exists (same
  transaction, grow-only keys). Every member it names is then read by point reads,
  with the same certificate checks, and added. The live test commits a batch after the
  scan passed a member's key; without the closure that view is partial
  (`mutate-batch-scan-no-closure`).
- **Anti-entropy (T13).** T12 appends one `Batch` event and no per-member events. The
  event materializes as:
  - the record;
  - every member's marker, receipt, envelope, revisions, tombstone and its writer's
    certificate;
  - every payload reference.

  The receiver stages all parts (W2's caps apply unchanged) and checks every member as
  T9's or T10's caller does. A later member may depend on, revise or delete an earlier
  one. One T13 transaction then runs every member's T9 or T10 body in batch mode,
  writes the receiver's copy of the record and appends one relay event. If any member
  is deferred or rejected, the whole batch is deferred or rejected. T9 and T10 refuse a
  member offered alone. The in-process `antientropy::export` emits a batch as one
  `Item::Batch`.
- **Working copies.** `plr pull` writes a batch's member records and then the batch
  file. The Lean loader (`Known.load`) ignores a record bound to a batch whose batch
  file is absent.
- **Checkpoints (T5).** The checkpoint guard reads in one transaction, so it sees all of
  a batch or none. W3's currentness rule then rejects a checkpoint that mixes a batch
  with what it replaced.

### store.md delta

Proposed text for docs/store.md, "Transactions":

> | T12 | Publish batch `b` | `batch/<b>`; for each member in order, T1's reads (or T8's) | each member's T1 (or T8) writes, `batch/<b>`, one `Batch` event |
> | T13 | Receive batch `b` | `batch/<b>`; for each member in order, T9's reads (or T10's) | each member's T9 (or T10) writes, `batch/<b>`, one `Batch` event |
>
> T12 runs the T1 or T8 body of each member of a controller-signed batch intent, in
> order, in one transaction. Each body reads the writes of the members before it. Job
> envelopes and tombstones carry the intent ID. T1, T8, T9 and T10 refuse such a bound
> object; only its batch admits it. The whole batch is idempotent through `batch/<b>`.
> A batch is bounded (128 members, 2 MiB of metadata) so that it fits one transaction
> and one anti-entropy event.

Under "Atomic transactions as step sequences": T12 is the concatenation of its members'
hardened steps. Nobody observes the intermediate states (Veil `AtomicBatch`).

Under "Physical scan and enumeration": a paginated scan is closed under batches. If a
batch member is in the scan, its record exists, and every member is added by point
reads. Without the closure, a scan over a batch committed mid-scan can return part of
it, which falsifies all-or-nothing visibility (TLA `batch_scan_no_closure`).

The full proposed paragraphs are applied to docs/store.md in this branch.

## Model

`verification/tla/AtomicBatch.tla`. Workspaces a and b, target name x, and one batch:

- `g1`: bar, a proof of x;
- `t0`: deleting foo's position;
- `u1`: use', which revises use and depends on `g1` and on `g2`, a group outside the batch.

A competing single proof `h1`, reassignment of x, an untrusted coordinator (forged
certificates, crashes, lost commit replies), a one-pass paginated scan, an anti-entropy
peer with staged parts, a working-copy cache and checkpoint commits interleave freely.
Guards are named operators. Violation tags are computed from the raw state at each
commit.

| Configuration | Readers | Distinct states | Result |
|---|---|---:|---|
| `AtomicBatch` (T12) | scan, checkpoints | 4,427,772 | pass |
| `AtomicBatchAE` (T12) | anti-entropy peer, working copy | 9,810,976 | pass |
| `AtomicBatchStaged` (staged) | scan | 66,752,232 | pass |

Invariants:

- **Single-publication safety:** `ReceiptSafety`, `CertSafety`, `NoStalePublication`,
  `TargetChain`, `DepsClosed`, `TombstoneSafety`, `BatchBound`, `PublishOnce`,
  `HeadIsLatest`.
- **No partial batch:** `NoPartialStore`, `NoPartialScan`, `NoPartialPeer`,
  `NoPartialCache`, `CheckpointNoStraddle`.
- **Unknown outcomes:** `OutcomeTruthful`.

Negative cases (in `check-tla-negative.sh`):

| Guard | Case | Required failure |
|---|---|---|
| Receipt for exactly that group | `batch_no_receipt` | `ReceiptSafety` |
| Member's own writer's certificate | `batch_no_cert` | `CertSafety` |
| Target owner | `batch_no_owner` | `NoStalePublication` |
| Target epoch | `batch_no_epoch` | `NoStalePublication` |
| Head compare-and-swap | `batch_no_head_cas` | `TargetChain` |
| Dependencies published or earlier in the batch | `batch_no_deps` | `DepsClosed` |
| W3 tombstone target | `batch_no_tombstone` | `TombstoneSafety` |
| Bound members refused by T1/T8 | `batch_member_alone` | `BatchBound` |
| All or nothing | `batch_partial_commit` | `NoPartialStore` |
| Scan closure | `batch_scan_no_closure` | `NoPartialScan` |
| Checkpoint currentness | `batch_checkpoint_stale` | `CheckpointNoStraddle` |
| Unknown outcome resolved by reading | `batch_unknown_as_failure` | `OutcomeTruthful` |
| T9/T10 refuse members alone | `batch_ae_per_member` | `NoPartialPeer` |
| T13 needs every part | `batch_ae_partial_parts` | `NoPartialPeer` |
| Working copy ignores unfiled members | `batch_cache_no_filter` | `NoPartialCache` |
| Batch file written last | `batch_cache_file_early` | `NoPartialCache` |
| Staged: readers resolve the intent | `batch_staged_ignores_intent` | `NoPartialStore` |
| Staged: intent needs every row | `batch_staged_incomplete` | `NoPartialStore` |
| Staged: commit re-checks guards | `batch_staged_no_recheck` | `TargetChain` |

Seven witnesses must be violated in the unmutated model, so the passes are not
vacuous:

- `batch_commit_work` and `batch_staged_work`: a batch commits;
- `batch_stale_rejected_work`: a stale member rejects a batch;
- `batch_scan_work`, `batch_checkpoint_work`, `batch_peer_work` and
  `batch_cache_work`: each reader sees the whole batch.

`verification/veil/Paralean/AtomicBatch.lean` (namespace `ParaleanAtomicBatch`)
models a batch as a nonempty run of hardened steps, observed as one step:

- **`breachable_iff`:** runs whose transactions are hardened steps or batch commits
  reach exactly the hardened reachable states. A batch refines a sequence of hardened
  steps, so `hardened_safe` and every other hardened theorem hold.
- **`batch_published_receipted` and `batch_no_target_collision`:** fixes 1 and 2
  restated for batch runs.
- **`commit_publishes_members`:** every group published by any member is published once
  the batch commits.
- **`stale_member_blocked`:** no member step publishes a target proof prepared under a
  stale epoch.

Readers that span transactions are outside the Lean model; the TLA model covers them.

## Implementation

(in progress; see the summary below)
