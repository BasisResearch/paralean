# Hardened: all hardened guards on one store (TLA+)

`Hardened.tla` puts the hardened guards that the separate models check one at a
time (`Receipts`, `Targets`, `Certificates`, `Fencing`) into one spec over one
shared store, so TLC explores their interactions. `scripts/check-tla-hardened.sh`
runs everything below. It is a finite-instance check, not a proof.

## What is modelled

One store: three replicas with majority write and read quorums (sets; every
write quorum meets every read quorum), plus a linearizable metadata store holding
the target record (owner, epoch, head) and the catalogue fence. Two workers.

1. **Receipts.** The validator signs receipts only for valid groups; receipts are
   store objects any worker can present. No worker evaluates validity. Staging
   (`PrepareProof`, `PrepareBad`) requires a receipt for exactly that group.
2. **Publish point (atomic, as `AtomicCert = TRUE` in `Targets`/`Certificates`).**
   A staged proof is published by one conditional write, conditional on the
   record's epoch matching the epoch stamped at prepare, that also writes the
   publisher's own certificates to the live replicas (the publisher logs the
   replies) and sets the recorded head. The marker acknowledgement by a live
   write quorum is a precondition (always obtainable here, see below). The
   preparer reads a local copy of (owner, epoch, head) that may lag the store
   arbitrarily; prepare checks the copy names it owner, revises the copy's head,
   and that it has no other pending proof. A refused publish drops the proof and
   the copy. A successful publish tells the writer the value it wrote.
   Reassignment bumps the epoch without the old owner's cooperation; the old owner
   keeps running as a zombie on its stale copy.
3. **Publication certificates.** Other workers write their own certificates only
   once they know the group published, to every live replica, with their reply
   log. Discovery reads
   certificates of a fully live read quorum. Checkpoint commit needs the
   committer's own reply quorum and the proof to be its unique known head.
4. **Catalogue (aligned with `Fencing`).** One record per token rank,
   `<<rank, snapshot>>`, naming a parent fixed at its first put: a lower-rank
   record the writer acknowledged itself or reads as ready, or none if it reads no
   ready record. First write per replica, conditional on fence = the writer's
   current token. Repair by the writer
   from a named live source replica, unconditional. The writer's ack is its own
   reply log covering a write quorum. The commit certificate is written to a live
   write quorum after that ack, conditional on the fence, and only once the parent
   is committed (`ParentsCommittedOK`, reading its certificates). Certificate repair
   (any process, unconditional) copies an existing commit certificate from a live
   replica. The snapshot's object certificate (manifest and
   payload) is written, unfenced, at checkpoint commit. Fence rotation issues the
   next rank to a worker other than the current holder, so a writer can re-acquire.
   Recovery readiness `Ready(Q, c)`: for c and every ancestor, bytes on some
   replica of the fully live read quorum Q, and commit and object certificates
   each held by every member of some fully live write quorum (as `Fencing`).
5. **Completion.** A worker completes the single task on its own record for the
   exact snapshot it committed, once its commit-certificate replies cover a write
   quorum.

Failures: one permanent replica loss (bytes and certificates on it are gone; a
read quorum survives), and one index erasure (every worker loses pending work,
known groups, checkpoint id and record copy; tokens and reply logs survive).

Observability: guards read only the acting worker's local state, receipts it
presents, the item a conditional write is conditional on (evaluated by the store),
the record when it reads it, or live replicas. Ghost variables (`writtenAt`,
`certFence`, `lateAck`, `byzRejected`) are read only by invariants and witnesses.

## Instance

`Hardened.cfg`: replicas `{r1, r2, r3}`, workers `w1`, `w2`, target proofs `p1`,
`p2` (valid), invalid group `x`; `w1` initially owns the target and holds fence
rank 1; `MaxEpoch = 1` (one handover), `MaxFence = 2` (one rotation). Replica
symmetry. `HardenedReacquire.cfg`: same with `MaxEpoch = 0`, `MaxFence = 3`
(rotation away and re-acquisition). No `CONSTRAINT` in either.

| Run | Distinct states | Depth | Time |
|---|---:|---:|---:|
| `Hardened.cfg` | 3,104,542 | 35 | 12 to 19 min |
| `HardenedReacquire.cfg` | 280,614 | 30 | 75 s |

Witness and mutation runs stop at their first counterexample after at most a few
thousand distinct states. The three redundancy probes explore their whole
(mutated) state space: 3.77M, 3.10M and 7.63M distinct states. Times are wall
clock with 4 TLC workers on a shared 10-core laptop under heavy load from
another session (load average 40 to 140); the main run is above the 15-minute
target under that load.

## Invariants (all hold in both instances)

- Receipts: `StagedValid`, `StagedReceipted`, `PublishedValid`, `PublishedReceipted`.
- Targets: `TargetChain` (published proofs form a chain), `HeadUnique` (each worker
  sees at most one head), `RecordTopsChain` (the recorded head is published and
  revises every other published proof), across the handover.
- Certificates: `CertSound` (certificates only for published groups),
  `ReceivedPublished`, `PublishedDiscoverable` (every published group, in
  particular the recorded head a new owner must revise, is found by every fully
  live certificate scan), `CheckpointDiscoverable` (each checkpoint's proof is
  published and discoverable).
- Catalogue: `StaleNeverStored`, `CertFenced`, and for every record ready on any
  fully live read quorum: `ReadyCommitFenced` (commit certificate written while
  its token was the fence; not a record acknowledged after rotation),
  `ReadyFirstWriteFenced` (bytes first written while its token was the fence),
  `ReadySnapshotSound` (its proof is published, found by every fully live
  certificate scan, and is the current recorded head or revised by it).
- Completion: `CompletedRecoverable`: the completed record's proof is published
  and discoverable, and for the record and each ancestor: its commit certificate
  was written under the fence and survives on a live replica (so certificate
  repair can restore a full live quorum of it), its object certificate is durable,
  and every fully live read quorum finds its bytes. Nothing in it reads an index,
  so it holds after any erasure. It does not say the record is `Ready` at every
  moment: right after a loss of a commit-certificate holder it is not, until
  repair (`NeverCompletedUnreadyAfterLoss` is violated); `NeverRecoveredAfterLossAndErasure`
  shows it ready again.
- `FailureEnvelope`, `TypeOK`.

What holds about the head, precisely: a ready or completed record's proof is on
the target chain at all times (current head or revised by it). It need not be the
recorded head when the record is committed or later: a worker commits from its
own knowledge, which can lag, and a later owner can supersede the proof
(`NeverCompletedSuperseded` is violated).

## Coverage witnesses (each must be violated)

Witnesses run `HardenedMC.tla`, which only adds the state constraint `NoFailures`
(no loss, no erasure) for pruning; a violation under a constraint is still a
behaviour of `Spec`. Some also shrink `MaxEpoch`/`MaxFence`.

| Witness | Settings | Trace found |
|---|---|---|
| `NeverCompletedAfterHandover` | `NoFailures` | `w1` publishes `p1` at epoch 0 (with its certificates); handover to `w2`; `w2` scans `p1`, publishes `p2` revising it, catalogues under its own rank and completes |
| `NeverRecoveredAfterLossAndErasure` | `MaxEpoch=0, MaxFence=1` | completion, replica loss, erasure of every index, certificate rescan of the proof; the record is ready on a live quorum |
| `NeverCompletedUnreadyAfterLoss` | `MaxEpoch=0, MaxFence=1` | after completion a commit-certificate holder is lost, so the record is not ready on the surviving quorum until certificate repair |
| `NeverStalePrepareRefused` (action property) | `NoFailures`, no symmetry | a proof prepared at epoch 0 is refused at publish after the handover |
| `NeverStaleCatalogueWriter` | `MaxEpoch=0`, `NoFailures` | rank-1 record put on one replica, rotation, repair completes the writer's ack after rotation |
| `NeverByzantineAttempt` | `ByzProbe=TRUE` | a staging write of `x` without a receipt is refused, and a receipted proof is published |
| `NeverReacquiredCompleted` | `MaxEpoch=0, MaxFence=3`, `NoFailures` | `w1` re-acquires the fence (rank 3) after `w2` held rank 2 and completes on its rank-3 record |
| `NeverCompletedSuperseded` | `MaxFence=1`, `NoFailures` | after completion on `p1`, `p2` revising it becomes the recorded head |

`ByzProbe` enables `RefuseBad`, a step that changes only a ghost; it is off in the
positive runs, where it would only double the state count.

## Mutations (each must produce the named violation)

Each removes one guard by an edit of `Hardened.tla` (exact single-site match)
and runs the full `Hardened.cfg` instance (or `HardenedReacquire.cfg`, where
noted) with only the named invariant.

| Guard removed | Mutation | Required violation |
|---|---|---|
| Staging needs a receipt | `m_no_receipt` | `StagedValid` |
| Prepare needs the copy to name the preparer owner (also lifts the read restriction below) | `m_no_owner_check` | `TargetChain` |
| Publish conditional on the epoch | `m_no_epoch_condition` | `TargetChain` |
| Publish sets the recorded head | `m_no_head_update` | `TargetChain` |
| Prepare revises the record's head, not a scan's | `m_head_from_scan` | `TargetChain` |
| The writer keeps the value it wrote as its copy | `m_no_learn_own_write` | `TargetChain` |
| The publish write carries the publisher's certificates (atomic point) | `m_publish_without_certs` | `PublishedDiscoverable` |
| Other workers' certificates only after they know the group published | `m_cert_before_publish` | `CertSound` |
| First write fenced | `m_unfenced_put` | `StaleNeverStored` |
| Repair copies from a live source | `m_repair_without_source` | `StaleNeverStored` |
| Commit certificate after the writer's ack | `m_commit_cert_before_ack` | `CompletedRecoverable` |
| Commit certificate fenced | `m_unfenced_commit_cert` | `ReadyCommitFenced` |
| Commit certificate only once the parent is committed (run on `HardenedReacquire.cfg`) | `m_parent_uncommitted` | `CompletedRecoverable` |
| Certificate repair copies an existing certificate from a live replica | `m_cert_repair_without_source` | `CertFenced` |
| Adoption on certificates, not a byte quorum | `m_adopt_on_bytes` | `ReadyCommitFenced` |
| Completion needs a committed catalogue record | `m_complete_uncommitted` | `CompletedRecoverable` |

`m_no_learn_own_write` shows that an epoch-only publish condition with a lagging
copy relies on the writer updating its copy from its own successful publish:
otherwise the owner can prepare a second proof against the head it read before its
own publish, in the same epoch. A compare-and-swap on the head would also close it.

## Redundant guards in this model

Run as probes (the mutated model must report no error for the listed invariants):

- `r_unfenced_put_adoption`: without the first-write fence, every adoption and
  completion invariant (`ReadyCommitFenced`, `ReadySnapshotSound`,
  `CompletedRecoverable`, plus target and certificate invariants) still holds. The
  first-write fence only protects `StaleNeverStored`/`ReadyFirstWriteFenced`; the
  fenced commit certificate alone keeps stale records out of recovery.
- `r_commit_without_own_quorum`: with atomic publication the publisher's
  certificates reach every live replica in the publish write, so every published
  group is already found by every fully live scan (`PublishedDiscoverable`), and
  dropping the committer's own-reply-quorum check breaks none of
  `PublishedDiscoverable`, `CheckpointDiscoverable`, `ReadySnapshotSound`,
  `CompletedRecoverable`. The check matters in `Certificates` with
  `AtomicCert = FALSE` and with partial certificate writes, neither of which is
  in this model.
- Mutating the checkpoint commit's own-reply-quorum check is therefore a probe,
  not a mutation.
- `r_ready_without_object_certs`: the object-certificate conjunct of `Ready` never
  decides readiness here, because object certificates are written to every live
  replica at checkpoint commit, before a record for that snapshot can be put.
  This is an artefact of the modelled ordering and certificate granularity, not
  evidence that object certificates are unnecessary.

## Restrictions and what is not modelled

Scheduling restrictions (fewer behaviours, documented in the spec):

- Proof ids are taken in a canonical order (`Fresh`); ids are interchangeable.
- A worker keeps a copy of the target record only when it names the reader owner
  (`ReadUseful`); with the owner check in place such a copy enables nothing else.
- A worker does discovery, certificate writes and checkpoint commits only while
  its copy names it owner (`Active`); a stale copy keeps a zombie active.
- Reassignment and fence rotation go to a worker other than the current one.
- One catalogue record per token rank; parents are named at first put but a
  writer cannot write a second record under the same rank.
- Commit-certificate repair runs only after a replica loss.
- At most one replica loss (the failure envelope for 3 replicas) and one index
  erasure, which hits every worker at once.

Not modelled:

- Marker bytes; the marker acknowledgement is a precondition of publish, always
  satisfiable since a live write quorum always exists here.
- Partial publication and object certificate writes and rewrites: each goes to
  every live replica in one step, once per writer and object. A commit
  certificate goes to one chosen live write quorum in one step and is then
  repaired replica by replica (repair only after a replica loss, a scheduling
  restriction). Partial publication certificate quorums are covered by
  `Certificates`. Repair of publication or object certificates is not modelled.
- Separate manifest and payload certificates and their byte acknowledgements (one
  object certificate per snapshot, written with its bytes).
- Causal reconstruction and selection among several ready records (`Fencing` has
  it); readiness is checked for every fully live read quorum instead of recorded.
- Snapshots with more than one group, dependencies, more than one target name,
  more than two proofs, a third worker, owner re-grant to the same worker.
- Lost replies, the publish write's failure modes other than the epoch check,
  Byzantine storage, signature checks (receipts, tokens) beyond set membership.
- Liveness. The stranded publication of the non-atomic design is shown here only
  as a safety violation (`m_publish_without_certs` breaks `PublishedDiscoverable`);
  progress properties are in the per-component liveness configurations.

## Run

`bash scripts/check-tla-hardened.sh` runs 29 cases (2 positive, 8 witnesses, 16
mutations, 3 probes), writes `.runs/tla/hardened/MANIFEST` and appends the
provenance block of `scripts/tla-common.sh` to each log. The last full run took
41 minutes wall clock at 4 workers under the load described above.
