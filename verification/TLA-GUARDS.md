# Admission and freshness guard coverage

## Editor/controller boundary (W5)

`EditorWiring` has separate publication, rename and capsule-replay scenarios.
It abstracts receipt verification, dependency discovery and Lean source replay
as verdicts supplied by those subsystems. The model checks that the boundary
requires these verdicts; it does not prove their implementations or arbitrary
editor-client behavior. Rename's atomic state is the controller's buffer map.
The authorization verdict includes the frozen target, owning workspace and
current dispatch epoch; an explicit request by a different registered workspace
does not satisfy it. Runtime source mutations test these concrete checks.

| Check | Mutation | Required invariant failure |
|---|---|---|
| Receipt before publishing | `editor_no_receipt` | `PublicationSafe` |
| Explicit user/agent action or policy | `editor_no_action` | `PublicationSafe` |
| Exact document, environment and generation stamp | `editor_stale_publish` | `PublicationSafe` |
| Policy advancement fences old sessions | `editor_no_policy_fence` | `SessionFenced` |
| Every rename participant prepared | `rename_missing_participant` | `RenameSafe` |
| Complete dependency inventory | `rename_incomplete_inventory` | `RenameSafe` |
| Valid semantic edit plans | `rename_invalid_plan` | `RenameSafe` |
| Rename plan stamps still current | `rename_stale_plan` | `RenameSafe` |
| All affected buffers change together | `rename_partial_commit` | `RenameAtomic` |
| Legacy metadata replay verified | `recapture_unverified` | `OverlaySafe` |
| Exact original capsule identity | `recapture_wrong_identity` | `OverlaySafe` |

`editor_publish_work`, `editor_rename_work`, and `editor_recapture_work` require
counterexamples to their `Never*` invariants in the unmutated model. Thus the
positive checks cannot pass solely by disabling publication, rename or replay.

## Atomic multi-group publication

`AtomicBatch` checks one batch that renames published declarations across two
workspaces:
- publish bar (`g1`, a proof of target name x);
- delete foo's position (`t0`);
- publish use' (`u1`), which revises use and depends on `g1` and on `g2` outside the batch.

A competing proof, reassignment, an untrusted coordinator, crashes and lost commit
replies interleave with four readers: a paginated scan, an anti-entropy peer, a
working-copy cache and checkpoint commits. `Staged = TRUE` replaces the
single transaction (T12) by staged rows and an intent committed last. Guard removals:

| Check | Mutation | Required failure |
|---|---|---|
| Receipt for exactly that group and envelope | `batch_no_receipt` | `ReceiptSafety` |
| Member writer's own certificate | `batch_no_cert` | `CertSafety` |
| Target owner | `batch_no_owner` | `NoStalePublication` |
| Target epoch | `batch_no_epoch` | `NoStalePublication` |
| Head compare-and-swap | `batch_no_head_cas` | `TargetChain` |
| Dependencies published or earlier in the batch | `batch_no_deps` | `DepsClosed` |
| W3 tombstone target | `batch_no_tombstone` | `TombstoneSafety` |
| T1/T8 refuse batch-bound members | `batch_member_alone` | `BatchBound` |
| All or nothing | `batch_partial_commit` | `NoPartialStore` |
| Scan closed under batches | `batch_scan_no_closure` | `NoPartialScan` |
| Checkpoint currentness | `batch_checkpoint_stale` | `CheckpointNoStraddle` |
| Unknown outcome resolved by reading | `batch_unknown_as_failure` | `OutcomeTruthful` |
| T9/T10 refuse members alone | `batch_ae_per_member` | `NoPartialPeer` |
| T13 needs every part | `batch_ae_partial_parts` | `NoPartialPeer` |
| Working copy ignores unfiled members | `batch_cache_no_filter` | `NoPartialCache` |
| Batch file written last | `batch_cache_file_early` | `NoPartialCache` |
| Staged: readers resolve the intent | `batch_staged_ignores_intent` | `NoPartialStore` |
| Staged: intent needs every row | `batch_staged_incomplete` | `NoPartialStore` (only invariant; `HeadIsLatest` also fails) |
| Staged: commit re-checks guards | `batch_staged_no_recheck` | `TargetChain` (only invariant) |

`batch_commit_work`, `batch_stale_rejected_work`, `batch_scan_work`,
`batch_checkpoint_work`, `batch_peer_work`, `batch_cache_work` and `batch_staged_work`
require counterexamples to their `Never*` invariants in the unmutated model.

## Store protocol guards

`scripts/check-tla-negative.sh` removes each effective admission or freshness
check below. It requires the named invariant or temporal error. A parser failure,
unrelated error, or arbitrary nonzero exit does not satisfy a check. Every
temporal mutation runs with exactly one `PROPERTY` in its configuration, so
TLC's generic "Temporal properties were violated" names that property.

| Check | Mutation | Required failure |
|---|---|---|
| Prepare requires `Valid` | `unchecked` | `AdmissionSafety` |
| Prepare requires known dependencies | `unknown_dependency` | `AdmissionSafety` |
| Prepare requires known ancestors | `unknown_ancestor`, `unclosed_ancestors` | `CausalAdmissionSafety`, `PublishedAncestorSafety` |
| Publish requires a prepared candidate | `unprepared_publication` | `AdmissionSafety` |
| Receive requires prior publication | `unpublished_receive` | `AdmissionSafety` |
| Commit requires `Buildable` | `unbuildable_commit` | `SnapshotSafety` |
| `Buildable` requires dependency closure | `unclosed_snapshot` | `NoRetargeting` |
| `Buildable` requires exporter acceptance | `unexportable_snapshot` | `NoUnexportableCheckpoint` |
| Commit requires current members | `stale_commit`, `stale_recommit` | `CommitFreshness` |
| Names retain every incomparable head | `silent_winner` | `EventualCollision` (only property) |
| Acknowledgement requires quorum persistence | `premature_ack` | `WitnessSurvives` |
| Publication requires acknowledgement | `unbacked_publication`, `staged_publication` | `PublicationGuard` |
| Checkpoint commit requires acknowledgement | `unbacked_checkpoint` | `CheckpointGuard` |
| Eventual recovery is required for progress | `no_fair_recovery` | `Convergence` (only property) |
| Fair receive service is required for progress | `no_fair_receive` | `EventualDelivery` (only property) |

The closure and exporter mutations change `Buildable` itself. Their failure
oracles therefore inspect pinned dependencies and exporter acceptance directly;
they do not reuse the weakened definition. `ExportRejected` admits a valid
declaration but rejects its nonempty export. Its publication witness prevents
the scenario from passing by rejecting all work.

`staged_publication` replaces acknowledgement with existence of one stored copy.
It admits a package before any write-quorum acknowledgement. This tests the
modeled distinction between staged persistence and durable admission. `Put`
already denotes validated bytes; corruption and validator errors are outside
this model. No concrete byte-corruption test is claimed.

## Redundant checks

Some individual guard deletions cannot violate the stated safety properties.
Requiring a counterexample for those deletions would demand a false result.

- **Self-dependencies and self-ancestors in Prepare.** Containment would require
  the candidate itself to be known. Known records are published. Strict admission
  rank decrease already rules out either self-edge on a published record.
  Thus the other guards reject the candidate before the explicit self-edge check.
- **Known snapshot contents in Commit.** For an included `d`, instantiate
  `Current` with `e = d`. It yields `isHead(d)`, which includes local knowledge.
- **Name compatibility inside Buildable.** Every included member is a head by
  `Current`. If included `d` and `e` share a name, the unique-head condition for
  `d` implies `e = d`.
- **Validity inside Buildable.** `Current` implies knowledge; knowledge implies
  publication; admission safety implies validity. Exporter acceptance and
  dependency closure do not follow from these facts and have separate mutations.
- **The duplicate-receive check.** Receiving an already known record adds nothing
  to the set. Deleting this guard adds a stuttering transition.
- **Receipts: Prepare's published-dependencies check.** The trusted validator
  issues a receipt for `g` only when `Deps[g]` is already published, staging
  needs a held receipt, and `published` only grows. So every staged or
  published group already has published dependencies and `DepsClosed` cannot
  fail. `receipt_prepare_no_deps` deletes the check and requires every
  Receipts invariant to survive. The check stays in the protocol as a cheap
  local rejection; it is not a safety guard.
- **Receipts: RelayReceive's published-dependencies check (W2 A-2).** Redundant
  in the model for the same reason (`receipt_relay_no_deps` requires the
  pass). The implementation keeps it in T9 because batch receipts may name a
  dependency that is not yet published, which is also why T1 reads it.
- **Certificates: Commit's own-reply-quorum check, under atomic certificates.**
  With the stranded-head fix every published group has a certificate quorum
  from publication on, and a committer knows only published groups, so
  `CheckpointDiscoverable` holds without the check
  (`cert_commit_unguarded_atomic` requires the pass). The check is necessary
  in the lagging design (`cert_commit_unguarded` on `CertificatesLagging`) and
  is kept: it is local, and it keeps commit safe if certificate writing ever
  lags publication again.
- **Targets: reading the head from the record rather than a scan, under atomic
  certificates.** See `target_scan_subset_atomic` below.

Alive/online checks constrain scheduling. They do not independently establish
the admission and snapshot invariants above. Crash suppression after `Heal` is
part of the progress assumptions, not an admission guard.

## Combined failure and useful-work witness

`CheckpointReuse` restricts the existing component transitions to this order:

1. Acknowledge the package and manifest; publish and commit a nonempty snapshot.
2. Destroy a disk in both acknowledgement quorums, holding both objects.
3. Crash and recover the worker through the actual registry actions.
4. Receive the published member while live copies of its package and manifest exist.
5. Commit the same nonempty snapshot again.

The stage variable records progress. Every selected action is an existing
`Publication.Next` action. `NeverReusedAfterLoss` must fail only after all five
steps. `checkpoint_loss_blocked` forbids disk loss after acknowledgement; the
same witness must then become unreachable. Separate acknowledgement and loss
witnesses would not detect that restriction.

The registry retains checkpoint identity across its worker crash. This witness
establishes reuse by known identity. It does not establish manifest enumeration,
recovery of a lost checkpoint hash, byte parsing, or source replay.

The independent full B→A→B chain and dependent-publication witnesses also remain
required. `dependent_work_blocked` rejects dependent declarations and must lose
both witnesses.

## Hardening guards

Each hardening model has its own mutations in `scripts/check-tla-negative.sh`.

| Model | Guard | Mutation | Required failure |
|---|---|---|---|
| Receipts | Staging needs a held receipt (the only receipt guard; publish is the base publish) | `unreceipted_staging`, `unreceipted_publication` (same deletion, two oracles) | `StagedValid`, `PublishedValid` |
| Receipts | T1 reads the issuer's cancellation (W2 A-2) | `receipt_publish_no_cancel` | `CancelledUnpublished` |
| Receipts | T9 at the issuer reads its cancellation (W2 A-2) | `receipt_relay_no_cancel` | `CancelledUnpublished` |
| Receipts | T9 at another deployment reads its own dependency markers (W2 A-2) | `receipt_remote_no_deps` | `RemoteDepsClosed` |
| Ingress | Per-event anti-entropy part cap before a part persists (W2 A-12) | `ingress_event_parts` | `EventPartsBounded` |
| Ingress | Per-event declared object-byte cap before an ObjectRef persists, so before any fetch (W2 A-12) | `ingress_event_objects` | `EventObjectsBounded` |
| Targets | Owner prepares | `target_no_owner_check` | `TargetChain` |
| Targets | Prepare revises the head in the owner record | `target_no_revise_head` | `TargetChain` |
| Targets | The head comes from the record, not a certificate scan | `target_scan_subset` (revise any `S` with `certified ⊆ S ⊆ published`), on `TargetsLagging` | `TargetChain` |
| Targets | Publish updates the recorded head | `target_no_head_update` | `TargetChain` |
| Targets | One pending proof per preparer | `target_no_single_pending` | `TargetChain` |
| Targets | Publish fenced on the prepare epoch | `target_no_epoch_fence` | `TargetChain` |
| Targets | Publish compares the job's controller-stamped statement with the pinned one (W2 A-4) | `target_no_statement_check`, on `TargetsStatement` | `PublishedPinned` |
| Targets | Publication writes the publisher's certificate quorum atomically | `target_stranded_head` (`AtomicCert = FALSE`), on `TargetsLive` | `HandoverProgress` (only property) |
| Fencing | First write conditional on the fence | `fencing_unfenced_put` | `StaleNeverStored` |
| Fencing | Repair copies bytes read from a live source replica | `fencing_repair_disguised` | `StaleNeverStored` |
| Fencing | Commit certificate conditional on the fence | `fencing_unfenced_commit`, `fencing_unfenced_commit_selected` (same deletion, two oracles) | `CertFenced`, `SelectedFenced` |
| Fencing | Commit certificate only after the writer's Ack | `fencing_cert_unacked` | `ScanFindsCertified` |
| Fencing | Scan adopts on live certificates, not byte quorums | `fencing_stale_selected` (adopts a record written before rotation and acknowledged after) | `NoLateAckedKnown` |
| Fencing | Commit certificate only over committed parents | `fencing_commit_orphan`, on `FencingLive` | `RecoveryAdopts` (only property) |
| Fencing | Certificate repair after a replica loss (fairness) | `fencing_no_cert_repair`, on `FencingLive` | `RecoveryAdopts` (only property) |
| Certificates | Receive reads certificates; put needs knowledge | `cert_scan_raw_marker`, `cert_put_unknown` | `ReceivedPublished`, `CertSound` |
| Certificates | Commit needs the committer's own reply quorum | `cert_commit_unguarded`, on `CertificatesLagging` | `CheckpointDiscoverable` |
| Certificates | Publication writes the publisher's certificates atomically | `cert_stranded_publication` (`AtomicCert = FALSE`), on `CertificatesLive` | `PublishedDiscoverable` (only property) |
| Workspace | Render from the known set; lineage winner; Lamport clock; live heads | `workspace_arrival_order`, `workspace_first_seen_winner`, `workspace_counter_clock`, `workspace_own_key_winner`, `workspace_render_superseded` | `SameKnownSameRender`, `IntentionPreserved`, `WinnerLineageKeepsName`, `NoSupersededRendered` |
| Workspace | A group superseded for any name holds no name | `workspace_superseded_holds_name` | `NameHeld` |
| Workspace | Receive needs the revision ancestor known | `workspace_receive_unknown_revision` | `RenderComplete` |
| WorkspacePending | Render by carried anchor paths, not the anchor tree of known records | `workspace_render_tree_order` | `RenderComplete` |
| WorkspacePending | Publish only once the anchor is known to the publisher (`PublishGuard`) | `workspace_no_publish_guard` | `AnchorClosed` |
| WorkspacePending | The clock covers the author's pending declarations | `workspace_known_clock` | `KeysUnique` |
| WorkspacePending | Staging may anchor at the author's own pending declaration (over-restriction) | `workspace_anchor_published_only` | loses `NeverOwnPendingAnchor` |

Every target guard conjunct is independently necessary. Each hardening model also
has reachability witnesses so a mutation cannot pass by blocking work: target
alternatives and handover; recovery after rotation, recovery of a record written
after the old writer re-acquired the fence (`NeverReacquiredRecovered`),
recovery of the middle-epoch (token 2) competitor after the fence moved on
(`NeverMiddleRecovered`), late acknowledgement and late repair; certificate
rediscovery and a commit after a lost replier; converged inserts, a resolved
collision, a revised winner, a deletion of a declaration the same agent had
rendered (`NeverDeleted` reads the ghost `rendered`) and a partial revision that
frees a name (`NeverPartialRevisionFreed`).

`target_scan_subset` encodes what a certificate scan guarantees: it sees every
proof with a certificate quorum and only published proofs. It runs on
`TargetsLagging` (certificates written after publication), where a new owner's
scan misses the head its predecessor published but had not yet certified.
Under the atomic-certificate fix a scan atomic with the prepare sees every
published proof, and the same mutation survives on `Targets`
(`target_scan_subset_atomic` requires that pass). The head record is still
required: a real scan is not atomic with the fenced prepare (the owner's own
publication can land between its scan and its next prepare), whereas the
record read and the conditional write are one store operation. This model
makes Prepare atomic and so cannot show that difference.

Workspace receive is in any order for anchors: rendering reads the anchor
path each record carries, so a declaration received before its anchor renders
at its position (`NeverEarlyArrivalRendered` must fail). Rendering by the anchor
tree of the known records instead drops it (`workspace_render_tree_order`).
Receive stays causal for the revision ancestor; deleting that guard keeps every
ordering and naming invariant but leaves a known live revision invisible.
`RenderComplete` states that every known live declaration is rendered. The
counter-clock mutation drops `ClockCovers` from its configuration, since that
invariant restates the Lamport rule; its oracle is `IntentionPreserved`.

`Fencing` no longer reads global state in its guards. Repair names its source
replica, and `Scan` reads certificates on live replicas. The ghost `writtenAt`
is reset when the last copy of a record is lost, so a second first write is
checked again. A record counts as committed for recovery (`CertDurable`) only
when every member of some fully live write quorum holds its certificate; after a
replica loss a single surviving holder no longer counts, and `CertRepair`
(copying an existing certificate, unconditional like byte repair) restores the
quorum. The record set is `a` (token 1), the middle-epoch competitor `m`
(token 2) and `d` (token 3); every token has a record.

Lean necessity witnesses for the Lean-only guards are listed in
the component notes (`scan_check_unsafe`, `partial_revision_frees_name`,
`own_pending_anchor`, `publish_guard_needed`, `render_reads_unknown_anchor`,
`reserved_check_needed`). The workspace guards for anchoring through the author's pending groups
also have TLA counterparts on `WorkspacePending` (above).

## Combined hardened model

`Hardened.tla` checks the receipt, target, certificate and catalogue guards on one
shared store ([HARDENED-TLA.md](tla/HARDENED-TLA.md)). `scripts/check-tla-hardened.sh`
runs it separately from the suites above: 2 positive instances, 8 coverage
witnesses, 16 single-guard mutations (each with a named violation) and 3
redundancy probes (each must pass). It adds three findings to the per-model
results.

- **The committer's own reply quorum is redundant under atomic publication.**
  `r_commit_without_own_quorum` deletes the checkpoint commit's own-reply-quorum
  check, and `PublishedDiscoverable`, `CheckpointDiscoverable`,
  `ReadySnapshotSound` and `CompletedRecoverable` still hold (7,628,232
  distinct states). The publish write already puts the publisher's certificates on
  every live replica. This matches `cert_commit_unguarded_atomic` above. If
  publication is not atomic the check is still needed (`cert_commit_unguarded` on
  `CertificatesLagging`).
- **An epoch-only publish condition needs the writer to keep the head it wrote.**
  The preparer's copy of the target record may lag. `m_no_learn_own_write` stops
  the writer from updating its copy after its own successful publish; the owner
  then prepares a second proof against the head it read before that publish, in
  the same epoch, the epoch condition accepts it, and `TargetChain` fails. A
  compare-and-swap on the head closes the same gap. Transaction T1 in
  [store.md](../docs/store.md#transactions) does this: it aborts unless the
  record's `head` equals the head the proof revises, as well as on owner and epoch.
- **The fenced commit certificate alone keeps stale records out of recovery and
  completion.** `r_unfenced_put_adoption` deletes the first-write fence and every
  target, certificate, adoption and completion invariant still holds
  (`ReadyCommitFenced`, `ReadySnapshotSound`, `CompletedRecoverable` among them).
  The first-write fence protects only `StaleNeverStored` and
  `ReadyFirstWriteFenced` (`m_unfenced_put` breaks `StaleNeverStored`).

A third probe, `r_ready_without_object_certs`, drops the object-certificate
conjunct from readiness and passes. In this model object certificates reach every
live replica at checkpoint commit, before any record for that snapshot can be put,
so the conjunct never decides readiness. That reflects the modelled write order
and certificate granularity, not that object certificates are unnecessary.

## W4 controller verification

### W4 history replay after compaction

`W4History.tla` models one request and one poll token as a local induction step
for controller-history compaction. A terminal work entry and its order entry
leave the current snapshot in the same fenced FDB transaction that writes its
immutable work replay row. A stable poll token moves to an immutable marker for
its original worker and first selection in that transaction; a first `NoWork`
token may move separately after logical grace. Pending work cannot move. The
marker preserves the first selection, while a late poll returns `Work` only if
that job remains pending with the same worker and assignment epoch. A duplicate
request checks the replay row's exact descriptor. Global J3 cancellation overlays
the immutable original terminal result, so a duplicate after cancellation
returns `Cancelled`. Turning off GC prevents new compaction but leaves replay
reads active. Crash clears a process's preparation; it cannot expose a partial
marker/head transaction. Retained old snapshot chunks remain roots under the
separate W4 snapshot GC model; this history model does not roll them back.

The bounded positive instance passes 3,780 distinct states with two workers,
two payload choices and two logical ticks. Seven reachability witnesses require
work and poll compaction, late work and poll retries, a retry after GC is turned
off, term handover and a duplicate after post-compaction cancellation. Eleven
guard mutations independently violate named properties: stale compactor fence,
terminal-state admission, missing work/poll replay marker, omitted work/poll
replay lookup, descriptor mismatch, wrong poll worker, work/poll grace and
missing J3 cancellation overlay. The model's one-request step lifts to a batch
only if every replay row and the shared pruned head commit in **one FDB
transaction**; disjoint marker keys alone are insufficient. Two-request crash
and unknown-commit integration tests are required to check that implementation
boundary. The model does not prove FDB atomicity, a total storage bound or
safe retirement of replay rows.

### W4 leases and snapshot collection

`W4Scale.tla` is a bounded, two-shard model for controller metadata. Each shard
has a monotone FoundationDB counter, lease holder, term and expiry counter.
Acquisition after expiry increments the term, including when the same process
reacquires. Stage records the term; publish transactionally checks holder,
unexpired counter and staged term. A stale pending save can be abandoned and
staged under a new term. No action reads wall time, so clock skew can only
change when monitors advance counters and when takeover happens; it cannot make
a stale term valid. The model does not prove a bound on how quickly a monitor
ticks or a standby takes over.

The GC domain is **controller snapshot incarnations**, not P2 protocol objects,
catalogue certificates or S3 keys. A snapshot incarnation may be reclaimed only
after a shard-local logical grace and a transactionally fresh root check. The
roots modeled are current shard heads, in-flight saves, retained references,
checkpoints, catalogue references, outstanding demands and (since the W3/W4
integration) W3 tombstone lineage: a tombstoned position leaves the live view,
but its record, certificates and anchor marker stay roots. Their dependency
closure crosses shard boundaries. A later authorized save may reuse the same
content hash as a collected incarnation; `NoResurrection` concerns the deleted
incarnation, not byte-level hash uniqueness. Recovery fetches require an explicit
demand and a live incarnation. Desktop index loss and subsequent requested
recovery are reachable. The recovery witness explicitly fetches a live root,
loses the desktop's local index, then requests and fetches that root again;
the witness flag is set only by the post-loss fetch. Physical protocol-object deletion remains deferred by
the grow-only contract in [store.md](../docs/store.md#p2-obligations-from-this-choice)
and [plan.md](../docs/plan.md).

The positive `W4Scale.cfg` instance checks root closure, incarnation
non-resurrection, the independent stale-publication observer, demanded fetches,
logical grace and absence of deleted outstanding demands. W4 alone explored
428,800 distinct states; with the tombstone root it explores 856,832. The
negative suite requires witnesses for handover, publication after handover,
cross-shard dependent publication, collection, retained roots, tombstoning and
desktop recovery. Removing either the term or expiry check violates
`NoStalePublish`; removing dependency closure or any one of pending, checkpoint,
catalogue, retained or tombstone roots (`w4_no_tombstone_root`) violates `RootsLive`;
removing demand protection violates `NoDemandDeleted`; removing grace violates
`GraceKept`; allowing unsolicited fetch violates `NoUnrequestedFetch`.

This finite instance proves safety for its bounded identities and schedules.
The handover publication is a reachability witness, not a temporal liveness
proof. It does not establish a real-time takeover bound, arbitrary dependency
depth, safe deletion of P2 objects, or a global production GC root inventory.

### W4-rest shard handover

`ShardHandover.tla` models Design 2 of [w4-rest-log.md](../docs/w4-rest-log.md):
bucket records `{shard, epoch, moving}`, the three-step move (Begin by the
authority, Export by the source leader, Import by the destination leader),
add and remove. Shards `A` and `B` start active with two candidate leader
processes each; `C` can be added and has one. Bucket `b1` (job `j1`, the
validation) starts at `A`; `b2` starts at `B` with job `j2` already queued, so a
move into `B` must merge without losing `j2`. One move is allowed; it may move
either bucket between any two active shards. A client submits `j1` and retries
arbitrarily; one worker polls and finishes it. Routing is adversarial: any
request may reach any shard's leader, which subsumes every stale bucket map.
Leader processes may be killed at any point, and a lease may lapse and be taken
over (term + 1) at any point, including in the middle of an operation. An
operation records its term at Load and commits under the lease and the
head-generation CAS; Export also holds the operation lock and drains its
in-flight validations. A validation is admitted under the operation lock and
then runs outside it: J1 issue and J2 receipt are separate fenced transactions.

The positive instance explores 6,538,594 distinct states (depth 34) and checks
`NoLoss` and `NoDup` (every submitted job lives in exactly one snapshot or
handoff record, and is admitted once), `Placement` (where a bucket's jobs and
validation index may live in each move state), `OwnerOnlyWrites` (an
independent observer: every committed job change, J1 and J2 is by the current
lease holder and term of the bucket's owner), `FinishApplies` (a finish is
either applied once or definitely refused only when the job is not running),
`ReceiptOnce` (held by J2's write-once key, not by any one fence),
`NoOrphanValidation` (a live validation past J1 runs at the
owner), `LoadedCurrent` (any process that can still pass the lease fence loaded
the current head) and `RemovedShardInert` (a retired shard owns nothing,
holds no jobs, is no move's destination and never writes again).

Witnesses (each `Never*` must be violated): `handover_move_done`;
`handover_src_killed` (the source leader is killed while the move is
`Prepared`, a leader of a later term exports and the move completes);
`handover_dst_killed` (the destination leader is killed while `Exported`, a
leader of a later term imports); `handover_finish_after_move` (a job running when exported
is finished at the destination); `handover_move_to_added` (add `C`, move to
it); `handover_removed` (an initial shard is emptied and removed);
`handover_receipt_while_moving` (a validation in flight at Begin records J2
while the move is `Prepared`, which is what the drain waits for).

| Check | Mutation | Required failure |
|---|---|---|
| Export removes the bucket's entries from the source snapshot | `handover_export_keeps_source` | `NoDup` |
| Import consumes the handoff record | `handover_import_keeps_handoff` | `NoDup` |
| Ownership changes only through Export (Begin sets `moving` only) | `handover_flip_without_handoff` | `Placement` |
| Definite answers refused while the bucket is moving (destination before import) | `handover_dest_serves_moving` | `FinishApplies` |
| Definite answers require ownership, read in the commit transaction | `handover_stale_answer` | `FinishApplies` |
| Work-route reservation requires owner and no move | `handover_submit_no_fence` | `NoDup` |
| ... including no move in progress | `handover_submit_while_moving` | `NoDup` |
| Export drains the source's in-flight validations | `handover_no_drain` | `NoOrphanValidation` |
| Drain and the J2 ownership check both removed | `handover_no_drain_no_receipt_owner` | `OwnerOnlyWrites` |
| Export under the source's lease and term | `handover_export_no_lease` | `OwnerOnlyWrites` |
| Remove requires owning no bucket | `handover_remove_owner` | `RemovedShardInert` |
| Remove requires no move in flight | `handover_remove_during_move` | `RemovedShardInert` |
| Remove sets the lease to a sentinel | `handover_no_sentinel` | `RemovedShardInert` |

Redundant checks (each deletion must leave every invariant intact):

- **Head-generation CAS on saves** (`handover_no_cas`). Every snapshot writer of
  a shard, including Export and Import, is that shard's leader under its
  operation lock, and a different process can only save under a newer term,
  which fails the older operation's term fence. `LoadedCurrent` checks the
  consequence directly. The CAS stays as defence in depth (for example against
  a future writer that does not take the operation lock).
- **J2 ownership check** (`handover_no_receipt_owner`). J1 is fenced by
  ownership and no move, so no validation enters a moving bucket; the drain
  waits for those admitted before Begin; a superseded leader's J2 fails the
  term fence. The check is the backstop for the drain:
  `handover_no_drain_no_receipt_owner` violates `OwnerOnlyWrites`.
- **T4 claim fence on assignment** (`handover_no_t4_fence`). Only the shard
  holding a job can assign it, and `Placement` keeps a job at its owner (or at
  the source while `Prepared`, where an assignment is carried by the export).
- **Import's move-state check** (`handover_import_no_state_check`). Import
  consumes the handoff, so a repeated import merges nothing, and a premature
  one (while `Prepared`) merges nothing and only ends the move with the bucket
  still at the source. The check stays so that a move record's state is
  monotone.

Design findings, with the fixes applied in the model:

1. **The J2 fence as written defeats the drain.** The design requires every
   bucket-keyed write, J2 included, to see no move in progress, and also has
   Export wait for in-flight validations. With both, a validation in flight at
   Begin can never record its receipt: the drain only waits for it to fail.
   `handover_literal_receipt_fence` restores the written fence and the
   `NeverReceiptWhileMoving` witness becomes unreachable (an expected pass).
   Fix: J2 requires `shard = self` only. J1 issue, reservation and T4 keep
   `shard = self` and no move in progress.
2. **Stale-routed definite answers drop finishes.** Requests are routed before
   the operation lock, so a finish can reach the source after Export (or the
   destination before Import). Answering from the snapshot, as today's
   `finish` does (`unknown work request`), gives a definite refusal for a job
   that is running in the handoff or at the destination; the worker ignores the
   answer and the result is lost until its lease expires. `handover_stale_answer`
   (the shortest trace sends the finish to a non-owner) and
   `handover_dest_serves_moving` violate `FinishApplies`. Fix: in dynamic
   mode a definite answer about a bucket's job (refusal or duplicate result) is
   given only if the operation's save transaction reads the bucket record with
   `shard = self` and no move; otherwise the answer is retryable (`moving` or
   `not controller shard`).

Scope limits. One move, one validation, one worker and one client job; `j2`
is passive. Lease expiry is abstracted to an immediate takeover with term + 1
(W4Scale checks the expiry fence). The process's in-memory copy is not stored;
`LoadedCurrent` justifies that for every commit that can pass the lease fence,
and mutations that remove a lease fence are caught at the commit by the
`OwnerOnlyWrites` observer. The reservation/T4 transaction and the save are one
commit here; in the implementation they are two transactions of one operation,
and a Begin between them is equivalent to a Begin after the commit because
Export needs the same operation lock or a newer term. Not modelled: the
takeover recovery pass that re-dispatches J1 envelopes (its dispatches must be
covered by the drain), worker leases and expiry re-queueing, cancellation
(J3), groups spanning buckets, handoff size limits, replay rows of compacted
work (see `ReplayHorizonShards`), and `controller/topology` epochs (no guard
reads them). FDB serializability is assumed.

### W4-rest replay horizons

`ReplayHorizon.tla` models Design 3 for one shard: generations 0 (legacy) to 3,
request IDs `r1` and `r2` (so a request is `(g, id)`), two leader processes, a
logical clock to 3 ticks with `H = 1` and `Grace = 1`, and at most three
distinct executed requests. Clients are adversarial: any `(g, id)` may be sent,
retried, delayed, duplicated or replayed at any time. A submission loads with
the snapshot and commits under the lease and term; the commit refuses
(`Expired`), deduplicates from the snapshot or a replay row, or executes.
Terminal work moves to a replay row in one transaction (W4History's step). The
advance is a separate leader task (read, then save under the lease and term);
the collector deletes rows under the lease. `--require-replay-generation` may be
switched on or off at any time.

The positive instance explores 4,861,494 distinct states (depth 32) and
checks `AtMostOnce` (no `(g, id)` executes twice), `RetiredRefused` (a retired
row's generation is refused), `ActiveNotLost` (executed unfinished work stays
running in the snapshot), `AnswerConsistent` (a duplicate is answered from its
own entry or row) and `LegacyKept` (no generation-0 row is ever deleted).
Witnesses: `horizon_advanced`, `horizon_retired`, `horizon_deduped` (a
duplicate answered from a replay row within the window) and
`horizon_refused_after_retire` (a retry of a retired request is refused).

| Check | Mutation | Required failure |
|---|---|---|
| Accept only `G` and `G - 1` (and 0) | `horizon_accept_old` | `AtMostOnce` |
| Retire only generations at most `G - 2` | `horizon_retire_previous` | `AtMostOnce` |
| Advance under the lease and term | `horizon_advance_no_fence` | `AtMostOnce` |
| Never retire generation 0 | `horizon_retire_legacy` | `LegacyKept` |
| Dedupe by the exact `(g, id)` | `horizon_dedupe_by_id` | `AnswerConsistent` |
| Only terminal work leaves the snapshot | `horizon_compact_active` | `ActiveNotLost` |
| Commit re-reads the generation in its transaction | `horizon_loaded_generation` | `AtMostOnce` |

`horizon_advance_no_fence` needs the advance's read-then-save: a superseded
leader writes `G = 2` after a newer leader reached `G = 3` and retired
generation 1, so generation 1 is accepted again.

Redundant check: **Grace** (`horizon_no_grace`). With the generation checked in
the commit transaction and `G` monotone, an accepted generation's rows are
never retirable, whatever the timing. Grace cannot replace the in-transaction
check either: logical ticks do not bound how long an operation takes.

Design findings, with the fixes applied in the models:

1. **Grace does not close the load-to-commit window.** As written, an
   operation decides with the generation it loaded. The advance runs under the
   lease and term but not the operation lock, so it, `Grace` ticks and a
   retirement can all land between Load and commit of a retry of a compacted
   request, which then executes again (`horizon_loaded_generation`,
   `AtMostOnce`, with Grace in place). Fix: the committing transaction reads
   `replay-gen` and refuses a generation no longer accepted (or the advance
   takes the operation lock).
2. **Per-shard generations break cross-shard replay reads.**
   `ReplayHorizonShards.tla` (562,556 distinct states; shards `A`, `B` and an
   addable `C`, one ID, generations 0 to 3) combines Design 3 with Design 2's
   rule that replay rows are read across every shard in the topology. As
   written, a shard retires its rows by its own `G`. Counterexample
   (`horizon_shard_local_retire`, `AtMostOnce`): `(1, r1)` executes and is
   compacted at `A`; `A` advances to `G = 3`; the bucket moves to `B`, still at
   `G = 1`; `A` retires the row after grace; the retry reaches `B`, which
   accepts generation 1, finds no row anywhere and executes again. Fix: retire
   a row of generation `g` only when every shard in the topology has refused
   `g` for `Grace` (read in the collector's transaction), and start an added
   shard at the topology's largest generation (`horizon_added_shard_low_gen`
   starts it at 1 and violates `AtMostOnce`). A single deployment-wide
   generation would also satisfy both. Witnesses: `horizon_shards_retired`,
   `horizon_shards_cross_dedupe` (a duplicate at `B` answered from `A`'s row).

Scope limits. Work requests only (poll tokens, group and validation request IDs
follow the same rule and are not modelled); one shard in `ReplayHorizon`;
leases abstracted as in `ShardHandover`; the collector's deletion is one
transaction and the advance is a read followed by a fenced save;
`ReplayHorizonShards` treats each action as
one fenced transaction of the current leader and abstracts the move to a route
change carrying active work. The `Expired` answer to a duplicate of still-running
old-generation work is definite but says nothing about execution: clients must
read it as "outcome unknown, too old", not "not executed".

## Liveness

| Scenario | Property | Fairness | Model |
|---|---|---|---|
| `Collision` | `EventualDelivery`, `Convergence`, `EventualCollision` | `Heal`, every receive | Registry |
| `Workspace`, `WorkspacePending` | `EventuallyIdentical` | receive | Workspace |
| `TargetsLive` | `HandoverProgress`: once stable, while a fresh proof id remains, the recorded head is eventually revised by a published proof | stabilization, the owner's prepare, publish, abandon, certify, receive | Targets, `AtomicCert = TRUE` |
| `FencingLive` | `RecoveryAdopts`: a record committed on a fully live write quorum is eventually adopted by recovery | scan, certificate repair | Fencing, records `a`, `d` |
| `CertificatesLive` | `CommittedDiscoverable`: a group in any checkpoint is eventually rediscovered by every node; `PublishedDiscoverable`: every publication is eventually discoverable by every node | certificate puts, scans | Certificates, `AtomicCert = TRUE`, one group |

Liveness instances use no symmetry reduction (TLC's symmetry is unsound for
liveness) and smaller constants than the safety instances. Crashes, replica
loss, index erasure, desktop loss, fence rotation and ownership handover get no
fairness. `Targets` adds the usual eventual-stability assumption (`Stabilize`,
as Registry's `Heal`): after it no crash or handover occurs. `Abandon` lets a
preparer drop a pending proof whose fenced publish failed.

Safety + reachability only: `Chain`, `Revision`, `Revert`, `Rejected`,
`Quorums`, `Integrated`, `CheckpointReuse`, `ExportRejected`, `Receipts`, and
the safety instances `Targets`, `TargetsLagging`, `Fencing`, `Certificates`,
`CertificatesLagging`.
The larger-scope instances (`ReceiptsWide`, `TargetsWide`, `FencingWide`,
`WorkspaceWide`; `check-tla.sh --wide`) are safety only and run no mutations.
The combined `Hardened` and `HardenedReacquire` instances are safety and
reachability only.

## The stranded head and its fix

The hardened design wrote discovery certificates after publication, and a
certificate write (`put`) needs the writer to know the group (`known n d`).
If every node that knows a just-published group loses its index (crash or
erasure) before writing a certificate quorum, no node can ever write one, no
scan can ever find the group, and no node can ever receive it. For a target
name the group is the recorded head. A new owner's prepare must revise the
recorded head and may only revise known proofs, so no owner can ever prepare
again: the target name is blocked forever.

The models show the gap and the fix with one constant, `AtomicCert`:

- `AtomicCert = FALSE` (original design). `target_stranded_head`: the
  publisher publishes p1 (the record head is now p1), crashes before
  certifying, ownership is reassigned (in TLC's trace, to the restarted
  publisher itself), the system stabilises, and no worker ever knows p1 again;
  `HandoverProgress` fails. `cert_stranded_publication`: the same at the
  certificate level; `PublishedDiscoverable` fails after `AckPublish` followed
  by `EraseIndexes`.
- `AtomicCert = TRUE` (fix). The publication transaction in the metadata store
  writes, atomically, the publication marker, the publisher's certificates on
  the write quorum that acknowledged the marker (with the publisher's record
  of those replies), and the target record's head update (the fenced
  conditional write). Every published group therefore has a certificate quorum
  from the instant it is published (`PublishedCertified`), so it is always
  discoverable, and `HandoverProgress`, `PublishedDiscoverable` and
  `CommittedDiscoverable` hold. All safety invariants hold under both settings
  (`Targets`/`TargetsLagging`, `Certificates`/`CertificatesLagging`).

The alternative, letting the target record's head itself count as discovery
evidence, was not adopted: it unblocks the head but not the proofs the head
revises. A new owner's prepare needs a revision set that is closed and known;
if an older proof in the head's revision chain was itself never certified,
the name stays blocked.

The Fencing parent-commit guard closes a related liveness gap found while
adding `RecoveryAdopts`: a record could be committed over a parent that was
acknowledged but whose writer was fenced out before committing it; recovery
adopts a record only with its parents, so that committed record was never
adoptable. `CommitCert` now reads the parents' certificates and requires each
to be committed (`ParentsCommittedOK`).

## Source replay and export lookup

W1 adds three finite, safety-only models of the Lean identity boundary. They
abstract kernel terms as distinct values; they do not model the elaborator or
prove cryptographic collision resistance.

| Model | Guard or association | Mutation | Required counterexample |
|---|---|---|---|
| `ReplayIdentity` | Replayed content must equal stored content | `replay_without_exact_identity` | `AcceptedExact` |
| `ExportLookup` | Associate generated declarations by raw hygiene key | `lookup_positional_queue` | `AttemptedKey` |
| `ExportLookup` | A key must have exactly one exported candidate | `lookup_no_uniqueness` | `AcceptedUnique` |
| `ExportLookup` | An exported declaration cannot serve two captured members | `lookup_no_reuse_guard` | `AcceptedNotReused` |
| `ExportLookup` | The matched declaration must still have exact stored content | `lookup_no_exact_identity` | `AcceptedExact` |
| `ExportLookupResidual` | Every exact-key candidate is reserved, including failed and ambiguous owners | `residual_no_exact_reservation` | `NoExactCandidateStolen` |
| `ExportLookupResidual` derived fixture | Residual fallback is allowed only when the captured full key has no exported candidates | `residual_no_fullkey_guard` | `NoAmbiguousAccepted` |
| `ExportLookupResidual` | A residual stem has one unmatched captured member | `residual_no_capture_uniqueness` | `NoTwoAccepted` |
| `ExportLookupResidual` | A residual stem has one available exported candidate | `residual_no_candidate_uniqueness` | `NoMultiAccepted` |
| `ExportLookupResidual` | Residual matching still requires exact stored content | `residual_no_exact_body` | `AcceptedExact` |

The replay model has witnesses for sensitive content succeeding in its original
module, failing in a synthetic module, and ordinary content succeeding in the
synthetic module. The lookup model has three successful initializer matches and
witnesses for changed literal content, ambiguous candidates, and declaration
reuse being rejected.

The residual model adds the stock F10 scope-ordinal drift witness and rejection
witnesses for a failed exact owner, attempted theft of its candidate, an
ambiguous exact owner and attempted theft of its candidates, two unmatched
captures, two residual candidates, and changed content. Exact-key reservation
is computed over all captured members, independently of whether their bodies
later validate. With that global reservation, phase ordering is a scheduling
choice rather than a separate safety guard; the reservation-removal mutation
tests the safety condition. A generated variant of the residual model adds a
third unclaimed exported candidate under the ambiguous owner's stem. The
variant passes all configured invariants; removing only the fallback's
`FullMatches(g) = {}` guard then admits the ambiguous owner with that third
candidate, violating `NoAmbiguousAccepted`. The script derives both cases in
temporary copies, so the pristine TLA model and its hash remain unchanged.

Both model and implementation reserve every full-key candidate before content
validation. The model marks a candidate used only after successful content
validation; `exportIdentity` also marks an associated candidate used before
`verifyExport` checks its body. The implementation is therefore stricter about
reuse after a content failure; the model's acceptance invariants do not claim
that every modeled acceptance is realized by the implementation. Raw-key matching is a
lookup operation, not a quotient of kernel literals. See
[the W1 identity analysis](../docs/w1-identity.md) for the concrete Lean evidence
and the limits of module-independent identity.

# W3 store/registry guard additions

The following finite models are part of the default positive and negative
suites. Each mutation changes a guard or projection while retaining an
independent oracle.

| Model | Removed rule | Negative case | Oracle |
|---|---|---|---|
| CheckpointConflicts | known-head freshness | `checkpoint_no_current` | `CommitCurrent` |
| CheckpointConflicts | duplicate binding rejection (with freshness disabled to expose its independent effect) | `checkpoint_no_buildable` | `CommittedBuildable` |
| CheckpointConflicts | selected dependency closure | `checkpoint_no_dependencies` | `CommittedDeps` |
| AgentAuthority | registered author key | `agent_no_registry` | `PublishedAuthorized` |
| AgentAuthority | key revocation | `agent_no_revocation` | `PublishedAuthorized` |
| AgentAuthority | controller fence | `agent_no_controller_fence` | `DeletedAuthorized` |
| AgentAuthority | original controller source | `agent_no_controller_source` | `DeletedAuthorized` |
| StorePositions | own-replica certificates | `position_foreign_certificate` | `LocalCertOnly` |
| StorePositions | position-specific deletion | `position_group_wide_delete` | `ReinsertVisible` |
| StorePositions | certified prior deletion for moves | `position_move_without_delete` | `MoveCertified` |
| StorePositions | registry preservation on deletion | `position_registry_erasure` | `TombstoneNeutral` |
| CatalogueExchange | original source proof | `catalogue_no_proof` | `OnlySourceCertified` |
| CatalogueExchange | certified parent first | `catalogue_no_parent` | `ParentClosed` |
| CatalogueExchange | receiver payload acknowledgement | `catalogue_no_ack` | `LocallyAcknowledged` |
| CatalogueExchange | source-qualified certificate namespace | `catalogue_local_certificate` | `FenceIsolation` |

`catalogue_relay` is a reachability witness for a replicated child record.
Catalogue fairness checks eventual delivery of committed records, without
requiring that a source creates a new commit. Cryptographic signatures and hash
implementations are abstracted by valid proof membership; Rust tests independently
corrupt signatures while keeping the signed object IDs unchanged.
