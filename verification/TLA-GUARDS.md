# Admission and freshness guard coverage

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
| Targets | Owner prepares | `target_no_owner_check` | `TargetChain` |
| Targets | Prepare revises the head in the owner record | `target_no_revise_head` | `TargetChain` |
| Targets | The head comes from the record, not a certificate scan | `target_scan_subset` (revise any `S` with `certified ⊆ S ⊆ published`), on `TargetsLagging` | `TargetChain` |
| Targets | Publish updates the recorded head | `target_no_head_update` | `TargetChain` |
| Targets | One pending proof per preparer | `target_no_single_pending` | `TargetChain` |
| Targets | Publish fenced on the prepare epoch | `target_no_epoch_fence` | `TargetChain` |
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
