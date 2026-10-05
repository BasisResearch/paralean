# Admission and freshness guard coverage

`scripts/check-tla-negative.sh` removes each effective admission or freshness
check below. It requires the named invariant or temporal error. A parser failure,
unrelated error, or arbitrary nonzero exit does not satisfy a check.

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
| Names retain every incomparable head | `silent_winner` | eventual collision property |
| Acknowledgement requires quorum persistence | `premature_ack` | `WitnessSurvives` |
| Publication requires acknowledgement | `unbacked_publication`, `staged_publication` | `PublicationGuard` |
| Checkpoint commit requires acknowledgement | `unbacked_checkpoint` | `CheckpointGuard` |
| Eventual recovery is required for progress | `no_fair_recovery` | temporal property |
| Fair receive service is required for progress | `no_fair_receive` | temporal property |

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
| Targets | Prepare revises the head in the owner record | `target_no_revise_head`; `target_scan_subset` (revise some subset of `published`, as a certificate scan would see) | `TargetChain` |
| Targets | Publish updates the recorded head | `target_no_head_update` | `TargetChain` |
| Targets | One pending proof per preparer | `target_no_single_pending` | `TargetChain` |
| Targets | Publish fenced on the prepare epoch | `target_no_epoch_fence` | `TargetChain` |
| Fencing | First write conditional on the fence | `fencing_unfenced_put` | `StaleNeverStored` |
| Fencing | Repair copies bytes read from a live source replica | `fencing_repair_disguised` | `StaleNeverStored` |
| Fencing | Commit certificate conditional on the fence | `fencing_unfenced_commit`, `fencing_unfenced_commit_selected` (same deletion, two oracles) | `CertFenced`, `SelectedFenced` |
| Fencing | Commit certificate only after the writer's Ack | `fencing_cert_unacked` | `ScanFindsCertified` |
| Fencing | Scan adopts on live certificates, not byte quorums | `fencing_stale_selected` (adopts a record written before rotation and acknowledged after) | `NoLateAckedKnown` |
| Certificates | Receive reads certificates; commit needs own reply quorum; put needs knowledge | `cert_scan_raw_marker`, `cert_commit_unguarded`, `cert_put_unknown` | `ReceivedPublished`, `CheckpointDiscoverable`, `CertSound` |
| Workspace | Render from the known set; lineage winner; Lamport clock; live heads | `workspace_arrival_order`, `workspace_first_seen_winner`, `workspace_counter_clock`, `workspace_own_key_winner`, `workspace_render_superseded` | `SameKnownSameRender`, `IntentionPreserved`, `WinnerLineageKeepsName`, `NoSupersededRendered` |
| Workspace | A group superseded for any name holds no name | `workspace_superseded_holds_name` | `NameHeld` |

Every target guard conjunct is independently necessary. Each hardening model also
has reachability witnesses so a mutation cannot pass by blocking work: target
alternatives and handover; recovery after rotation, recovery of a record written
after the old writer re-acquired the fence (`NeverReacquiredRecovered`), late
acknowledgement and late repair; certificate rediscovery and a commit after a
lost replier; converged inserts, a resolved collision, a revised winner, a
deletion and a partial revision that frees a name (`NeverPartialRevisionFreed`).

`Fencing` no longer reads global state in its guards. Repair names its source
replica, and `Scan` reads certificates on live replicas. The ghost `writtenAt`
is reset when the last copy of a record is lost, so a second first write is
checked again. Lean necessity witnesses for the Lean-only guards are listed in
the component notes (`scan_check_unsafe`, `partial_revision_frees_name`,
`own_pending_anchor`, `publish_guard_needed`, `render_reads_unknown_anchor`,
`reserved_check_needed`). The workspace guards for anchoring through the author's pending groups are
Lean-only: the TLA model has no pending state.
