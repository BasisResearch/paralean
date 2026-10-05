# Durable acknowledgement certificates

`Paralean/AckCertificates.lean` (namespace `ParaleanAckCertificates`) layers durable,
physically readable publication certificates over `ParaleanProtocol.Next`.
`ParaleanPublicationDiscovery` accepts a scanned marker by reading Durability's ghost
`acknowledged` flag, which no real store can observe: after replica loss a staged
marker and an acknowledged marker can have identical surviving bytes.

## Model
- `Extra node replica group` has two fields.
  - `cert r d`: physical store state. Replica `r` durably holds a certificate for
    the publication marker of `d`. Erased when `r` is lost.
  - `certReply n d r`: writer `n`'s own record that replica `r` acknowledged `n`'s
    certificate write for `d`. It is local to the writer, not store state, and is
    not erased when `r` is lost.
- `CertQuorumBy a e n d := ∃ w, ∀ r ∈ w, certReply n d r`: node `n` holds replies
  from a whole write quorum. The replies may have been collected at different
  times, and members may have been lost since. `CertQuorum a e d := ∃ n, CertQuorumBy a e n d`.
- `Next (s,e) (t,e') := ParaleanProtocol.Next s t ∧ Guard s e t e'`, where `Guard` is
  either a protocol step that satisfies `ReceiveGuard`, `CommitGuard` and
  `PublishWrite` from `clearLost s t e` (certificates of replicas that went from live
  to lost are erased), or an extra-only `CertStep` with `t = s`.
- `PublishWrite` (atomic publication certificates): a step that publishes nothing
  new leaves the certificates unchanged. A step that newly publishes `d`
  (`NewPub`) is one transaction that also writes, for a node `n` that knows `d`
  after the step (the publisher) and a write quorum `w` live after the step,
  `cert r d` and `certReply n d r` for every member `r` of `w` (`putQuorum`).
  `publish_write_enabled`: every base step that newly publishes `d` is the base
  publish, whose marker acknowledgement used a write quorum live after the step and
  whose publisher knows `d`; so the write never blocks a publication.
- `CertStep.put n r d`: `live r` and `known n d`. Sets `cert r d` and `certReply n d r`
  (`putCert e n r d`). There is no step that requires a whole write quorum to be
  live at one instant.
- `ReceiveGuard`: if `known n d` newly becomes true and `d` was already published,
  then `∃ q r, memberR r q ∧ live r ∧ cert r d`. A first publish is not affected.
- `CommitGuard`: if `head n` changes, every `d ∈ contents (head n)` satisfies
  `CertQuorumBy a e n d`, read from the committer's own replies. No ghost state is read.
- `guard_stutter`, `protocol_stutter`, `reachable_protocol` satisfy the layering contract.
- `WGuard`/`WNext`/`WReachable`: the same layer without `CommitGuard`;
  `reachable_weak` embeds the guarded runs.

## Proved (all `Reachable`, by induction over the real `Next`)
- `Core` (certificates name acknowledged markers, replies survive, published groups
  have a certificate quorum) is proved over `WReachable`, so it does not use
  `CommitGuard`; `reachable_checkpoint` adds the checkpoint clause.
- `cert_sound`: `cert r d → published d ∧ acknowledged (.publication d)`. Certificates
  are now also written by the publication step itself, only for the group it
  publishes, so every certificate still names a published group.
- `published_certified`: every published group has a certificate quorum (the
  publisher's, from the publication step on).
- `published_discoverable`, `published_receivable`: every published group is found by
  every fully live read-quorum scan, and any live, online node that does not know it
  can receive it by a guarded step. No publication can be stranded.
- `reply_survives`: `certReply n d r → live r → cert r d`. Uses that liveness only
  shrinks and that only loss erases certificates.
- `scan_complete`: `CertQuorum a e d` implies that every scan of a fully live read
  quorum finds `d` (`certScan`), via `meet` and `reply_survives`.
- `live_quorum_exists`: the failure envelope supplies a fully live read quorum.
- `scan_between`: for a fully live read quorum, the certificate scan `S` satisfies
  `CertQuorum ⊆ S ⊆ published` and `published ⊆ CertQuorum`, so `S = published`. It
  holds in every reachable state; it does not depend on worker indexes being erased.
- `checkpoint_contents_discoverable`: `d ∈ contents (head n)` implies
  `CertQuorumBy a e n d` and that every fully live read-quorum scan finds `d`.
- `checkpoint_discoverable_unguarded` (over `WReachable`): every checkpoint group is
  found by every fully live read-quorum scan without `CommitGuard`. Checkpoint groups
  are published (base registry safety) and published groups are certified. The
  commit guard is redundant for discoverability under atomic publication
  certificates (TLA: `cert_commit_unguarded_atomic` passes); it is kept as a local
  check that keeps commits safe if certificate writing ever lags publication again
  (TLA `cert_commit_unguarded` on `CertificatesLagging` fails without it).
- `receive_guard_sound`: physical evidence implies the base guard's `published` and
  `acknowledged` premises. `receive_guard_physical`: the hardened receive is enabled
  from the evidence plus `alive`, `online`, `¬known` alone.
- `Example.nonvacuous_certificate_rediscovery` (ProtocolExecution instance, 2
  replicas, write quorum both, read quorum replica `true`): each publication writes
  the publisher's certificate quorum (`eA_publisher_quorum`); the committer holds no
  replies before its own puts (`eA_committer_none`); the publisher's certificates
  serve both guarded receipts; the committer
  (node `true`) then collects replies in four separate `put` steps interleaved with
  manifest and catalogue writes; the catalogue commits; replica `false`, which
  replied for both groups, is lost; the checkpoint commit then succeeds from the
  committer's replies. After both workers crash (every index erased) and one
  recovers, the certificate scan of the surviving quorum finds both groups and the
  hardened receive succeeds.
- `Example.guard_necessity`: a base-reachable state after losing a replica in which
  the acknowledged marker of `false` and the staged marker of `true` have identical
  bytes on the live replica. No function of `(live, stored)` decides `acknowledged`,
  and no hardened run reaching that state holds a certificate for `true`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only (`results/lean/AckCertificates.log`).

## Discovery claim
Discovery after index loss is complete for every published group. The publication
transaction writes the publisher's certificates on the write quorum that
acknowledged the marker, so a group has a certificate quorum from the instant it is
published. In the earlier design certificates were written after publication, and
a group whose every knower lost its index before a certificate quorum existed could
never be certified, scanned or received again (TLA `cert_stranded_publication`;
for a target name the head is stranded and the name is blocked forever,
`target_stranded_head`). Any node that knows the group may still write further
certificates; the committer writes its own before a checkpoint commit.

## TLA
`tla/Certificates.tla` mirrors the model: `certReply[n][g]`, `CertPut(n, r, g)`,
`Commit(n, S)` guarded by `CertQuorumBy(n, g)` for every `g ∈ S`, and
`AckPublish(n, g, w)` which, with `AtomicCert = TRUE`, writes `n`'s certificates on
`w` (the Lean `PublishWrite`). `PublishedCertified` is the Lean
`published_certified`; `PublishedDiscoverable` and `CommittedDiscoverable` are
liveness properties checked only in TLA. Invariants:
`CertSound`, `CertLive`, `ReplySurvives`, `ScanComplete`, `ScanBetween`,
`CheckpointCertified`, `CheckpointDiscoverable`, `ReceivedPublished`. Replicas,
groups and nodes are model values under `SYMMETRY`. Mutations:
- `cert_commit_unguarded`: drop the reply-quorum conjunct from `Commit`; breaks
  `CheckpointDiscoverable`.
- `cert_put_unknown`: drop `g ∈ known[n]` from `CertPut`; breaks `CertSound`.
- `cert_scan_raw_marker`: scan marker bytes instead of certificates; breaks
  `ReceivedPublished`.
- Witnesses expected to fail: `NeverRediscoveredAfterLoss` (a checkpoint is
  rediscovered after loss and index erasure) and `NeverCommitWithLostReplier`
  (a commit succeeds although a replica that replied is already lost).

## Implementation contract
A certificate is a durable record, distinct from marker bytes, written only by a
writer that knows the group as published. The publisher's certificates are written
in the publication transaction itself (docs/store.md T1), on the write quorum that
acknowledged the marker; if the publication aborts, no certificate is written. A lost replica's records are gone.
Receipt of an already published group reads certificates from live replicas. A
checkpoint commit by node `n` requires that `n` has itself written a certificate
for every checkpoint group and received replies from every member of some write
quorum; the replies may arrive at different times.

## Assumptions
- Liveness only shrinks: replicas never rejoin. A rejoining replica with an empty
  store would invalidate `reply_survives`.
- Certificates are never garbage-collected.
- A writer's reply records persist for as long as it relies on them. The model
  never clears them, including across a node crash; clearing them would only
  disable commits, not affect safety.

## Not established
- Certificates use separate Extra state, not a `ParaleanArtifacts.Object` constructor.
  Their durability (`put` on a live replica, erasure on loss) mirrors Durability but
  is not a generated Durability object.
- Readers of `cert` are trusted to read only live replicas. The receive premise needs
  only some live certified replica; completeness needs a fully live read quorum.
- The model does not tie the certificate quorum `w` of the publication write to the
  quorum of the base marker `Ack`; it requires only that `w` is live after the step
  (which the `Ack` quorum is, `publish_write_enabled`).
- Replica rejoin, certificate garbage collection, and reply loss in transit.
- No fairness or liveness results are restated. TLA is an independent finite
  abstraction, not linked to the Lean model.
