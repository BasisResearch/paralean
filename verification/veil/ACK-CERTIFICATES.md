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
  either a protocol step that satisfies `ReceiveGuard` and `CommitGuard`, with
  `e' = clearLost s t e` (certificates of replicas that went from live to lost are
  erased), or an extra-only `CertStep` with `t = s`.
- `CertStep.put n r d`: `live r` and `known n d`. Sets `cert r d` and `certReply n d r`
  (`putCert e n r d`). There is no step that requires a whole write quorum to be
  live at one instant.
- `ReceiveGuard`: if `known n d` newly becomes true and `d` was already published,
  then `∃ q r, memberR r q ∧ live r ∧ cert r d`. A first publish is not affected.
- `CommitGuard`: if `head n` changes, every `d ∈ contents (head n)` satisfies
  `CertQuorumBy a e n d`, read from the committer's own replies. No ghost state is read.
- `guard_stutter`, `protocol_stutter`, `reachable_protocol` satisfy the layering contract.

## Proved (all `Reachable`, by induction over the real `Next`)
- `cert_sound`: `cert r d → published d ∧ acknowledged (.publication d)`.
- `reply_survives`: `certReply n d r → live r → cert r d`. Uses that liveness only
  shrinks and that only loss erases certificates.
- `scan_complete`: `CertQuorum a e d` implies that every scan of a fully live read
  quorum finds `d` (`certScan`), via `meet` and `reply_survives`.
- `live_quorum_exists`: the failure envelope supplies a fully live read quorum.
- `scan_between`: for a fully live read quorum, the certificate scan `S` satisfies
  `CertQuorum ⊆ S ⊆ published`. It holds in every reachable state; it does not
  depend on worker indexes being erased.
- `checkpoint_contents_discoverable`: `d ∈ contents (head n)` implies
  `CertQuorumBy a e n d` and that every fully live read-quorum scan finds `d`.
- `receive_guard_sound`: physical evidence implies the base guard's `published` and
  `acknowledged` premises. `receive_guard_physical`: the hardened receive is enabled
  from the evidence plus `alive`, `online`, `¬known` alone.
- `Example.nonvacuous_certificate_rediscovery` (ProtocolExecution instance, 2
  replicas, write quorum both, read quorum replica `true`): before the committer's
  puts no node holds a certificate quorum (`eA_no_quorum`); the publisher's
  certificates on replica `true` alone serve both guarded receipts; the committer
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
Discovery after index loss is complete for groups with a certificate quorum. A
published group without one is published but not yet discoverable after index
loss: publication (the marker acknowledgement) precedes certificate writes, so a
group can be published and orphaned before any certificate exists, and
certificates on fewer than a write quorum may be seen by one live read quorum and
not another. Any node that knows the group may write certificates. Checkpoints
only include groups for which the committer holds a certificate quorum, so no
checkpoint depends on an undiscoverable group.

## TLA
`tla/Certificates.tla` mirrors the model: `certReply[n][g]`, `CertPut(n, r, g)`,
`Commit(n, S)` guarded by `CertQuorumBy(n, g)` for every `g ∈ S`. Invariants:
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
writer that knows the group as published. A lost replica's records are gone.
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
- Discovery of a published group without a certificate quorum.
- Replica rejoin, certificate garbage collection, and reply loss in transit.
- No fairness or liveness results are restated. TLA is an independent finite
  abstraction, not linked to the Lean model.
