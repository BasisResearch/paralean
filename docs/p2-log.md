# P2 log

Branch `p2`, implementation in [impl/p2](../impl/p2/README.md). Services on aws-dev in user
space under `/data/home/kirancodes/paralean-p2/`: FoundationDB 7.3.79 (single, ssd-2) and
Garage 2.4.1 (replication 1, consistent mode) behind `s3-guard`. The leftovers (branch
`p2-rest`, [below](#leftovers-branch-p2-rest)) add instance clusters under
`.../paralean-p2/inst/<name>`: `ft` (FDB `triple`, 6 fdbservers in 6 zones, 5 coordinators,
behind `netsplit`; Garage 3 nodes, replication 3) and `ae-a`, `ae-b` (two independent
single-process deployments).

## Results (2026-10-06, live services)

- library unit tests 9/9 (PCE, IDs, objects, P1 golden vectors), s3-guard 1/1,
  guards 13/13, fixtures 9/9, faults 10/10, property test 150 cases / 0 failures,
  multi-process 1/1 (12 workers; 4 aborted at injected crash points, 2 SIGKILLed; audit clean,
  at most one head per target, selected records fenced).
- Garage checks: wrong `x-amz-checksum-sha256` is rejected (InvalidDigest), the checksum is
  echoed, 300 back-to-back PUT→GET read-after-write checks passed. No client-side fallback
  was needed; the client also re-hashes before PUT and after GET.
- Mutations (`scripts/check-mutations.sh`, the counterpart of TLA-GUARDS.md): all 11
  cases detected. Removing the owner check, the epoch fence, the head CAS, the atomic
  publisher certificate (lagging design), the T5 fence check or the T5 parent check each
  makes the named tests fail.
- FDB process kill (`scripts/fdb-kill-test.sh`): fdbserver SIGKILLed with 4 stress
  workers running, restarted after 4 s; every worker resolved its in-flight transactions
  (FDB errors retried, including real `commit_unknown_result`) and finished; audit clean.
- SHA-256 golden vectors computed by running P1's `Sha256.lean` with P1's toolchain match
  the Rust implementation, including a §1.2 preimage (`id::tests::matches_p1_lean_sha256`).
  Since deviation 10 was fixed, `scripts/p1-golden.sh` checks P1's group IDs against P2's
  for whole P1 stores instead (below).

## Leftovers (branch `p2-rest`)

Three things were not done on branch `p2`: faults inside a redundancy mode, tombstones and
anti-entropy between deployments. All runs below are against live services on aws-dev,
on instances of their own (`PARALEAN_INSTANCE`; the default cluster and the other agents'
instances were not touched).

### Faults within and beyond the redundancy mode (instance `ft`)

FDB runs `triple` on six fdbservers in six zones (`--locality-zoneid`), with coordinators on
five of them; `status` reports "Fault Tolerance - 2 zones". Garage runs three nodes in three
zones with replication factor 3 (quorum 2). Faults are SIGKILL, SIGSTOP/SIGCONT, network
partitions and disk wipes of single processes (`scripts/proc.sh`). Partitions go through
`netsplit`: each fdbserver listens on a private port and advertises a public port served by
the proxy, which reads the source process from FDB's `ConnectPacket` and blackholes every
link across the cut (no root or iptables on the shared box). Before each fault the script
waits until a probe write commits and FDB reports a fault tolerance of 2 again.
`scripts/fault-redundancy.sh`; logs in `results/p2/faults-ft/` (`stress` is run 4, runs
1–3 are `stress-run1` to `stress-run3`; `beyond`; `fixtures`).

**Within tolerance (`PHASE=stress`).** Six `paralean-p2 stress` workers run in a loop
throughout, each with random client-side faults (`--fault-p 0.02`). Every effect a call
returned as done is appended to an acknowledgement log: published groups with their markers,
committed records, tombstones, issued ranks and assignments. A probe commits and reads a key
once a second (5 s timeout). Faults, one step at a time, each after writes succeed and FDB
reports a fault tolerance of 2 again:

| Fault (run 4, 2026-10-06 23:46–23:53) | Probe outage | Back to tolerance 2 |
|---|---|---|
| SIGKILL fdbserver-1, restart after 10 s | none | 0 s |
| SIGSTOP fdbserver-2 for 15 s | ~11 s | 0 s after SIGCONT |
| partition fdbserver-3 for 15 s | ~8 s | 0 s after heal |
| SIGKILL fdbservers 0 and 4 (two coordinators) for 15 s | ~38 s | 28 s after restart |
| SIGSTOP fdbserver-1 and partition fdbserver-5 for 15 s | ~1 s | 0 s |
| partition fdbservers 2 and 3 together (the cut-off side holds two zones) for 15 s | ~32 s | 22 s after heal |
| SIGKILL fdbserver-2 and wipe its data dir (disk loss), restart empty | none | 91 s (re-replication) |
| SIGKILL and wipe fdbservers 3 and 5 (two disk losses) | none | 91 s |
| SIGKILL garage-0 (the gateway's first upstream) for 15 s | no worker error | 3/3 nodes after restart |
| SIGSTOP garage-1 for 15 s | no worker error | 3/3 |
| SIGKILL garage-2, replace its data disk, `garage repair blocks` | no worker error | 3/3 |

Run 4 results:

- 5150 acknowledged effects (2191 groups, 129 committed records, 471 tombstones, 1680
  ranks, 679 assignments); `verify-acks`: all present, **lost 0**.
- Audit clean: every marker and tombstone certified, every metadata key's S3 object present,
  one head per target, fenced commits, ranks `1..fence`.
- No worker error. Probe 96.7% OK (582 probes). The workers resolved real
  `commit_unknown_result`s and retried FDB errors.

Runs 1–3 (same schedule, harness bugs since fixed) also lost nothing and had clean audits.
They recorded 5905, 5375 and 3359 acknowledged effects:

- **Run 1.** One worker exited with SIGSEGV (finding below).
- **Run 2.** Garage-2 had not come back after run 1's disk wipe (finding below). Killing
  garage-0 then left one node of three, *beyond* tolerance by accident. Four worker rounds
  failed with "Could not reach quorum of 2" and acknowledged nothing.
- **Run 3.** A wipe raced its SIGKILL and was skipped.

**Beyond tolerance (`PHASE=beyond`, 2026-10-06 23:59 to 2026-10-07 00:02).**

- *FDB.* Three stress workers ran while fdbservers 0, 1 and 2 (three of five coordinators)
  were SIGKILLed for 30 s:
  - status became unavailable, and the probe failed for ~79 s;
  - the acknowledgement logs did not grow between 5 s and 30 s into the outage (188 lines
    both times): nothing was acknowledged during the outage;
  - a `discover` run during the outage gave no answer within 20 s (exit 124), and wrong
    data was never returned;
  - after restart: writes and tolerance 2 within 30 s, the workers finished, all 371
    acknowledged effects present, audit clean.
- *Garage.* With garage-1 and garage-2 SIGKILLed (one node of three, below quorum 2):
  - a publish failed: "PUT … not acknowledged after 8 attempts", ServiceUnavailable;
  - a verified read of an acknowledged group failed with an error, not wrong bytes;
  - no marker was written (142 before and after);
  - after restart, the same publish succeeded and the audit was clean.
- *Data loss beyond tolerance* (`PHASE=dataloss`, wiping three zones' disks) is in the
  script but was not run (it destroys the instance).

**Tests under chaos (`PHASE=fixtures`, 2026-10-07 00:09–00:20).** A chaos loop on `ft`
cycled through six fault kinds on random processes, 9 times each (54 faults). Each lasted
8 s, and the next started once writes succeeded and tolerance was 2 again. The kinds:

- SIGKILL;
- SIGSTOP;
- partition;
- SIGKILL of one process plus a partition of another;
- SIGSTOP of two processes;
- SIGKILL of a Garage node.

The test suites ran meanwhile on `ft`, with the anti-entropy peer on `ae-b`:

| Suite | Runs | Passed |
|---|---|---|
| fixtures | 20 | 180/180 |
| guards | 20 | 260/260 |
| tombstones | 20 | 100/100 |
| faults | 1 | 10/10 |
| antientropy | 1 | 8/8 |
| property (8 cases) | 1 | 1/1 |
| multiprocess (12 worker processes) | 1 | 1/1 |

The probe saw 28 outage windows of 1–32 s (72.6% of probes OK); the tests waited through
them. An earlier run with a harness bug (the chaos loop's counter was clobbered, so only
kills, pauses and partitions ran: 23 faults) also passed (`fixtures-run1`).

### Tombstones (§11.4)

A tombstone is a typed store kind with the publication discipline of markers:

- **Write path (T8).** The writer PUTs the tombstone's preimage to S3
  (`obj/tombstone/<id>`, the staged copy, as §8.2 step 2 for markers) and waits for the
  acknowledgement. One transaction then writes `tombstone/<id>` and the publisher's tombstone
  certificate `tcert/<id>/<writer>` (domain `v0/tcert`, signed). The transaction aborts
  unless all of the following hold:
  - the target is published *and certified* here (a raw `marker/` key is not evidence);
  - the target is in the tombstone's file;
  - the target's Lamport time is smaller than the tombstone's;
  - the tombstone's `author` is the target marker's author;
  - the writer is the workspace of the target's revisions;
  - no target record exists for any of the target's names;
  - a named receipt exists.

  A retry after an unknown outcome finds its own certificate. A tombstone key without this
  writer's certificate is refused (`TombstoneExists`).
- **Discovery** scans `tcert/` only. A tombstone counts iff a valid certificate names it and
  its stored bytes decode to that ID. Raw `tombstone/` keys are reported as ignored.
- **Rendering** (`recovery::render`, `Discovery.files`) is Workspaces' `render`. A file shows
  its *live* discovered groups: not deleted by a discovered tombstone of that file, and not
  superseded. A group is superseded when a discovered revision has one of its revisions as a
  transitive ancestor, for any name. The order is `PosLt`: carried root paths in RGA order
  (a proper prefix first, otherwise the larger `(lamport, author)` first), then the group's
  own key. It reads only fields carried by the markers (`render_carried`). A deleted or
  superseded declaration therefore leaves the rendered file after recovery. §11.4 says a
  tombstone "never removes the group from the registry, from snapshots, or as a
  dependency", so registry heads and catalogue recovery ignore tombstones. A checkpoint that
  holds a deleted group still commits and is adopted
  (`fixture_tombstoned_and_superseded_leave_the_rendered_file`).
- **Audit**, as for markers:
  - every stored tombstone is certified and its staged S3 copy exists;
  - every tombstone certificate names a stored tombstone with the same target;
  - every tombstone is a valid deletion (same file, older target, same author) of a
    published and certified group;
  - a named receipt exists.

Results on `ae-a`:

- `tombstones.rs` passes 5/5:
  - rendering after recovery;
  - a byte-identical uncertified tombstone is ignored;
  - every T8 guard;
  - unknown commit outcomes and crashes around T8;
  - a concurrent revision and tombstone.
- The property test now includes tombstone operations and checks after every step that no
  tombstoned group is rendered.
- The property test (with tombstone operations) passes 150 cases.
- Mutations: all 7 tombstone cases are detected (`scripts/check-mutations.sh`; the final
  run with all 22 cases on 2026-10-07 detected every one):

  | Mutation | Detected by |
  |---|---|
  | certificate in a later transaction | `tombstone_faults_resolve` (crash between leaves an uncertified tombstone) |
  | no target check | `t8_tombstone_guards` |
  | no author check | `t8_tombstone_guards` |
  | discovery reads raw tombstone keys | `fixture_uncertified_tombstone_is_ignored` |
  | render ignores tombstones | the rendering fixture and the property test |
  | render ignores supersession | the rendering fixture |

**Rules the models lack (not invented silently; P2's choices are marked):**

1. *A tombstone is not the models' tombstone.* `Workspaces.lean` (`Layout.tombstone`) and
   `Workspace.tla` (`Tomb[d] => Rev[d] # None`) model a tombstone as a *group*: a revision
   of its target, published through Groups and present in the registry. It supersedes the
   target for every name of the target. §11.4's tombstone is a separate object outside the
   registry. Rendering agrees: `Live` is the same predicate once "tombstoned by a known
   tombstone" replaces "has a known tombstone descendant". So `tombstone_not_rendered`,
   `render_carried` and `render_disappears` carry over. Registry consequences do not. In the
   model the tombstone becomes the head of the target's names, and commit freshness then
   excludes the target from new snapshots. Under §11.4 the target stays the head and
   snapshots may hold it. No model covers §11.4's registry-neutral tombstone. P2 follows
   §11.4.
2. *Who may delete (OPEN-19).* The models' `StageGuard` only says that the stager is the
   tombstone's author. No model restricts deletion to the target's author. P2 implements
   §11.4's v0 default (the element's author) and binds it to the certifying writer: the
   writer must be the workspace of the target's revisions. There is no agent registry
   (§11.6), so `author : AgentID` cannot be checked against a signer. The controller path is
   not implemented.
3. *Lamport.* `StageGuard` needs the tombstone's time to exceed everything the author knows.
   The store can check only the target's time.
4. *Target names.* TargetNames has no deletion. A model tombstone revising a target-name
   group would need the owner/epoch/head-CAS and would become the recorded head. P2 refuses
   such tombstones (`TombstoneOfTarget`). Conversely, T4 does not check tombstones: a free
   name whose group was deleted can later be assigned as a target name.
5. *Certificates.* AckCertificates certifies publications of groups. Tombstone
   certificates are its rules applied to the tombstone as a publication (§11.4: "stored,
   acknowledged and certificate-discovered like markers"). They need their own body and
   domain (`v0/tcert`), because a `v0/cert` names a marker and a group.
6. *Moves* (OPEN-20) and renaming under §11.5 (candidates exclude tombstoned groups) are not
   implemented in P2.

### Anti-entropy between deployments (instances `ae-a` and `ae-b`)

Each deployment has its own FDB cluster, its own Garage, its own fence, key file and
abstract replica σ. Under store.md's single-replica mapping, two deployments are two
abstract replicas (`antientropy.rs`):

- **Export.** A sender exports what it has *discovered*: payload objects with their IDs,
  then each group (marker, revisions, receipt, the job envelope the receipt answers, and the
  sender's certificates), then each tombstone (with its certificates). Raw markers and raw
  tombstones are never exported, and neither are groups whose validator the sender has
  revoked (since the merge with P3, below).
- **Verification at the receiver.** Every object is re-hashed against its ID. Every decoded
  object is checked against the IDs that name it: the marker names the revisions and the
  receipt; a certificate names the marker or the tombstone. Every certificate and receipt
  signature is verified under the receiver's key ring. The ring must list the peer's
  writers and validators (`KeyRing::trust`; the peer's fence authority is not trusted as an
  authority, only as an issuer of target-free job envelopes). Since the merge with P3, a
  group's receipt must pass P3's staging rule against its job envelope under the
  receiver's ring, and T9 reads the receiver's revocation of the validator (below).
  Undecodable, corrupt, truncated, forged and untrusted items are `Rejected`.
- **Application.** A group or tombstone needs at least one valid sender certificate (§8.3).
  It is applied only after its payloads are acknowledged by the receiver's own S3, and only
  when its revision parents (groups) or its target (tombstones) are published here.
  Otherwise it is `Deferred`. The receive is one idempotent transaction: T9 for groups,
  T10 for tombstones (with T8's guards against the receiver's copy of the target). It
  writes the objects if absent and the receiver's *own* certificate, signed by its sync
  writer and naming its own replica. AckCertificates `put` needs only that the writer knows
  the group as published, and §8.3 says "receiving requires a live replica certificate".
- **Sender certificates.** They are stored apart as evidence (`xcert/`), never under
  `cert/`, and discovery never counts them. The only certificate copy the model allows is
  T7 to a *replacement* of the same replica. T7 now also requires the certificate's
  `replica` to be this store's σ, so a copy between deployments is refused.
- **Duplicates, reordering and lost replies** are absorbed (`Present`, retry). Rounds repeat
  in both directions until neither side applies anything. A corrupt or missing payload at
  the receiver is re-PUT by the next round (content addressing makes that the store's
  repair copy).

Results (two clusters, `scripts/test.sh` with `PARALEAN_PEER_INSTANCE=ae-b`):

- `antientropy.rs` 8/8:
  - convergence;
  - rejection of corrupt objects, truncated items, tampered markers and revisions, forged
    and untrusted certificates, a receipt from an untrusted validator, and items without
    certificates, with no metadata written;
  - deferral until dependencies arrive (worst-case reversed order: objects, parent, child,
    tombstone, one level per round);
  - T9/T10 unknown commit outcomes and a receiver crash;
  - rot at the receiver repaired, rot at the sender waits;
  - marker conflicts reported;
  - foreign target names refused, and T7 between deployments refused.

  Every test also checks that each deployment's `cert/` and `tcert/` keys are signed by its
  own workspaces and name its own replica.
- `any_exchange_order_converges_to_the_union` (proptest) generates per side 1–5 random
  inserts, revisions and tombstones in one shared file. It then runs a random schedule of
  pushes in random directions. Each push shuffles the items and applies a per-item fault:
  drop (partial transfer), duplicate, bit flip or truncation. The audit must be clean on
  both sides after every push. A final fair sync must reach `PublishedSet(A) =
  PublishedSet(B)`: groups with their markers, tombstones and rendered files, equal to the
  union of what was published.
  Results: 48 cases passed (2026-10-07, two clusters, 79.6 s), and 8 more under chaos on
  `ft` with `ae-b`.
- Mutations, all 4 detected (two more since the merge with P3, below):
  - accept unverified certificates (`receiver_rejects_corrupt_forged_and_untrusted`);
  - store the sender's certificate as the receiver's own
    (`sync_converges_between_two_clusters`, the own-certificate check);
  - overwrite a conflicting marker (`marker_conflict_is_reported_not_overwritten`);
  - skip the payload acknowledgement (`corrupt_payloads_at_rest_are_repaired_or_wait`).
- CLI: `paralean-p2 sync w2 w2` between `ae-a` and `ae-b` (one group and a tombstone at A,
  one group at B) converged in 2 rounds: groups 2/2, tombstones 1/1.

**Where convergence needs rules the models lack:**

1. *Two markers for one group.* The store keeps one `marker/<g>`. The Workspaces model's
   `Layout` gives each group one file, anchor and key. §11.4 allows several markers to insert
   the same group ("the lowest `(lamport, author)` defines its position"). If two
   deployments publish the same group with different markers, the receiver reports
   `Conflict` and keeps its own marker. The group *sets* converge, the marker maps do not
   (`marker_conflict_is_reported_not_overwritten`). Convergence needs a multi-marker layout
   (`marker/<g>/<marker id>`) and a position rule over several markers per group, which no
   model has.
2. *Target names across deployments.* TargetNames has one linearizable record per name, in
   one store. Each deployment has its own records, so two deployments could each own `x`.
   P2 refuses to receive a group declaring a name that the receiver holds as a target
   (`ForeignTarget`). Since the merge with P3, a group published *as a target* is never
   received at all: its receipt binds the sender's target epoch, which only the sender's
   controller signs and only the sender's record fences, so it fails the receiver's staging
   rule. Such groups stay at their home deployment and the published sets differ by them. A
   free-name group declaring a name without a record at the receiver is still received as
   an ordinary name, so a registry conflict between two owners becomes visible after the
   exchange. A sound rule ("each target name is homed at exactly one deployment") is not
   modelled.
3. *Catalogue records* (`catalog/`, `rcert/`, `ocert/`) are not exchanged. They are fenced
   by their own deployment's fence, so ranks of another fence mean nothing, and nothing in
   CatalogFencing lets one deployment commit for another.
4. *Trust.* The key rings must already list the peer's writers and validators. Distributing
   them is out of band and not modelled.

## Merge with P3 (branch `integrate-p2-rest`)

`p2-rest` was merged into main at `7df9ace`, which holds P3 control's receipt binding
([p3-log](p3-log.md)) and P3 remote imports ([p3-remote-log](p3-remote-log.md)). The textual
conflicts in the store crate (`Cargo.toml` features and members, `audit.rs`, `faults.rs`,
`id.rs`) were additive: both sides' domains (`Job`, `Policy`, `Checker`, `Revocation`,
`TCert`), transaction tags (`P3Job`, `T8`–`T10`), audit fields (`suspect_receipts`,
`uncertified_tombstones`), mutation features and workspace members are kept. T1 is P3's
(staging rule, revocation and cancellation reads, the undeclared-target guard). Where the
two sides meet, behaviour changed as follows.

- **Receiving needs a receipt valid at the receiver (T9).** An anti-entropy group item now
  carries the signed job envelope its receipt answers (`job/<id>`). Before T9 the receiver
  runs P3's staging rule (`receipt::check`) under its *own* key ring: a trusted validator,
  an accepted verdict, an envelope from a trusted issuer, the receiver's pinned policy and
  checker. T9 then reads `vrevoke/<validator>` in its transaction, as T1 does, and writes
  `job/<id>` with the receipt, so the receiver's audit and P3's `published_receipt` re-check
  received groups like local ones. Cancellation (`jobcancel/`) is not read: request IDs
  belong to the issuing deployment.
- **Trust between deployments.** `KeyRing::trust(peer)` adds the peer's writers and
  validators as before, and now also the peer's controller and job issuers as issuers of
  *target-free* envelopes. Pins are not merged; the peer's controller is never this
  deployment's fence or revocation authority.
- **Target-bound groups stay home.** A receipt bound to target epochs needs an envelope
  signed by the controller of the deployment whose record fences those epochs (P3's rule
  4). No other deployment can check that, so such groups are `Rejected` with "receipt is
  bound to another deployment's target epochs". Before the merge they were received as
  ordinary names. `antientropy::exchangeable_set` is the published set without them; two
  deployments have converged when these are equal (the CLI's `sync` uses it).
- **Revocation at the sender.** `export` leaves out groups whose validator the sender has
  revoked (they are suspect there).
- **Tombstones (T8, T10).** A tombstone that names a receipt is refused when that receipt's
  validator is revoked; T8 reads `vrevoke/<key>` in its transaction. T10 shares the guard. A
  received tombstone whose named receipt has not arrived yet is now `Deferred`, not
  `Rejected`. Deleting a suspect group without naming a receipt stays possible.
- **Fixtures and CLI.** `fixture::package_by` signs envelopes with a given controller key,
  and the tests sign with their own deployment's controller. `keys init` without `--demo`
  now pins the fixture policy and checker. `publish-demo`, `checkpoint-demo` and `stress`
  sign envelopes with the key file's authority (before, random key files could not publish
  once T1 checked receipts). Every CLI command trusts `PARALEAN_PEER_KEYS` when it is set,
  so `audit` after a `sync` can verify received receipts and `xcert/` evidence.
- **P3 remote imports** now use the store API for tombstones and discovery (`plr tombstone`
  is `Writer::tombstone`, i.e. T8; `plr pull` takes tombstones from `discover`).

Three new tests: `received_groups_need_a_receipt_valid_here` (an unpinned checker at the
receiver, a revocation at the receiver, a revocation at the sender, envelopes stored with
received groups) and `t8_named_receipt_respects_revocation`; `receiver_rejects_…` also
covers a re-signed and a missing envelope. Two mutation features cover them:
`mutate-receive-no-receipt-check` (new) and P3's `mutate-no-revocation-check`, which now
also removes the T8/T9 reads.

**Results (2026-10-20, own instances `ia`, `ib` (single, ports 22200/22300) and `ift`
(FDB `triple`, 6 processes and 5 coordinators behind netsplit, Garage 3 nodes with
replication 3, port 22100)):**

| Suite | Result |
|---|---|
| library unit tests | 11/11 |
| s3-guard, netsplit | 1/1, 1/1 |
| guards, fixtures, faults | 13/13, 9/9, 10/10 |
| tombstones | 6/6 |
| antientropy (two clusters, `ia` with peer `ib`) | 9/9; the convergence proptest with 48 cases |
| property | 150 cases, 0 failures |
| multi-process | 1/1 |
| `check-mutations.sh` | 26/26 detected (the 22 earlier cases and 4 new) |
| `fault-redundancy.sh`, `PHASE=stress` on `ift` | PASS: 3978 acknowledged effects (1718 groups, 93 records, 366 tombstones, 1267 ranks, 534 assignments), lost 0, audit clean, no worker error; probe 96.2% OK |
| `fault-redundancy.sh`, `PHASE=fixtures FIXTURE_ROUNDS=3` on `ift` (peer `ib`) | PASS under 48 faults: fixtures 3×9, guards 3×13, tombstones 3×6, faults 10, antientropy 9 (8 cases), property (8 cases), multi-process 1; probe 67.7% OK |
| CLI `sync w2 w2` between `ia` and `ib`, random key files | 2 rounds; 4/4 exchangeable groups and 1/1 tombstones on both sides; A's target group rejected at B; both audits clean |

Logs are in `results/p2/faults-ift/`. The `beyond` and `dataloss` phases were not rerun.

## Fault-injection findings

- **Paginated scans truncated silently (fixed).** The first FDB kill run reported
  certificates without markers and multiple target heads. The cause was the scan, not the
  kill: it stopped at a batch shorter than its page size, but FDB returns partial batches
  (byte limits) with `more = true`. Once a key space exceeded one batch, discovery,
  catalogue recovery and the audit saw a subset (268 of 445 markers), breaking
  `scan_between` / `certScanValue_covers`; recovery could have selected an older record.
  The scan now continues on `more()`; `paginated_scan_follows_partial_batches` is the
  regression test. The rule is now a refinement obligation in store.md, under
  "Physical scan and enumeration" (branch `store-doc`). Small test deployments never exceed a batch, which is why the unit
  tests missed it; the audit caught it at scale.

- **T7 accepted a certificate naming another replica (fixed, `p2-rest`).** `repair_cert`
  checked the signature, the key and the existing bytes, but not the body's `replica`. A
  copy from deployment A into deployment B (another abstract replica) was therefore
  accepted, which certifies on A's behalf. T7 now requires `replica` = this store's σ
  (`t7_repair_is_unfenced_signed_and_needs_existing_bytes`,
  `foreign_target_names_and_certificate_copies_refused`).
- **Gray failures stall FDB longer than crashes (`ft`, run 4).** A SIGKILLed fdbserver or a
  wiped disk cost no probe failure at all; the cluster recruits around a refused connection
  at once. A SIGSTOPped or partitioned process costs 8–11 s, a two-process partition ~32 s,
  and two simultaneous kills ~38 s. In the traces of run 1, the long windows are the
  ratekeeper unable to read the storage-server list (`RkSSListFetchTimeout`, ~25 s) and a
  recovery waiting in `recruiting_transaction_servers` for up to 41 s
  (`RecruitStorageNotAvailable`). Clients see stalls, not errors, and nothing is lost. The
  failure-detection knobs were not tuned.
- **`status` fault tolerance is not availability.** While the probe's commits were failing,
  `max_zone_failures_without_losing_availability` already reported 2 again. The harness
  first waited on it and overlapped faults; it now also requires a probe commit before the
  next fault.
- **Garage does not start on a replaced (empty) data disk.** After the wipe it refuses to
  start: "Could not find expected marker file `garage-marker`". A hand-made marker is also
  refused ("Mismatched content"). The operator must remove `meta/data_layout`; Garage then
  re-creates the marker, and `garage repair blocks` resyncs. In run 1 the node silently
  stayed down, so run 2's next "tolerated" Garage fault left one node of three: an
  accidental beyond-tolerance fault. Correctly, PUTs failed ("Could not reach quorum of 2")
  and nothing was acknowledged. The harness now checks that all nodes are healthy between
  faults.
- **One SIGSEGV of a stress worker (undiagnosed).** In run 1, one worker process (one round
  of 25 operations) exited with 139 during the double disk-loss recovery. Every effect it
  acknowledged before dying was present afterwards. It was not reproduced in 400 short runs
  on a healthy cluster, nor in runs 2–4. The fault is native code: Rust code here is safe
  outside the FDB client library. The CLI now stops and joins the FDB network thread before
  exit (`meta::shutdown`), which removes one suspect, the client library's thread running
  during process teardown. No core dump was available.
- **s3-guard fails over on refused connections only.** A paused (SIGSTOP) first upstream
  accepts TCP connections and stalls each request until the S3 client's 20 s attempt
  timeout. The runs therefore pause garage-1, not the gateway's first upstream. Failing over
  on timeouts would be safe for this store (every PUT and GET is idempotent under content
  addressing) but is not implemented.
- A T3/T4 retry resolved only from "the state since my first attempt" misses a late,
  reordered duplicate and issues a second rank / reverts ownership. Fixed with grow-only
  request-index keys `treq/<request>` and `areq/<name>/<request>` written in the same
  transaction (and the `assign/<name>/<epoch>` log).
- A corrupt read of a payload during checkpoint commit aborts the commit
  (`NotAcknowledged`): safe, but a liveness cost; the writer could re-GET before giving up.
- FDB's default 5% operating-space reserve throttles all writes on a nearly full disk
  ("Log server running out of space"); `up.sh` lowers the knobs.

## Deviations from and gaps in store.md (exact places)

Items 1–9 are fixed in docs/store.md on branch `store-doc`. That branch also adds the
paginated-scan rule (continue while `more()`; never stop on a short batch) as a
refinement obligation under "Physical scan and enumeration". Item 10 is being fixed
in P1.

1. **Fixed in store.md (branch store-doc).** "Unfenced repair and acknowledgement" says an unknown-outcome T5 that committed before
   a rotation is retried, aborts, and leaves the record without a commit certificate. With
   T5 as in the Transactions table (record and `rcert` in one transaction) that is wrong:
   a committed T5 wrote the `rcert` too, the retry finds it and succeeds, and the record is
   (correctly) adopted. The late-ack case needs a staging write of the record before its
   commit. P2 implements that staging form (`stage_record`, fenced first write) and the
   fixture uses it; `fixture_put_before_rotation_acked_after` exercises both readings.
   Suggested sentence: "The late-acknowledgement case appears as a staging write of the
   record (fenced) whose outcome is resolved after a rotation; the commit T5 then aborts."
2. **Fixed in store.md (branch store-doc).** Layout: no domain for export manifests; P2 adds `v0/manifest` (sourceRoot, buildReceipt)
   and `v0/token`. T5's `ocert/manifest/<m>` is the record's snapshot, stored as
   `ocert/snapshot/<m>`.
3. **Fixed in store.md (branch store-doc).** Layout: ">64 kB values replaced in the marker by its ID" would change marker IDs. P2
   keeps IDs and uses a value envelope `0x01 ‖ objectID ‖ blobID`.
4. **Fixed in store.md (branch store-doc).** Layout additions: `treq/`, `areq/`, `assign/` (exact T3/T4 resolution, finding above).
5. **Fixed in store.md (branch store-doc).** §8.2 step 2 ("marker durably acknowledged") has no key; P2 PUTs the marker preimage to
   S3 `obj/marker/<id>` before T1.
6. **Fixed in store.md (branch store-doc).** T2 additionally requires an existing certificate (a raw marker key is not evidence),
   following §8.3 "receiving requires a live certificate".
7. **Fixed in store.md (branch store-doc).** Certificate bodies carry `replica`; a T7 copy to a *replacement* replica keeps σ, so
   the field cannot name the physical replica. Underspecified in §8.3/§9.
8. **Fixed in store.md (branch store-doc).** Signed objects (receipts, records, certificates) have ID = H(body); they cannot be stored
   as their preimage alone. P2 stores `bytes(preimage(body)) ‖ bytes(sig)`.
9. **Fixed in store.md (branch store-doc).** store.md calls Garage a way to avoid MinIO's AGPL; Garage is AGPL-3.0 too. MinIO
   community binaries are no longer distributed. Garage has no bucket policy or Object
   Lock, so deletes are refused by the `s3-guard` gateway; app credentials hitting Garage's
   port directly could still delete.
10. **Fixed (2026-10-06, branch `p1-encoding`).** P1 deviated from §1.2: P1 group IDs were
    SHA-256 of the raw `paralean-group-v2` bytes (no `"paralean\0v0/group\0"` prefix), and
    `H("v0/insttype")` omitted the prefix. P1 also encoded Lean `Nat` as LEB128, not §1.1
    big-endian `nat`. P1 now uses `H(domain, PCE(x))` for every ID it computes (`v0/group`,
    `v0/capsule`, `v0/package`, `v0/marker`, `v0/insttype`; the fork's instance hash too) and
    encoding `paralean-group-v3` with §1.1 `nat` for Lean `Nat` values
    ([p1-interface-notes.md](p1-interface-notes.md) §7). `import-p1` and the new offline
    `check-p1` require P2's group ID to equal P1's `declId` for every group (they did for all
    groups of the P1 gate stores; numbers in [fork-log.md](fork-log.md)), and
    `scripts/p1-golden.sh` is that equality check.

## store.md deltas (branch `p2-rest`; store.md itself is unchanged)

- **Layout.**
  - `tcert/<tombstone>/<writer>`: TombstoneCert `{replica, tombstoneID, target, writer}`,
    new domain `v0/tcert`, value `bytes(preimage) ‖ bytes(sig)`. Tombstones are discovered
    by these keys, as markers by `cert/`.
  - `xcert/<cert|tcert>/<object>/<replica>/<writer>`: another deployment's verified
    certificate kept as anti-entropy evidence. It is never a certificate of this deployment
    and is never read by discovery.
  - New S3 kind `tombstone` (domain `v0/tombstone`): the staged tombstone copy, acknowledged
    before T8.
- **Transactions.**
  - T8, publish tombstone `t` of group `g`:
    - reads `tombstone/<t>`, `tcert/<t>/<self>`, `marker/<g>`, one key of `cert/<g>/*`,
      `target/<x>` for each name `x` of `g`, and `receipt/<r>` if named;
    - writes `tombstone/<t>` and `tcert/<t>/<self>`;
    - aborts unless `g` is published and certified, in the same file, older, by the same
      author and the same workspace, has no target name, and a named receipt exists and its
      validator is not revoked (`vrevoke/<key>`, read in T8 since the merge with P3).
  - T9, receive group: writes `marker/<g>` if absent (aborts on another marker), revisions,
    receipt and `job/<envelope>` if absent, `cert/<g>/<self>` and `xcert/` evidence. It
    aborts on a name held as a target here, on a missing parent revision, or when
    `vrevoke/<validator>` exists here. Before it, the receiver checks P3's staging rule
    (`receipt::check`) under its own key ring.
  - T10, receive tombstone: T8's guards against the receiver's copy of the target; then
    `tombstone/<t>`, `tcert/<t>/<self>` and evidence.
- **T7.** A repair copy is accepted only if the certificate's `replica` is this store's σ,
  because a copy into another deployment would certify on its behalf.
- **"Abstraction".** Two deployments are two abstract replicas. Receiving at σ_B is Groups
  `receive` plus `CertStep.put` by the receiving writer on σ_B. Copying σ_A's certificate to
  σ_B is not a step of the model.
- **"The stores' own claims".** FoundationDB `triple` was run and faulted (results above),
  not just assumed.
- **P2 obligations.** Add tombstone fixtures (an uncertified tombstone is ignored; a deletion
  needs a certified target) and anti-entropy convergence under drops, duplicates and
  corruption.
- **Payload store.** s3-guard takes several Garage upstreams and fails over on connection
  errors. A paused (not dead) first upstream still stalls requests until S3 client
  timeouts.

## Not done

This is the historical `p2-rest` backlog. The `m-p2` workstream below records
which anti-entropy and fault items have since been implemented and verified,
with remaining limitations kept explicit.

- Buildability beyond the build-receipt verdict (unchanged from `p2`). Receipt binding is
  P3's (merged; see below).
- **Tombstones.**
  - Deletion by the controller (OPEN-19's second v0 case) is not implemented.
  - Moves (OPEN-20) and §11.5 renaming are not implemented. The rendered *names* are not
    computed; only the order and membership of rendered files are.
  - There is no agent registry, so `author` is checked against the target marker and the
    signing workspace, not against a registered agent key.
  - The registry-level meaning of a tombstone is unmodelled (model gap 1 above).
- **Anti-entropy.**
  - Catalogue records and their certificates are not exchanged.
  - Groups published with different markers at two deployments do not converge at the
    marker level (reported as conflicts).
  - Target names have no home-deployment rule.
  - The exchange is in-process (the sender's export is handed to the receiver's import as
    encoded items over two client connections), not a network service. There is no
    scheduling, batching or incremental cursor: every round exports the sender's whole
    discovered set.
  - Chunk objects are not transferred. P2 treats a group manifest as opaque and no metadata
    names its chunks, so the exporter cannot enumerate them.
- **Faults.**
  - All processes run on one host, so a "machine" is a process, and disks and the kernel
    are shared.
  - Garage nodes were killed, paused and given new disks but not partitioned: netsplit
    covers FDB's protocol only, and Garage's RPC port is not proxied.
  - Not exercised: changing coordinators after a permanent loss (`coordinators auto`),
    `three_data_hall`, and a Garage layout change after a permanent node loss (the disk
    replacements kept the node identity).
  - Gray failures (SIGSTOP, partitions) cost tens of seconds of unavailability; the FDB
    failure-detection knobs were not tuned (findings).
  - One stress worker exited with SIGSEGV once (run 1, during the double disk-loss
    recovery). It was not reproduced in 400 short runs or in the later fault runs, and its
    cause is undetermined (findings).

## Sentences for plan.md / README.md

- plan.md P2: "Implemented on branch p2 (impl/p2): FoundationDB 7.3 + Garage, T1–T7,
  certificate-based discovery and catalogue recovery, fault injection; gate tests pass
  against the live services (docs/p2-log.md)."
- plan.md P2, replacing "Not yet: FDB faults within a redundancy mode, tombstones (§11.4),
  anti-entropy between deployments": "Branch p2-rest adds tombstones (T8), anti-entropy
  between independent deployments (T9, T10), and fault runs inside and beyond FDB `triple`
  and Garage replication 3. Acknowledged effects were never lost and audits stayed clean.
  Open: catalogue exchange, marker conflicts and target-name homing across deployments
  (docs/p2-log.md)."

## Robustness workstream (`m-p2`, 2026-10-20, in progress)

Independent work began while `integrate-p2-rest` was being tested. The checkpoints
were rebased onto its completed merge `f384e4c` on 2026-10-20 after its published
log recorded passing tests, then onto `origin/main` at `cb1ca05` (including P4).
The independent results below predate those rebases;
merged-code verification is recorded separately as it completes.

- **Target home rule, model first.** `verification/tla/TargetHomes.tla` models one
  target with independent per-deployment owner/epoch/head registers. A shared,
  immutable home mapping permits prepare, publication and reassignment only at
  the home. Foreign receive requires the original home's publication evidence
  and leaves ownership registers unchanged. Forgetting the receive copies and
  non-home registers gives TargetNames' single authoritative register. All target
  names in a multi-target group must share a home; otherwise publication is
  rejected because there is no transaction across deployments. Configuration
  must be pinned before federation writes; home migration is outside this rule.
- **Model results.** `TLC_WORKERS=1 TLC_HEAP=1g scripts/check-tla.sh TargetHomes`:
  133 distinct states, safety and fair eventual delivery pass. The negative
  suite's `target_no_home` removes the home guard and reaches two incomparable
  published proofs, violating `TargetChain` even though both stores obey their
  local fences. Three reachability witnesses demonstrate home publication,
  remote receive and publication after reassignment. Logs with source hashes:
  `results/p2/target-homes/`. This is finite model checking plus a written
  refinement argument, not a new Lean theorem.
- **Anti-entropy design and store delta.**
  [p2-antientropy-design.md](p2-antientropy-design.md) specifies commit-versionstamp
  events, bounded network pages and object fetches, durable deferred events before
  cursor advancement, chunk references bound by group bytes, and source-qualified
  catalogue certificates. The store, signed transport, scheduled service and CLI
  are implemented; merged-code verification is in progress.
- **Garage proxy.** The independent `garage-netsplit` crate uses distinct loopback
  source addresses and Garage's `rpc_bind_outgoing` to identify both ends of RPC
  links. It blackholes crossing links, including existing connections, and closes
  them on healing. Six unit/TCP tests pass. The live partition test passed using
  staged instance scripts; the proxy is now integrated into the merged instance
  scripts and workspace.
- **Fault studies and cluster gates.** The gray-failure study and permanent
  coordinator-loss, Garage and bounded SIGSEGV results are below. Merged-code
  gates remain in progress on private `mp2-*` instances. No other agent's instance
  is used or modified.

### Independent fault-study results

FDB 7.3.79, private `mp2-gray`, five processes with distinct zones, `triple`,
five coordinators, through netsplit; no Garage or stress workers. Three trials
per setting pause process 2 for 15 seconds, then partition process 3 for 15
seconds, waiting for a committed probe and tolerance 2 between faults. Each
serial read/write probe has an eight-second timeout and a one-second gap.
Numbers below bracket observed unavailability between adjacent successful
completions; they are not exact outage durations. No failed probe does not
mean no stall.

| Setting | SIGSTOP failed samples per trial | Partition failed samples per trial | Median partition success bracket |
|---|---|---|---|
| Pinned default failure delay 4.0 s | 0, 1, 1 | 2, 2, 2 | 17.470 s |
| Failure delay 1.0 s | 0, 1, 1 | 2, 2, 2 | 17.631 s |
| Delay 1.0 s, connection timeout 0.5 s, monitor interval 0.25 s | 0, 0, 0 | 4, 4, 4 | 43.709 s |

The first candidate provides no demonstrated improvement. The aggressive
candidate reduces sampled pause failures but substantially worsens partition
recovery, so neither becomes the default. In the aggressive candidate's first
partition, traces show 41.856 seconds in `recruiting_transaction_servers`,
33 `RecruitStorageNotAvailable` events and 23 `RkSSListFetchTimeout` events.
The dominant long recovery is recruitment, not just the initial failure delay.
This experiment does not establish an optimal production tuning.

Raw timing rows, fault timestamps, summaries and a trace excerpt are in
`results/p2/robustness-mp2-gray/`; the method and reproduction commands are in
`results/p2/robustness-study.md`. The timing analyzer was reviewed and its totals
checked independently against the raw rows.

**Permanent coordinator loss: pass.** Private `mp2-coord` used six FDB processes,
five initial coordinators, distinct loopback IPs and zones, and `triple`.
Coordinator `127.0.0.2:24200` was killed and never restarted. `coordinators auto`
reported `Coordination state changed` and replaced the dead endpoint with
`127.0.0.7:24205`. The pre-loss acknowledged value remained readable, and a new
write/read succeeded. Artifacts: `results/p2/robustness-mp2-coord/coordinator/`.
Distinct IPs let the single-host test exercise the automatic coordinator
selection rule. Both FDB-only study instances were stopped afterward.

**Garage RPC partition: pass with a measured stall.** Private `mp2-garage`
used three Garage 2.4.1 nodes behind the new proxy. After isolating node 2, its
PUT timed out without acknowledgement. Nodes 0 and 1 eventually acknowledged
and served a new object. The combined majority PUT/read stage lasted about
59 seconds (03:11:21–03:12:20 UTC); the original harness overwrote retry errors,
so that run cannot establish the retry count or a more precise outage duration.
Its raw final line saying “remained available” must be read with this qualification.
The harness now preserves every attempt's duration, exit and error. After healing,
all nodes returned both pre-partition and majority-acknowledged bytes. Root
independently compared the saved payloads. Artifacts:
`results/p2/garage-partition-mp2-garage-20261020T031053Z/`.

**Garage permanent loss and layout replacement: pass.** On the same private
instance, node 2 was killed permanently and its role replaced by a new node 3.
The first harness command used an invalid `--replace` argument order; the
corrected remaining steps were executed manually without restarting node 2.
Layout version 2 moved 256 partition copies. Because the dead node could not
acknowledge the new layout, `layout skip-dead-nodes --version 2` was required;
`--allow-missing-data` was not used. Final health was `HEALTHY`, with all three
storage nodes up and all 256 partitions fully healthy. Pre-loss acknowledged
bytes were read through the surviving and replacement nodes, and a post-change
write was read through the replacement. Root independently checked the saved
payloads. The harness records the corrected assignment and dead-node skip.
Artifacts, including the manual continuation and before/after health:
`results/p2/robustness-mp2-garage/garage-layout/`.

### Stress-worker SIGSEGV follow-up (private `mp2-segv`)

The prior run-1 log records worker 3, seed 3045, exiting 139. It records the
fdbserver-3 plus fdbserver-5 double disk loss, but worker errors were collected
only at the end, so the original crash time and stack are unknown. Commit
`667dcf6` added an explicit `meta::shutdown()` that joins the FDB network thread
before CLI process exit; that is a plausible teardown fix, not a proven cause of
run 1's crash.

We repeated the 3+5 kill, disk wipe, five-second delay and restart in private
`mp2-segv` using the exact staged `origin/p2-rest` source `b2056d2` and FDB 7.3.79.
Ten GDB-managed 25-operation workers used the CLI with explicit shutdown. Another
ten used a binary built from identical source with only the shutdown call removed
(the exact patch and binary hashes are saved in
`results/p2/robustness-mp2-segv/`). Every worker was alive at its fault
injection. The harness enabled unlimited core size; GDB was set to capture a
SIGSEGV, all-thread backtrace and core before the host's apport handler. None
occurred: both arms had ten normal inferior exits, 250 acknowledged effects,
10/10 `verify-acks` checks with zero lost effects, and 10/10 clean audits. The
cluster regained write availability and FDB fault tolerance 2 between attempts,
then was fully stopped.

**Not reproduced or explained conclusively.** The original run had six concurrent
workers, three Garage nodes and preceding faults. This bounded A/B used one worker,
one Garage node and only the repeated double-loss schedule; GDB also perturbs
timing. A six-worker replay with the original six FDB plus three Garage nodes
would exceed the shared box's eight-heavy-process limit. No core was produced
because no crash occurred. The explicit network-thread shutdown remains a
source-supported candidate fix, without direct reproduction evidence.

### P2 anti-entropy `store.md` delta and plan/README wording

The following is the precise delta for a later `docs/store.md` revision; it is
recorded here because this workstream does not alter that specification in place.
The implementation design and wire/store API contract are in
`docs/p2-antientropy-design.md`.

- **Layout:** add `federation/config` and `aegeneration`; append-only
  `aelog/<commit-versionstamp>/<operation>`; receiver state
  `aecursor/<source>`, `aepending/<source>/<event>`,
  `aeterminal/<source>/<event>`, `aepart/<source>/<event>/<sequence>` and
  `aecount/<source>` (active pending rows only); authenticated
  `gchunks/<group>`; compatible marker copies
  `mvariant/<group>/<marker>` and `vcer/<group>/<marker>/<writer>`;
  exact signed-job evidence `jobproof/<group>/<marker>/<publisher-cert>`;
  certificate-ID-keyed `xcertv/<kind>/<object>/<cert>`; and source-qualified
  `xcatalog/<source>/<id>`, `xrcert/<source>/<id>`,
  `xtoken/<source>/<rank>`, `xrevision/<source>/<id>` and
  `xocert/<source>/<kind>/<id>`. Existing `xcert/` remains readable as legacy
  foreign evidence. Foreign proof never satisfies a local `cert/`, `tcert/`,
  `rcert/` or `ocert/` guard.
- **Transactions:** pin a shared, immutable member/key/target-home roster only
  on a new empty deployment; a preexisting local deployment requires an
  explicit migration with a write barrier and event backfill. T1, T4, T8, T9
  and T10 read that persisted roster inside their write transaction. A target
  name may be prepared, published or reassigned only at its configured home;
  all target names in one group have the same home. A foreign copy requires
  the original home controller's signed target job and a home writer's source
  certificate, and cannot update the receiver's target record. T8/T10 cannot
  delete a configured target proof even if the receiver has no local
  `target/<name>` key. T1/T8/T9/T10 and ready T5 append a versionstamped event
  atomically with their first publication. T2/T6 and newly imported evidence
  append a separate exact-certificate event only when transferable state grows.
  T1/T9 retain the exact signed job paired with a publication certificate even
  when another signed job has the same content ID, so relays cannot substitute
  a different deployment's signature.
  Cursor movement and pending-fragment insertion are one transaction; import
  of a verified foreign catalogue is one source-qualified transaction that
  never advances a local fence. A terminal outcome atomically archives its
  event and reason, deletes active pending/fragments and frees its quota slot;
  terminal diagnostics remain pageable and cannot starve later valid events.
- **Content-addressed writes and refinement:** a new group wrapper begins with
  raw `paralean-group-chunked-v1`, then a PCE version, opaque core and ordered
  `(chunk ID, stored-preimage length)` references. Its full bytes remain under
  `v0/group`; the refs are authenticated by that group ID and checked against
  `gchunks`. New wrappers admit at most 2,048 ordered references, bounding the
  one-value derived index to 75,778 bytes at maximum distinct IDs and lengths,
  below FoundationDB's 100,000-byte value limit. T1/T9 require local
  acknowledgements for each referenced chunk.
  Legacy opaque P1 groups have unknown chunk coverage, rather than an asserted
  empty chunk set. Commit-versionstamp pagination prevents inserts behind a
  cursor; `more()` is followed even after a short FDB batch. A deferred event
  is durably queued before the cursor passes it, then replayed idempotently.
  Receipt-only marker variants preserve immutable placement, revisions, root
  and lineage; the lowest locally certified, non-revoked variant is preferred.
  If none qualifies, lookup selects a certified suspect variant, then the
  legacy base for inspection; discovery still requires a valid local
  certificate, and the fallback does not admit a new revoked receipt.
  Other marker differences produce a field-level diagnostic. Source-signed
  catalogue records, tokens and certificates remain source-qualified and do
  not become local fenced commits. The target-home rule is checked by the new
  `TargetHomes.tla` model refining TargetNames and its mutation case.
- **Trust boundary:** signed TCP frames authenticate configured deployments but
  carry plaintext. An authenticated federation member can `Fetch` any known
  content-addressed object, including staged/unpublished bytes. This does not
  satisfy the receipt, publication or source-certificate guards. Deployments
  must trust their peers as content readers and protect the network path if
  confidentiality is required; P2 does not claim certificate-gated read access.

The P2 plan/README sentence is: “P2 anti-entropy is a scheduled, authenticated
TCP service with commit-ordered bounded pages, durable replay cursors, chunk and
source-qualified catalogue transfer, and a pinned target-home rule; legacy
in-process export remains for compatibility and opaque P1 groups do not expose
complete chunk references.”

### Network implementation checkpoint (merged main `cb1ca05`)

The new `ae-wire`, `ae-service`, store event/cursor APIs and CLI are implemented.
The root agent reviewed and integrated the delegated store, transport, fault
harness and test changes. The first workspace all-targets check passed; the
network integration suite now passes **13/13** on private `mp2-net` (distinct
logical deployment roots, writers, replicas, validators and transport keys).
Transport and Garage proxy tests passed **9/9** and **6/6** respectively. Raw logs:
`results/p2/network-service/`. The baseline P2/P3 and scoped fault reruns are still
pending at this checkpoint.

The network tests cover three-hop group/tombstone, home-target and catalogue
relay; exact original certificates; bounded descriptors and durable restart
replay; new publications after startup; missing/corrupt payload repair; chunk
metadata; configuration and generation rejection; receipt-only marker convergence
and revocation; and precise incompatible-layout diagnostics. The stronger marker
test also requires that valid variants leave no terminal pending events. A simultaneous
first-receive test covers compatible variants racing to fill the marker slot.

Two real failures found during review/testing were fixed rather than weakening
the cases. A mutable S3 HEAD length could persist corrupt-object length metadata
and prevent later repair: materialization now derives lengths from hash-verified
GETs and checks derived chunk indexes against the group bytes. This costs a GET
for referenced non-chunk objects when materializing an event, including continuation
pages; chunk lengths come from the authenticated group manifest. It still avoids
full-store export each round. Also, signed jobs with equal
body IDs can have different issuer signatures: `jobproof` retains the exact
signed envelope paired with the publisher certificate, so relay events cannot
substitute another deployment's signature. A concurrent first-receive race now
defers for restaging when another marker wins the slot before T9 commits.

### Merged baseline verification and final review

On main `cb1ca05`, the final marker fast path passed the store baseline
**53/53**, the property suite with **150 cases**, and legacy anti-entropy
**9/9 with 48 randomized cases**. P3's adversarial suite passed **13/13**.
The guard-removal matrix detected **26/26** listed mutation/test pairs.
Evidence is in `results/p2/merged-gates/`; `context.json` identifies the pinned
fork and the read-only P1 artifacts, whose sources match merged main. The
fast path only avoids certificate/receipt reads when no marker variants exist;
the return value remains the legacy base marker. The anti-entropy run took
332.48 s after this change versus 404.61 s immediately before it on the shared
host; this is not a controlled benchmark or a claim about the historical runs.

The expanded network suite passed **14/14**, including durable continuation
from an 80 KiB marker split across metadata pages. Two actual CLI service
processes on independent `mp2-net` and `mp2-peer` instances passed publication,
target receipt, catalogue, incremental restart and graceful SIGTERM checks.
The final smoke evidence is
`results/p2/ae-cli-smoke-20261020T042041Z-2398435/`; private authority and
transport keys remain under ignored `.runs/`.
Two earlier smoke attempts are retained: the first incorrectly searched the
abbreviated `discover` output for a full ID, and the second signalled a shell
wrapper instead of the service process. The corrected script checks an exact-ID
GET and uses `exec` so SIGTERM and `wait` address the actual daemon.

Final review found that retained terminal conflicts could exhaust the 10,000
active-event quota and prevent newer valid events from arriving. Terminal
diagnostics now move atomically to `aeterminal`, freeing the active count and
staged fragments. Stale retries cannot resurrect an archived event. The
network suite passed **14/14 again** after this fix; the conflict regression
checks the exact durable diagnostic, zero active count, cleared fragments,
repeated conflict status, and arrival of a later unrelated group.
`ae-status` pages archived diagnostics separately. `--once` retains a nonzero
conflict result, using one archive entry as an indicator rather than scanning
or counting the entire archive.

The first plain remote gate run exposed its fixed 1.5-second validator startup
race: Bob's initial validation got `Connection refused`, causing gate items
1 and 7 to fail while later validations and the other checks passed. That
failure is retained in `p3-remote-final.log`. The P2-owned
`scripts/remote-gate.py` runner loads the unchanged P3 scenario and replaces
only its startup sleep with a bounded readiness wait. The rerun passed **10/10**
gate checks in **200.4 s**, including clean export and identical re-encoding of
**11/11 groups**. Both result JSON files and console logs are retained under
`results/p2/merged-gates/`. No P3 scenario assertion was changed.

The multiprocess suite also passed all twelve worker configurations in waves of
three: seven completed, three aborted at injected crash points, and two were
deliberately killed. Its audit checked 117 certified groups, 27 committed
records, 368 object certificates, three targets and 29 tombstones. Normal
production binaries and all workspace tests were rebuilt after the archive fix;
their hashes are in `binary-sha256-archive.txt`. Implementation checkpoint
`5179bcd` is pushed; the scoped fault phases remain in progress.

### Merged fault-run findings

The FDB stress phase passed all eight kill/pause/partition and single/double
disk-loss stages on six FDB processes (`triple`, five coordinators) plus one
Garage node and one worker. All **1,339 acknowledged effects** were present;
the audit passed with 494 certified groups, 306 committed records and
89 tombstones. There were no worker errors. After the double disk loss,
reported tolerance for two zone failures returned 100 seconds after restart.
The serial probe succeeded 188/203 times; these are samples, not a continuous
availability measurement. Exact commands and evidence:
`results/p2/merged-fault-summary.md`.

The first fixture-under-chaos attempt is **failed/aborted**, not a pass.
In round 9, `paginated_scan_follows_partial_batches` unwrapped a raw setup
commit that returned `Transaction may or may not have committed`; no scan
assertion had run yet. Its setup now uses FDB's `on_error()` retry path for
each fixed-key/fixed-value batch, with a 60-attempt bound. Retrying these
writes is idempotent even when the first commit landed. All 2,000 keys,
400-byte values and page-size assertions remain unchanged. The failed logs
and safe interruption are retained under
`results/p2/faults-mp2-fdb-gate/fdb/fixtures/20261020T043454Z-2668337/`.
A fresh full 20-round fixture run follows the focused verification of this
test-only fix; production binaries are unchanged.

The second attempt completed all 20 rounds plus the fault and eight-case
property suites under 152 injected faults. It remains **FAIL**: 61/62 suite
results passed, but round 19's first valid tombstone call returned `false`
instead of the test's expected `true`. T8 returns that value only after reading
the exact tombstone and this writer's certificate, as happens when a committed
transaction loses its reply and resolves by idempotent retry. The test had
confused freshness with successful publication. The corrected tests retain
strict first-fresh expectations unless that operation records a real ambiguous
commit, and always check the exact durable effect and certificates. Repeat-false
and invalid-guard assertions remain strict. Real FDB errors interrupting a
simulated committed outcome now have a separate diagnostic counter; the
fence-order fixture retries a fresh scenario only for that recorded interruption,
with a ten-attempt bound and durable-state checks on interrupted attempts.
Its original ordering assertions must all pass on an uninterrupted attempt.
A fresh full chaos gate is required after these changes.

### Review corrections after the first merged fault phases

The chunk wrapper now admits at most 2,048 ordered references. The earlier
4,096 limit could produce a 151,554-byte `gchunks` value, exceeding FDB's
100,000-byte value limit. The new maximum is 75,778 bytes; a regression constructs
distinct IDs with maximum lengths and measures the actual index encoding.

A new network regression reproduced a marker-variant liveness bug:
after a lower receipt-only variant became canonical, certification failed with
`certificate names another marker`. T2, T8 and T10 deliberately bind the
immutable base marker, so their three caller paths now use `marker_base`.
The new regression checks certification, author deletion and tombstone relay
when both source and receiver select a lower variant. It failed before the
fix, and the complete network suite passed **15/15** afterward
(`results/p2/network-service/base-marker-before.log` and
`base-marker-full.log`). Transaction guards and canonical discovery selection
are unchanged.

The next Garage run also uses strengthened harness checks: read pre-loss bytes
through the replacement node, heal an issued RPC partition on harness exit,
and report a final failed-probe window as a censored sampled span without
inventing a recovery time. The SIGSEGV harness can now select the original
worker 3 and seed 3045 for a further bounded replay.

The post-review baseline passed **54 store checks** (16 library, 10 fault,
9 fixture, 13 guard and 6 tombstone checks), plus **9 wire checks**. The
production CLI, P3 controller and remote binaries rebuilt successfully;
their hashes are saved in `results/p2/merged-gates/binary-sha256-base-marker.txt`.
Shell syntax and recovered/censored/empty probe-summary cases also passed.

## Integration into main (branch `integrate-m-p2`, 2026-10-20)

`origin/m-p2=a7c19ed` was merged into `origin/main=2b3982d` (m-targets plus m-p5).
m-p5 had vendored m-p2's `ffbdb6e` snapshot, so every add/add conflict except
`writer.rs` was byte-identical on main to that snapshot and resolves to m-p2's
newer version. `writer.rs` takes m-p2's version (chunk index, 2,048-reference cap,
`marker_base` in T2/T8) and re-applies main's P3/P5 glue: the public
`Writer::signer()` and resolution of job dependency capsules to declaration IDs
passed to T1 (`dep_groups`, `replica`). `meta.rs` and `Cargo.lock` merged cleanly.

`TargetHomes` was already in `scripts/tla-common.sh` and the negative suite
(three witnesses and `target_no_home`). The archive failed `--verify` only because
the negative and hardened logs predated the new TLA sources. All four suites were
rerun with at most four TLC workers: default **21** positive, **85** negative cases,
**4** wide and **29** hardened cases. `archive-verification.sh --tla-only` then
`--verify` pass. TargetHomes: 133 distinct states; `target_no_home` violates
`TargetChain`.

Gates on private instances `int-a` (peer `int-b`), `int-ft` (six FDB, triple,
netsplit) and `p5-int`, with P1 and fork artifacts read-only from paralean-m-p4
`604dade` (`impl/p1` identical). Logs are in `results/p2/integrate-gates/`:

- `cargo test --workspace` (P2 store, ae-wire, network, proxies, multiprocess,
  P3 control and remote crates): **135 passed, 0 failed**, run twice
  (`workspace-run1.log`, `workspace-run2.log`). The first attempt was discarded
  because the instances' FDB and Garage processes were killed externally at 11:48;
  the instances were restarted with their data before the reruns.
- Anti-entropy network suite: **15/15** (`network.log`).
- P3 validator-api and control on `p5-int`: **38 passed**, including adversarial
  **13/13**; Mathlib throughput and measure tests remain ignored (`p3-control-all.log`).
- P3 remote gate through `impl/p2/scripts/remote-gate.py`: **all 15 checks pass**
  in 142.6 s (`p3-remote-gate.log`). A first run failed only its export check because
  the environment exported `PARALEAN_MATHLIB` for a nonexistent `.deps/mathlib-fork`;
  this core-only gate is run without it, as before.
- P5 unit tests **28/28**; P5 live gate with Claude workers on
  `list_reverse_map_lengths`: **ok** (10/10 contracts, recovery after desktop loss,
  dependency closure, stock export; 133 s wall) (`p5-gate.json`).
- Pagination under FDB faults, one fixture round (`FAULT_SCOPE=fdb`,
  `FIXTURE_ROUNDS=1`): **PASS**. Fixture 9 (both pagination tests), guard 13,
  tombstone 6, fault 10, property 1, with 15 injected faults; artifacts in
  `results/p2/faults-int-ft/fdb/fixtures/20261020T122741Z-3734578/`. The single fast
  round lasted 25 s, so only its first faults overlapped the pagination fixtures.

The m-p2 clone also held an uncommitted 20-round FDB fixture run
(`faults-mp2-fdb-gate/fdb/fixtures/20261020T053143Z-3746438`). Its events log ends in
`phase fixtures: PASS`, with 62 suite results and 131 faults. It is left uncommitted
as instructed and is not counted here.
Binary hashes: `results/p2/integrate-gates/binary-sha256.txt`.
