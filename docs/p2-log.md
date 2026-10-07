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
  then each group (marker, revisions, receipt, and the sender's certificates), then each
  tombstone (with its certificates). Raw markers and raw tombstones are never exported.
- **Verification at the receiver.** Every object is re-hashed against its ID. Every decoded
  object is checked against the IDs that name it: the marker names the revisions and the
  receipt; a certificate names the marker or the tombstone. Every certificate and receipt
  signature is verified under the receiver's key ring. The ring must list the peer's
  writers and validators (`KeyRing::trust`; the peer's fence authority is not trusted).
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
- Mutations, all 4 detected:
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
   (`ForeignTarget`). A name without a record there is received as an ordinary name, so a
   registry conflict between two owners becomes visible after the exchange. A sound rule
   ("each target name is homed at exactly one deployment") is not modelled.
3. *Catalogue records* (`catalog/`, `rcert/`, `ocert/`) are not exchanged. They are fenced
   by their own deployment's fence, so ranks of another fence mean nothing, and nothing in
   CatalogFencing lets one deployment commit for another.
4. *Trust.* The key rings must already list the peer's writers and validators. Distributing
   them is out of band and not modelled.

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
      author and the same workspace, has no target name, and a named receipt exists.
  - T9, receive group: writes `marker/<g>` if absent (aborts on another marker), revisions
    and receipt if absent, `cert/<g>/<self>` and `xcert/` evidence. It aborts on a name held
    as a target here, or on a missing parent revision.
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

- Receipt binding (P3); buildability beyond the build-receipt verdict (unchanged from `p2`).
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
