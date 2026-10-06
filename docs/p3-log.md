# P3 log: control plane (validators and the controller)

Branch `p3-control`, implementation in [impl/p3](../impl/p3/README.md). The receipt format
and staging rule are in the P2 store crate (`impl/p2/crates/store/src/receipt.rs`), so that
the publication transaction T1 can enforce them. All results below are from this agent's own
cluster instance on aws-dev: FoundationDB 7.3.79 on port 4989, Garage 2.4.1 on ports
18739–18741 behind `s3-guard` on 18733, data under `/data/home/kirancodes/paralean-p3-control-cluster`
(`impl/p3/scripts/cluster-up.sh`; P2's binaries are used read-only).

## What is implemented

- **Validators** (`paralean-p3 validator`, `crates/control/src/validator.rs`). A validator
  takes a controller-signed job envelope. It rebuilds a P1 store holding exactly the group
  and its dependency closure from the payload store, re-hashing every object. It refuses
  unless every dependency is published with a receipt that verifies now. It then runs
  `paralean check-group`, a new impl/p1 command: source replay must reproduce the
  declaration ID, the stock kernel replays every group of the closure, axioms are read from
  the kernel environment, and statement hashes are re-derived by the validator's own replay.
  It applies the envelope's policy and target contracts and signs an Ed25519 receipt
  (accepted or rejected) bound to the envelope.
  - **Failure handling.** Deadline, resident-memory limit, checker crash, cancellation and
    unavailable bytes give no receipt.
  - **Deduplication.** Requests are deduplicated by request ID.
  - **Backpressure.** Running and queued checks are bounded.
  - **Fork mode.** A validator runs the Paralean fork (impl/p1 built against `fork/`)
    instead of stock Lean by configuration. Its receipts name the fork's checker version.
- **Receipt binding** (OPEN-7, below). T1 re-checks the staging rule inside the publication
  transaction, together with these reads:
  - the validator-key revocation;
  - the request cancellation;
  - a new guard: a revision of a name that has a target record must be a prepared target.
- **Key rotation and revocation, minimal.**
  - The configured validator set may hold several keys. `keys add-validator` adds one, and
    the old keys stay trusted.
  - `keys retire-validator` removes a key from the configuration.
  - `keys revoke-validator` writes a signed `vrevoke/<key>` (R1). Every later T1 reads it,
    and a revoked validator refuses work.
  - Groups published before a revocation stay published. The audit lists them as suspect,
    and `published_receipt` (consumers) refuses them.
- **Controller** (`paralean-p3 controller`, `crates/control/src/controller.rs`).
  - **Target assignment.** A worker polling for work gets a job only if its free memory
    covers the job; the target is then assigned to it with T4.
  - **Leases.** Workers renew leases by heartbeat. On lease expiry each owned target is
    reassigned at once with T4, to another live worker with room or to a sentinel owner, so
    the epoch moves even while the dead owner might still run.
  - **Validation dispatch.** A `Validate` request becomes an envelope only for the target's
    current owner, stamped with the record's epoch.
  - **Retry deduplication.** It uses the request ID, an in-flight map and the write-once
    records `jobreq/` (J1) and `jobreceipt/` (J2).
  - **Cancellation.** It writes `jobcancel/` (J3), stops the dispatch and kills the
    validator's checker process.
  - **Backpressure.** Both queues are bounded and answer `Busy`.
  - **Failover between validators.** `Busy`, inconclusive results, timeouts, invalid
    receipts and per-validator refusals move on to the next validator.
- **Workers** (`crates/control/src/worker.rs`). A worker publishes a group's dependencies
  first, each with its own receipt. It stages only with a bound receipt and publishes with
  T1.
- **APIs** for the remote-imports work:
  - `paralean_store::receipt`: the format and `check`;
  - `paralean-validator-api`: wire types, the client and `published_receipt`.

  Both are in the branch since commit 3c0082a, and the remote-imports agent was told.

## OPEN-7 decision (receipt binding), and OPEN-11

The §6 receipt body keeps its shape, so `format` stays 0. P3 fixes the contents of three
reserved slots:

- **`validatorBin`** holds the ID of `CheckerVersion {leanGithash, checkerSha256, mode}`
  (domain `v0/checker`). That is the checker version.
- **`requestID`** holds the ID of the `JobEnvelope` the receipt answers (domain `v0/job`).
  It is required.
- **`targetID`** holds the PCE `set` of `TargetBinding {name, epoch, statement}`, or none
  when the job has no target.

The envelope is OPEN-11's decision. It is `{request, group, capsule, deps, base, policy,
checker, worker, targets, deadlineMs, memoryMb}`, signed by the controller with the fence
authority key.

**Staging rule** (`receipt::check`). A worker stages, and T1 publishes, group `g` only
with a receipt that:

1. verifies under a configured validator key;
2. is accepted;
3. names `g`;
4. comes with a controller-signed envelope whose ID is `requestID` and whose group, base,
   policy, checker and targets equal the receipt's;
5. names a pinned policy and checker (new `KeyRing.pins`, `KeyFile.policies/checkers`);
6. binds exactly the target names and epochs the publication was prepared under.

T1 additionally refuses when, in its own transaction:

- the validator key is revoked;
- the request is cancelled;
- a revision names a target that is not prepared.

So the receipt binds group, policy, checker version, request, epoch and target. A receipt
for an old epoch is useless after a reassignment, independently of the epoch fence on the
target record.

**What is deliberately not bound.** The publishing workspace is not bound. The envelope
names the requesting worker, but T1 does not require publisher = requester. Receipts are
statements about content (PUBLICATION-RECEIPTS "Trust boundary"), and for targets the
owner/epoch record already fences publication. Recorded in p0-interfaces §6, §10 and §13
(OPEN-7, OPEN-11 rows).

## Results (2026-10-06, live services)

**P3 tests:** `impl/p3/scripts/test.sh`, 20 tests, all pass.

Adversarial (`tests/adversarial.rs`, 12 tests). Each attack is refused both by the
worker-side staging check and by T1 alone (through `publish_skipping_staging_check`, test
feature `adversary`). Nothing is published, and the audit is clean.

| Attack | Refused with |
|---|---|
| Forged receipts: rogue key; trusted key named but wrong signer; body altered after signing; worker's own key; genuine receipt with an envelope re-signed by the worker | `ReceiptRejected`; `ReceiptBinding(JobNotIssued)` for the re-signed envelope |
| Receipt for another group | `ReceiptRejected` |
| Receipt for another policy, checker, base or target, or with no request (signed by a misbehaving validator holding a configured key) | `ReceiptBinding(Policy/Checker/Base/Target/Request)` |
| Unpinned policy: the controller records no receipt, and a validator asked directly signs, but nothing stages | `PolicyNotPinned` |
| Receipt for another epoch: the target is reassigned away and back, and the old-epoch receipt is used under the current epoch | `ReceiptBinding(Epoch)` |
| Prepared under the old epoch | `StaleEpoch` |
| Receipt for another request | `ReceiptBinding(Request)` |
| Request cancelled after its receipt was issued | `JobCancelled`; no new receipt for it either |
| Revoked validator key | `ValidatorRevoked`; the controller fails over to the other validator; the earlier group is listed as suspect; consumers refuse it |
| Retired key: a key ring without it | `ReceiptRejected` |
| Worker that skips validation: N1 `sorry`, N2 new axiom, N3 kernel-skipped ill-typed theorem and N6 `native_decide` each get a rejected receipt from the stock-kernel re-check | `ReceiptNotAccepted` when published anyway |
| N2.bad over an unpublished axiom group | validator refuses (dependency not receipted) |
| A good group's receipt reused for N3 | `ReceiptRejected` |
| Stale owner after lease expiry | target reassigned within one lease, epoch bumped; the stale owner's publication fails with `NotOwner`/`StaleEpoch`; re-reading the record fails with `NotOwner`; the controller refuses it a target job; a target-free receipt for the same group published without listing the target fails with `UndeclaredTarget`; the new owner publishes and is the head |
| Dependency not yet published | validator refuses |
| Strict policy (propext only) | `F06.fib_pos` (Classical.choice) rejected; `F02.classify_two` accepted |
| Pinned target statement changed | rejected |

The end-to-end test shows a target with three dependencies published through the controller,
two validators and a worker. All four receipts re-verify, and the target's binding names the
owner's epoch and the re-derived statement hash.

Operational (`tests/control.rs`, 6 tests):

- **Duplicates.** Four concurrent duplicates of one request gave one check and identical
  receipts. A retry after completion returned the recorded receipt with no check. A request
  ID reused for another group was refused. The validator deduplicates direct duplicates. A
  duplicate work submission answers `Duplicate`, and a re-publication is idempotent.
- **Timeouts.** With every validator hanging there is no receipt and nothing is recorded,
  and the checkers are killed. With one hanging and one working validator the receipt comes
  from the second.
- **Memory limit.** A 700 MiB checker under a 200 MiB limit is killed and gives no receipt.
  The real checker fits in 1 GiB.
- **Cancellation.** It stops a running check within the test's bounds and kills the checker.
  A cancelled request stays cancelled, and a cancelled work job is never handed out.
- **Backpressure.** The controller's validation queue, the validator's queue and the work
  queue all answer `Busy`, and record nothing.
- **Memory admission.** Jobs are handed out only within each worker's free memory, and
  memory is freed on `Finish`.

Processes (`tests/processes.rs`). Real `paralean-p3` processes ran: a controller, two
validators and two workers. A worker was SIGKILLed while holding the target job. Its lease
expired, the target was reassigned with a higher epoch, the other worker published the target
and its three dependencies, and the audit was clean.

Fork (`tests/fork.rs`). Validators running impl/p1 built against the fork (Lean `dfc13cc6`,
fork build from the `paralean-fork` clone, P1 copy built in `.runs/p1-fork-build`) checked and
signed a fork-captured F04 target with dependencies. They rejected N3. The receipts name the
fork checker version.

**Mutations:** `impl/p3/scripts/check-mutations.sh`, 13 of 13 detected. Each removes one
check, and the named test fails at the intended assertion (spot-checked: a forged receipt
publishes, a stale owner gets a receipt, a sneaked publication succeeds).

| Check removed | Detected by |
|---|---|
| T1's receipt check | `forged_receipts_fail_closed`, `worker_that_skips_validation_cannot_publish`, `receipt_for_another_group_policy_checker_base_or_target_fails_closed` |
| The epoch binding | `receipt_for_another_epoch_fails_closed` |
| The revocation read | `revoked_or_retired_validator_key_fails_closed` |
| The cancellation read | `receipt_for_another_or_cancelled_request_fails_closed` |
| The undeclared-target guard | `stale_owner_after_lease_expiry_cannot_publish` |
| The controller's owner check | `stale_owner_after_lease_expiry_cannot_publish` |
| Lease reassignment | `stale_owner_after_lease_expiry_cannot_publish`, `processes::killed_owner_is_replaced_and_the_target_published` |
| Request deduplication | `duplicate_and_retried_jobs_are_deduplicated` |
| The validator's dependency check | `dependency_must_be_published_with_a_receipt` |
| The validator's axiom policy | `validator_enforces_the_envelope_policy` |

These are the implementation counterparts of PUBLICATION-RECEIPTS' `unreceipted_staging` /
`unreceipted_publication` and TARGET-NAMES' `target_no_owner_check` /
`target_no_epoch_fence`.

**P2 regressions.** P2's suite (unit, guards, fixtures, faults, property, multiprocess) passes
with bound receipts in its fixtures. P2's `check-mutations.sh` still detects 11 of 11. Both
were run against this instance.

**P1.** `run-core.sh` gives the same replay, export and verify results after the
`check-group` changes.

**Costs** (`tests/measure.rs`, ignored by default). All 97 core fixture groups were
validated and published in dependency order through the controller and two stock validators:

| Measure | Value |
|---|---|
| Accepted | 95 groups (79 published, 16 share a group ID with an already published one: byte-identical declarations from different P1 packages, OPEN-23) |
| Rejected | 2: the F10/F13 initializer groups P1's isolated replay also fails |
| Check latency | p50 0.36 s, p95 0.77 s, max 1.25 s per group (whole closure re-checked; including upload and RPC) |
| Total time | 47 s |
| Payload | 326 kB |
| Mean closure | 1.9 groups |

## Findings

- **T1 did not guard every group declaring a target name** (fixed). T1 read target records
  only for the targets the publisher listed. A stale or non-owning worker could get a
  target-free receipt for a group declaring a target name and publish it without listing the
  target, bypassing the owner, epoch and head checks. TargetNames guards every group
  declaring a target name. T1 now reads `target/<name>` for every revision name. The
  regression is `stale_owner_after_lease_expiry_cannot_publish`, and the mutation is
  `mutate-no-undeclared-target`.
- **`RLIMIT_AS` cannot limit Lean.** A fixture check peaks at 0.5 GB resident, but Lean
  cannot create its threads under a 4 GB address-space limit. The memory limit is therefore
  a resident-set watchdog over the checker's process group. It is not a hard kernel limit: a
  burst between 50 ms samples can exceed it.
- **A fork validator rejects stock-captured groups with derived instances.** The fork names
  them canonically, so source replay does not reproduce the stock declaration ID. Capture and
  validation must use the same mode; the checker version in every receipt makes the mode
  explicit, and pins choose it.
- **The P1 core store has 16 groups whose group ID equals another's.** These are
  byte-identical declarations of different packages (OPEN-23). The second publication of a
  group ID is `AlreadyPublished`; workers treat that as done.

## Deviations

1. **The receipt format and staging rule live in the store crate**
   (`paralean_store::receipt`), not in impl/p3. T1 must enforce them, and the store crate
   cannot depend on impl/p3. The small separate crate is `paralean-validator-api` (wire
   types, client, consumer verification). Both P3 crates are members of impl/p2's cargo
   workspace, with `package.workspace` pointing there.
2. **The store crate gains P3 items.** These are:
   - the `Job`, `Policy`, `Checker` and `Revocation` domains;
   - five guard failures;
   - the `pins` field on `KeyRing` (and on `KeyFile`, with serde defaults);
   - the write-once transactions J1–J3 and R1 (`Meta::put_once`; `Txn::P3Job`);
   - an audit check of every published receipt;
   - six cargo features: five mutations and `adversary`.

   P2's fixtures now build bound receipts, signed by the demo authority key.
3. **The memory limit is a resident-set watchdog, not `RLIMIT_AS`** (finding above).
4. **Controller state is in memory, except validation records.** The work queue, worker
   registry and leases live in memory. Validation deduplication, receipts and cancellations
   are in FoundationDB. A controller restart loses queued work and leases, but not issued
   envelopes, receipts or target records. There is one controller and no failover.
5. **The base ID is `H("v0/base", PCE(string leanGithash))`.** It is not §2's full base
   manifest (no Mathlib pin); the fixtures use Lean core only.
6. **Every check rebuilds and re-checks the whole closure** from scratch. There is no cache
   of checked environments and no warm workers.
7. **The `Policy` object holds only the allowed axioms and the statement-check flag.**
   Forbidden options and the unsafe policy are left to P1's capture and the kernel re-check.
8. **RPC is plain TCP with no authentication.** Worker IDs in requests are claims. Safety
   does not depend on them: T1 checks the publisher's ownership and every signature. A
   client can still cancel or flood (denial of service only).
9. **Leases use the controller's local clock.** This affects liveness only; reassignment is
   safe at any time (TargetNames).
10. **The fork validator uses borrowed builds.** It uses the fork build of another clone
    (`paralean-fork/.deps`) and a P1 copy built in `.runs/p1-fork-build`; it does not run
    `fork/build.sh` here. `tests/fork.rs` skips when they are absent.
11. **p0-interfaces.md was edited.** §6's OPEN-7 bullet, §10's OPEN-11 sentence and their
    §13 rows record the decision. plan.md and README.md are not edited (sentences below).

## Not done

- **The P1 transparent-workspace HMAC receipts (`Paralean/Receipt.lean`) are not
  replaced.** `remote%` and its receipts belong to the P3 remote-imports work, which builds
  on `paralean_store::receipt`. The store's publication path has no HMAC.
- **Controller persistence and failover** are not done (deviation 4), and neither is RPC
  authentication (deviation 8).
- **Validators were not run at Mathlib scale.** Costs are measured on the core fixtures
  only.
- **Multi-target groups are untested end to end.** Envelopes and T1 handle binding sets,
  but no fixture group declares two target names.
- **Revocation is not retroactive.** Unpublishing would need deletion, which the grow-only
  store forbids. Suspect groups are reported, not removed.

## Sentences for plan.md and README.md

- plan.md P3, after "Add retry deduplication, cancellation, memory limits and queue
  backpressure.": "The control plane is implemented in `impl/p3` (Rust): Ed25519
  validators that re-check each group from its exact receipted closure with the stock
  kernel or the fork, receipts bound to a controller-signed job envelope (request), policy,
  checker version, target and epoch (OPEN-7, enforced inside T1 with revocation and
  cancellation), and a controller with T4 assignment, leases, deduplication, cancellation,
  memory admission and backpressure; adversarial tests and 13 mutations pass against the
  live P2 services ([p3-log](p3-log.md))."
- plan.md P3, replacing "its receipts are an HMAC under a shared key … The HMAC stands in
  for validator Ed25519 signatures (§6). P3 replaces both: real proofs and signed
  receipts.": "… its receipts are an HMAC under a shared key. Published groups now carry
  Ed25519 receipts checked by T1 (impl/p3); `remote%` still has to move to them and to
  real proofs."
- README.md, implementation status: "P3 control plane (`impl/p3`): validators, signed
  receipts bound to request, policy, checker, target and epoch, and the controller; see
  [impl/p3/README.md](impl/p3/README.md)."
