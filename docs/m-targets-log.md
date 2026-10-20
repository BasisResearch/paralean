# Targets and controller hardening workstream

Branch `m-targets`, starting at `7df9ace`. The requested `gpt-6.1-sol`
subagent model was unavailable; the user selected `gpt-6-sol`. Separate agents
implemented working-copy targets and controller persistence/authentication, and
wrote independent tests. The parent agent implemented warm validation/batching,
reviewed integration, and ran verification.

## Instance and resource limits

This work uses its own FoundationDB on `127.0.0.1:5189`, Garage on
`18939–18941`, and the S3 guard on `18933`. Data, credentials, logs and PID files
are under `/data/home/kirancodes/paralean-m-targets-cluster`. Source
`impl/p3/scripts/m-targets-env.sh` before starting `cluster-up.sh` or testing.
No other instance is stopped or modified. Initial `/data` free space: 273 GB.
Rust builds use at most two jobs and integration tests one test thread. The
private Mathlib base build started with two Lean threads and resumed with four;
validator jobs use two Lean threads. Existing pinned
toolchain and Mathlib builds and captured fixtures are read-only inputs; P1 and
Rust build caches were copied into this checkout before modification.

During the first measurement on fork `99967f1`, an initializer's nested Lake build
rebuilt dependency artifacts in the shared Mathlib cache despite the intended
read-only use. Observed commands included `Batteries.Tactic.Lint.Simp` and
`ImportGraph.Tools.FindHome`. The run was stopped and its timings discarded;
no service instance or tracked source was changed, and no shared cache was
restored over possible concurrent work. Subsequent materialization uses a
private, dereferenced copy of Mathlib and its package caches under
`.runs/m-targets/mathlib-private` (no hardlinks), with its sample import closure
prebuilt before capture. This incident is an exception to the read-only-input
intent above, not an assertion that the shared cache remained untouched.

## Implementation checkpoint

- Working copies discover target records, check ownership before asking the
  controller for a signed target job, and retain the preparation's epochs and
  heads through T1. The gate includes a two-name group, handover with a pending
  proof, rejection of the stale owner, and a subsequent revision of a recorded
  nonempty head. Controller `AssignGroup` changes all names atomically.
- Control RPC transport uses Ed25519 signatures over a server-generated random
  challenge, request, and response, with distinct signature domains. Worker
  operations bind the verified key to the claimed workspace. Administrative
  operations require the authority key. Validator calls authenticate the
  authority or the job's issuer key. Replaying an exchange against a fresh
  challenge fails.
- Controller queues, workers, leases, assignment intents, group associations and
  recovery cursor are persisted in FoundationDB. Snapshot chunks (60 KiB each,
  at most 8 MiB total) and their hash-checked head pointer commit under the
  controller lease. Assignment reads the same lease transactionally. Dispatch
  records the chosen worker before assigning a target, then recovers that intent
  after a crash. Group handovers are atomic and worker expiry fences all linked
  names together. Receipt writes are fenced by the controller lease.
- A persistent Lean checker executable lives in `impl/p3/lean`. It reuses P1's
  immutable imported-base cache, while each job builds a fresh catalogue,
  frontend session, command state, kernel environment, and axiom cache. A
  validator owns a bounded pool; failed transport, cancellation, memory excess,
  and timeout discard the process. Materialized initializer jobs use disposable
  processes with the same nonce-bound transport. Each response must echo a fresh
  random request nonce; unrelated or replayed stdout frames are ignored. The
  checker version hashes both checker executables.
- Batches contain at most 64 ordered envelopes. Every job gets its own receipt;
  an earlier accepted batch receipt can establish a later job's dependency,
  after rechecking its binding, cancellation, revocation and capsule identity.
  Payloads are still rehashed. T1 now independently requires certified publication
  of every envelope-listed dependency, including through the adversarial writer entry point.
  The validator checks completeness against the captured dependency closure.
  Accepted batch receipts therefore cannot publish a dependent before its prerequisites.
- Minimal P2 store changes: expose the existing writer signer through a read-only
  accessor for authenticated worker RPCs, and enforce dependency publication in T1.
  The writer resolves hash-verified dependency capsule JSON `declId` fields into
  group IDs; T1 reads their markers and signed certificates in its transaction.
  This matches the existing P3/P1 capsule contract and fails closed for opaque
  dependency capsules without a declaration ID. No anti-entropy code is changed.

The warm checker's isolation claim concerns Lean environments. It is not an OS
sandbox for arbitrary metaprograms or their external side effects, which the
existing cold checker also does not sandbox.

## Verification

The parent ran the integrated Rust build and live tests against the isolated
cluster. Results: control/adversarial/auth/target/durable/protocol tests 30/30;
process failure tests 4/4; batch and warm isolation tests 3/3; fork-validator
test 1/1; P2 store tests 59/59. These are 38 distinct control tests and 59 store tests after rebasing onto cb1ca05.
The warm test was run separately with its required fork fixtures; a stock-only
batch test invocation reports it as passed after an early configuration return,
which is not counted as isolation evidence. The batch test additionally
checks that a byte-distinct capsule for one group does not displace the receipt
for the original dependency capsule. Both normal publication and the adversarial
writer entry point reject a dependent before its prerequisites publish.

The rebased full remote gate passed 15/15 in 224.8 seconds, including all
five target checks with the P4 proof-loading path. Its report is
`m-targets-remote-gate-rebased.json`. The earlier full gate passed 15/15 in 220.5 seconds. After the final controller
and T1 changes, the target-only gate passed 5/5 in 33.3 seconds. Both JSON reports
are in `impl/p3/results/`. The full gate verifies its baseline export before
introducing the target fixtures; target proof consumption is checked separately
in both working copies with no errors or placeholder axioms.

The process tests kill real OS processes. One kills the elected controller after
T4 but before the reply, then recovers the durable assignment on its standby.
Another kills it after J1 while the validator is running: the standby writes J2
without a client retry and the validator reports one check. A third kills a
worker and observes a replacement publish. This establishes logical request and
publication deduplication for those crash windows; work can be re-executed after
a worker lease expires, rather than promising exactly-once physical computation.

The final warm binary built and its isolation test passed. It checks a rejected
contract followed by two successful checks of the same declaration, refuses an
unpublished dependency despite having checked it earlier, replays F11 scoped
notation then returns to F01 without growing the process count, and replaces the
process after timeout. `checkGroup` constructs a fresh catalogue; `openSession`
constructs fresh command state/options from an immutable imported environment;
`kernelReplay` starts from that base with a fresh kernel environment and axiom
cache. Only imported-base environments are intentionally cached between jobs.

The paired M14 sample on implementation commit `bd081a4` accepted and published
all 50 groups in each mode. Warm validation took **17.082 s (0.342 s/group)**;
cold validation took **44.659 s (0.893 s/group)**: **2.61×** the validation
throughput, or **61.75% fewer validation RPC seconds** for this sample. Measured
module work including upload, publication and audit took 25.655 s warm versus
53.574 s cold. Both runs used ordered batches of 32 and the new T1 dependency
guard. This is one sequential paired sample on a shared host, not a controlled
performance distribution. Cold-path RSS was not instrumented; its JSON zero
means unavailable, not zero memory. Raw reports are in `impl/p3/results/`.

The initial full run attempted all 1,105 groups from the 18-module sample: 1,104
were accepted and published, one was rejected. It used 1,745.646 validation
seconds (1.580 s/group), before the final nonce, initializer-process and T1
dependency-publication changes. Its raw report is retained as
`m-targets-mathlib-18-initial.json`. A rerun is pending on the rebased implementation and the updated fork pin;
it uses two disjoint shards, each with one validator slot.

## Additional crash and concurrency review

A final full-sample rerun exposed a race between recovery of durable J1 jobs and
an ordered batch using the same validator request ID. The standalone recovery
request could refuse an unpublished dependency while the batch already held
that dependency's accepted receipt. The batch inherited the refusal. The fix
reacquires the normal validation slot with the batch's dependency context,
preserving cancellation and deduplication. A deterministic regression fails on
`bd081a4` with the same dependency refusal and passes with the fix. The partial
run with three such M01 refusals was stopped and is not the final measurement.

Review also found that lease-expiry reassignment could commit T4 before saving
its chosen replacement. If the controller then crashed and that replacement
expired, recovery could retry an immutable assignment request with a different
owner and strand the job. Expiry now persists an owner/attempt intent before T4,
including handovers to the unowned sentinel, and resumes unfinished intents.
A process regression kills the leader in that window, lets the replacement
expire, and requires the standby to fence it and deliver the original job to a
third worker. It fails on the previous implementation (with only the pause
failpoint added) and passes with the fix. The complete four-process-test suite,
control scheduling tests, durable snapshot test, and target tests also pass.

Review additionally found that a singleton group could be reassigned through
legacy APIs without updating its stored group owner. Expiry could then fence
the new live owner. Group-associated targets now require the group workflow;
queued/running work blocks both legacy and group assignment. The regression
checks every overlap direction before target mutation and checks that expiry
of a separate group owner leaves a live work target unchanged. The final affected
suite passed 16/16 (six scheduling, one durability, four process, five target);
the final target-only working-copy gate passed 5/5 in 21.3 seconds.

## Operational limits and remaining work

- Controller state is bounded at 8 MiB per snapshot. History and immutable snapshot
  chunks are retained; an unbounded deployment needs sharding and garbage
  collection. The cap fails closed. Lease timing uses wall clocks; clock skew
  affects takeover timing, while FDB term/holder conflict reads fence stale writes.
- Environment isolation is checked, not arbitrary native/metaprogram process
  sandboxing. Materialized initializers run in disposable processes. There is no
  claim that untrusted code with arbitrary process-memory access is contained.
- Each benchmark module uses one validator slot and dependent batches of 32 on a
  shared host. The final full run uses two such modules concurrently. Its wall times include validation fetch/replay and RPC, but exclude capture,
  initial payload upload, and T1 publication, which are recorded separately. Preparing
  the private Mathlib base is a separate one-time setup cost. Dollar
  charges cannot be attributed without a machine rate and an allocation of shared
  FDB/Garage costs; validation RPC time, module wall time, and observed checker RSS
  are reported instead. Validation RPC seconds exclude time the validator remains
  allocated during upload, issuance, publication and audit, so they are not billed
  instance-hours.
- Full sample certification is blocked by the existing P1 source replay mismatch
  for M08 (`Mathlib/Tactic/ByCases.lean:37`), group
  `4cb846e8e10a561a786626acb401de0870008bb7e08a975539752eb086a795d4`
  on the rebased fork. Its generated macro name replays to declaration
  `b20f7eca3d55…` instead of stored `f5a1a2428cd2…`. A separate cold P1
  `check-group` reproduces the rejection (exit 1, 1.977 s); see
  `m-targets-cold-M08-rebased.log`. The older fork's reproduction is retained
  as `m-targets-cold-M08.log`. This work does not
  modify P1 source replay or bypass the rejection.

## Reproduction

Use `PARALEAN_LEAN=fork`, source `impl/p3/scripts/m-targets-env.sh`, start
`impl/p3/scripts/cluster-up.sh`, and build `impl/p3/scripts/build-warm.sh`. Set
`PARALEAN_P3_WARM_BIN` to `impl/p3/lean/.lake/build/bin/paralean-warm` **before**
generating checker pins. Before materializing initializer jobs, make a private copy
of the Mathlib checkout **including** `.lake/packages` and build caches (dereference
symlinks; do not hardlink files). Set `PARALEAN_MATHLIB` to that copy and prebuild
the 18 module targets from `corpus/modules.txt` with the selected fork. Check
freshness under `LEAN_PARALEAN=1`, which P1's initializer export uses. Capture
inputs with `impl/p3/scripts/capture-mathlib.py .runs/m-targets/mathlib`; it
verifies the Mathlib commit from `versions.json`. Keep that private base fixed
through capture and measurement: initializer export invokes Lake and may rebuild
stale dependencies, so pointing it at another workstream's cache is unsafe.

Set `LEAN_PATH` from `lake env printenv LEAN_PATH` in `$PARALEAN_MATHLIB`,
`PARALEAN_P3_MATHLIB_STORES` to the capture directory, and
`PARALEAN_P3_THROUGHPUT_REPORT` to an output JSON path. Run:

```sh
cargo test --release --manifest-path impl/p2/Cargo.toml \
  -p paralean-control --test mathlib_throughput \
  -- --ignored --nocapture --test-threads=1
```

`PARALEAN_P3_MEASURE_MODULES=M14` selects a paired sample. For the cold leg,
unset `PARALEAN_P3_WARM_BIN` and set `PARALEAN_P3_MEASURE_COLD=1`. Use distinct
report paths. Stock control fixtures require the stock P1 checker; fork tests
use `PARALEAN_P3_FORK_BIN`, `PARALEAN_P3_FORK_PREFIX`, and
`PARALEAN_P3_FORK_STORE`. The fork store used here contains F01Theorem,
F04Inductive, and F11ScopedDecl captured with the pinned fork.

For the working-copy gate, retain this cluster's environment and set
`PARALEAN_PLR` and `PARALEAN_P3_BIN` to this checkout's release executables;
set unused `PARALEAN_VALIDATOR_PORT` and `PARALEAN_CONTROLLER_PORT`. Run
`impl/p3-remote/scripts/gate.py RUNDIR`, optionally with `--targets-only`.
Worker/controller clients accept comma-separated controller addresses.

## Integration notes

At the user's request, the branch was rebased onto `origin/main` at `cb1ca05`,
which includes P2 anti-entropy/tombstones and P4. The rebase required one minimal
P2 adjustment: remove the duplicate crate-private `Writer::signer` accessor and
retain the public accessor used by authenticated RPC clients. No upstream
anti-entropy implementation was changed. The incoming fork pin is
`99967f1ee50a1ee82bb178359ad95b723c8196a2`; P1 and the warm checker were rebuilt
in this checkout against that pin. The new warm checker ID is
`faf75494080ba4763461c8228e1861ade109d8a135e9c25762e515d741d2d8f0`.
An initial capture used a read-only P4 P1 build with identical Lean sources.
The final capture used this checkout’s rebuilt P1 and private Mathlib base:
1,105 groups across all 18 modules in 49.558 seconds, with identical group IDs
to the initial capture. The private base prebuild took 1,001.455 seconds across
two invocations; this setup time is excluded from validation measurements.
Freshness under `LEAN_PARALEAN=1` passed all 2,354 build targets. Hashing 18,720
build files (1,269,868,112 bytes) before and after capture confirmed no changes. Earlier measurements explicitly retain their older
`dfc13cc6...` toolchain provenance.

The new dependency-publication guard applies to local T1. Incoming P2 T9
anti-entropy certification is a separate path and does not enforce this local
dependency publication order; changing T9 is outside this workstream. This log
does not claim the T1 guard as a new universal invariant of all replication paths.

P5 and other external callers must use authenticated RPCs with the workspace
signer for worker operations and the authority signer for administrative
operations. `call_controller` accepts a comma-separated replica list.
`WorkerNode` now sends `PollRequest` with a stable token across transport retries;
new clients should do the same. The legacy `Poll` variant remains available but
does not have a request token for replaying a lost response. Group assignment
request IDs are immutable bindings to a normalized name set and owner; a stale
request cannot restore an earlier owner, and subsets of an associated group
cannot be reassigned independently.

The small P2 change is deliberately limited to the writer signer accessor and
the T1 dependency-publication guard. Dependency capsules now need the P3/P1 JSON
`declId` field when listed in a publication envelope. No P2 anti-entropy internals,
P4 code, P5 code, plan.md, or README.md were changed.

## Sentences for plan.md and README.md

Proposed plan.md sentence: “M-targets adds target-aware working copies, atomic
multi-name handovers, FDB-persisted elected controllers with crash recovery,
Ed25519-authenticated control RPCs, and a bounded warm validator pool with
ordered dependent batches; verification and Mathlib measurements are recorded
in docs/m-targets-log.md.”

Proposed README.md sentence: “Target-aware copies publish controller-issued jobs
through the owner/epoch/head fences; see docs/m-targets-log.md for controller
failover, RPC authentication, warm-batch setup, measurements, and current limits.”

Neither plan.md nor README.md was edited.
