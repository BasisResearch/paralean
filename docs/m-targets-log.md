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
Rust builds use two jobs and integration tests one test thread. Existing pinned
toolchain and Mathlib builds and captured fixtures are read-only inputs; P1 and
Rust build caches were copied into this checkout before modification.

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
  of every dependency, including through the adversarial writer entry point.
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
cluster. Results so far: control/adversarial/auth/target/durable/protocol tests
29/29; process failure tests 3/3; P2 store tests 44/44. The batch test additionally
checks that a byte-distinct capsule for one group does not displace the receipt
for the original dependency capsule. Both normal publication and the adversarial
writer entry point reject a dependent before its prerequisites publish.

The full remote gate passed 15/15 in 220.5 seconds. After the final controller
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

Final warm-isolation results and Mathlib measurements follow after completion.

## Operational limits and remaining work

- Controller state is bounded at 8 MiB per snapshot. History and immutable snapshot
  chunks are retained; an unbounded deployment needs sharding and garbage
  collection. The cap fails closed. Lease timing uses wall clocks; clock skew
  affects takeover timing, while FDB term/holder conflict reads fence stale writes.
- Environment isolation is checked, not arbitrary native/metaprogram process
  sandboxing. Materialized initializers run in disposable processes. There is no
  claim that untrusted code with arbitrary process-memory access is contained.
- The benchmark uses one validator slot, dependent batches of 32, and a shared
  host. Its wall times include validation fetch/replay and RPC, but exclude capture,
  initial payload upload, and T1 publication, which are recorded separately. Dollar
  charges cannot be attributed without a machine rate and an allocation of shared
  FDB/Garage costs; validator-hours and observed checker RSS are reported instead.

## Reproduction

Use `PARALEAN_LEAN=fork`, source `impl/p3/scripts/m-targets-env.sh`, start
`impl/p3/scripts/cluster-up.sh`, and build `impl/p3/scripts/build-warm.sh`. Set
`PARALEAN_P3_WARM_BIN` to `impl/p3/lean/.lake/build/bin/paralean-warm` **before**
generating checker pins. Capture inputs with
`impl/p3/scripts/capture-mathlib.py .runs/m-targets/mathlib`; it verifies the
Mathlib commit from `versions.json` and reads the pinned Mathlib build.

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
