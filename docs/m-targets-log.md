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
  and timeout discard the process. Materialized initializer jobs use the cold
  path. The checker version hashes both checker executables.
- Batches contain at most 64 ordered envelopes. Every job gets its own receipt;
  an earlier accepted batch receipt can establish a later job's dependency,
  after rechecking its binding, cancellation, revocation and capsule identity.
  Payloads are still rehashed and normal publication still uses T1.
- Minimal P2 store change: expose the existing writer signer through a read-only
  accessor so worker RPCs can authenticate with their existing workspace key.
  Store internals and anti-entropy remain under m-p2 ownership.

The warm checker's isolation claim concerns Lean environments. It is not an OS
sandbox for arbitrary metaprograms or their external side effects, which the
existing cold checker also does not sandbox.

## Verification and measurements

The fork warm checker built successfully. Focused live tests passed:
authentication/replay (2), multi-target publication/handover (2), ordered
dependent batches (1), warm isolation/replacement (1), leader death between T4
and the dispatch reply with a different replacement worker (1), and existing
control tests (6). The warm test checks a rejected target contract followed by
successful checks in the same process, refusal of an unpublished dependency
despite prior checking, and timeout followed by process replacement.

Fresh captures of all 18 modules produced 1,105 groups in 97.23 seconds. Full
validator measurements and the working-copy gate are running. Final verification
will rerun against the integrated revision, including the latest FDB chunking and
receipt fencing changes.

## Sentences for plan.md and README.md

Pending final verified results; neither file is edited by this workstream.
