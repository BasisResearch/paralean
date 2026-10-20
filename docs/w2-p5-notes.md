# W2 P5 security audit (2026-10-20)

Scope: `impl/p5` controller, workers, journal, workspace sources, cache metadata and export checkpoint. This pass made no P2/P3 store or protocol-model changes. The controller and coding workers still share a Unix account; the deployment does not claim an OS boundary against a worker that can read arbitrary files owned by that account.

## Findings and fixes

- **High: source symlink traversal.** A worker could replace a frozen source with a symlink. P5's journal capture, provisioning and export reads used `Path.exists/read_text/write_text`, which follow symlinks and could read or overwrite a file outside `work/`. Source paths now have canonical components and descriptor-relative `O_NOFOLLOW` opens for each directory and file. Nonregular files are rejected. The initial provision write uses `O_EXCL`.
- **High: administration credentials in runtime children.** P5 removed the recovery secret from Lean, workspace and validator subprocesses but still passed Garage's admin token and RPC secret. These children handle worker-controlled material. A shared runtime environment filter now removes all three controller-only values from bridge, Lean, workspace, validator and store-discovery children. S3 client credentials remain required for remote fetches and are excluded from backend failure logs.
- **Medium: restored key path and stale key.** Recovery followed a dangling symlink when writing a decrypted key, and accepted a preexisting local key without comparing it to the authenticated journal. It now installs complete key files through an exclusive hard link from a private staged file, rejects symlinks, and compares existing bytes with the authenticated plaintext.
- **Medium: explicit export head mismatch.** `Controller.export` checked that target heads validated, but did not compare their groups with the journal's completed groups. A reassigned and republished target could produce an export checkpoint inconsistent with the recorded run. It now checks all recorded groups before and after export.
- **Medium: workspace cache file selection.** P5 used capsule IDs from worker-writable marker JSON to construct filesystem paths and followed symlinked cache files. It now requires 64-character lowercase hex IDs and uses the secure reader for marker/capsule files. Snapshot marker file names are checked before checkpoint submission.

## Verification

`python3 -m unittest discover -s impl/p5/tests -p 'test_*.py' -q` passed: 37 tests, 2 skipped. `git diff --check` passed. The skipped tests were already environment-gated live checks; this audit did not run a live store/validator gate.

`python3 impl/p5/tests/check_security_mutations.py` reruns the copied-source baseline and five guard-removal mutations in a temporary P5 source tree. It never edits the shared source. Each mutated suite exits 1 with its named regression failing; the full logs and machine-readable summary are under `results/w2/p5-security-mutation-logs/` and `results/w2/p5-security-mutations.json`.

| Mutation | Failing regression |
| --- | --- |
| Remove `O_NOFOLLOW` from source walk/open | source capture and restore symlink tests |
| Remove local-key plaintext comparison | stale local key test |
| Remove pre-export head check | replaced valid head test |
| Return unfiltered runtime environment | controller secret child environment test |
| Remove snapshot file validation | unsafe snapshot file test |

The source and cache checks protect P5's own reads and writes from paths controlled by a coding worker. They do not turn a shared Unix account into a process sandbox. The existing live P5 gate should be rerun on this branch before claiming integrated deployment behavior.

## P1 receipt consumer alignment

`impl/p1/Paralean/P3.lean` had four mismatches with the Rust receipt gate. The PCE unsigned varint parser accepted nonminimal encodings and had unbounded recursion; it now uses at most ten bytes, checks u64 overflow and rejects a redundant final zero. Target-bearing jobs now require an authority signature, and the receipt's target slot must equal the exact encoded job binding set, including names, epochs and statement hashes. The receipt cache also rechecks that the parsed job's ID equals the receipt's requested ID before returning a cached admission. `Remote.lean` no longer suggests a later cancellation retroactively invalidates an already published group; Rust's T1 blocks cancelled jobs before publication.

`python3 impl/p1/tests/p3_security.py` passed. It builds `Paralean.P3` and runs a Lean fixture using real Ed25519-signed PCE job and receipt bytes. It rejects malformed varints, an issuer-signed target job, a genuine but mismatched target receipt, a replaced job file after a successful cached admission, and a weak-key signature. `python3 impl/p1/tests/check_security_mutations.py` compiled six mutant oleans in temporary source trees, linked the unmodified dependency oleans without copying the build cache, and required a named Lean assertion failure for each mutation. All six passed this negative check. Full logs and summary are under `results/w2/p1-security-mutation-logs/` and `results/w2/p1-security-mutations.json`. The existing `Paralean.Encode` deprecation warning appeared during builds.

## Remaining isolation boundary

P5's ordinary CLI workers still run under the controller's Unix account. Codex's workspace-write mode does not confine reads, and the custom command adapter has no process sandbox. Workers need S3/FDB client access for remote helpers; an arbitrary same-UID process can also inspect controller files outside the coding workspace. The P3 validator checker uses a separate `bwrap` sandbox with no network, but that launch profile cannot directly serve networked coding CLIs. A secure worker profile needs narrowly mounted CLI authentication/configuration, compiler and P2/P3 tools, workspace and cluster access, without exposing the P5 desktop. This was not implemented or represented as a closed boundary in this pass.

Disposable reproduction: `python3 impl/p5/tests/reproduce_worker_isolation.py` printed `worker_exit=0 read_outside_workspace=True`. It uses a synthetic sentinel outside the worker directory and no deployment credentials. This demonstrates the custom command adapter's filesystem reach without accessing any real secret. The broader trust issue also includes raw client access: a worker that legitimately has S3 and FDB access can bypass trusted Rust client guards to mutate unauthenticated FDB protocol keys, even if journal HMAC prevents forging an accepted task payload. An isolated worker with a brokered, authenticated store API is needed for a hostile-worker claim; mounting only the desktop out of view would protect local key files but would not close raw store access.

## Validator result provenance: defensive review only

`Paralean.Validate.checkGroup` calls `sourceReplay` and then `kernelReplay` in the same Lean process (`impl/p1/Paralean/Validate.lean:129-132`). Source replay renders stored capsules and passes each to `replayCapsule` (`impl/p1/Paralean/Replay.lean:63-75`), so that process executes frontend code originating in a package being checked. `Main.lean:326-328` prints its verdict as a `CHECK` line on stdout. The cold validator reads the last stdout line with that prefix, parses it as a `Raw` verdict and requires a successful process exit for acceptance (`impl/p3/crates/control/src/checker.rs:477-485`). The warm transport runs `checkGroup` inside a persistent process and prints a nonce-bearing `WARM` line (`impl/p3/lean/WarmMain.lean:45-63`); the nonce is delivered to that same process in the request. The validator's recent output byte cap and OS sandbox constrain resources and outside access but do not establish that a verdict frame was produced by trusted code within that process.

The architectural repair is a process boundary between package execution and verdict authority. A disposable, restricted frontend can replay source and produce evidence needed for identity comparison. A separate trusted process must load pinned imports and content-addressed term bytes, perform kernel insertion and axiom/target checks without evaluating the capsule source or its native code, and issue the authoritative result over a channel unavailable to the frontend. Its input must be independently checked: merely forwarding a success flag, name map or declaration summary from the frontend would preserve the same trust problem. Initializer materialization and warm checking need the same boundary. A stdout marker, random nonce visible to the executing process, or a shell-level output filter alone does not supply provenance.

This workstream did not construct or run a spoofing package, demonstrate validator acceptance of a forged result, or change the checker protocol. The review establishes a code-level trust-boundary concern; exploitability and a complete split-checker design remain unverified.
