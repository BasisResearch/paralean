# W2 security and chaos log

Branch: `w2-security`. Starting base: `fee94d9be23d9e9902cb006b1e8cdfaa3bcf809c`.
`origin/main` was fetched and still matched that base on 2026-10-20.

## Scope and ownership

The primary agent reviewed P2/P3 transport, signatures, key handling, storage
ingress and verification. Three `gpt-6-sol` agents received disjoint assignments:
P2 chaos/SIGSEGV; P3 checker sandbox; P5/workspace/Lean receipt consumers.
Their detailed evidence is in `w2-chaos-notes.md`, `w2-sandbox-notes.md` and
`w2-p5-notes.md`. The primary agent reviews and integrates their changes.

Only private instances `w2-chaos` and `w2-audit` are operated. `w2-audit` uses
FDB 29600, gateway 29650 and a private Garage Unix socket. The chaos agent owns
its cluster on ports 29400–29450. Installed FDB/Garage binaries are read-only
inputs. P1 builds and fixture stores are private. `/data` initially had 244 GiB
available; checks during builds showed 201 GiB available. Heavy build and model
drivers use one worker/job each.

## Evidence corrections

The prompt's “61/62, round 15 pagination” does not match the retained evidence.
`docs/p2-log.md` and the retained 152-fault run identify round 19,
`t8_tombstone_guards`: a successful idempotent retry after an ambiguous commit
returned `false`, contradicting the fixture's first-write freshness assertion.
The earlier pagination failure was round 9 and occurred in setup before a scan
assertion. Both test corrections are already on the merged base; W2 must test
them rather than invent a new production pagination defect.

P3's original log calls RPC unauthenticated, but `m-targets` subsequently added
challenge-bound Ed25519 mutual authentication and durable controller fencing.
The audit uses current code, not that superseded limitation.

## Implementation and review

- Modeled operational connection/size admission and deletion reachability in
  `verification/tla/Ingress.tla`, wired into the positive and negative scripts.
  Initial focused run: 9 states, four named mutation counterexamples. Complete
  archive regeneration is required and recorded below when finished.
- Added pre-authentication RPC admission and handshake deadlines, outbound
  frame bounds, strict Ed25519 verification, private atomic key-file writes,
  redacted key/config debug output, PCE allocation budgets, and bounded S3 reads.
- Replaced cluster Garage S3 TCP listeners with private Unix sockets. A startup
  checker refuses public socket directories or a reachable legacy TCP backend.
  The gateway decodes query names before applying a write-operation allowlist,
  limits request bodies/connections/time, and omits credential-bearing URIs from
  refusal logs.
- The first live S3 regression caught an SDK compatibility error in the new
  allowlist: Rust's SDK sends `x-id=PutObject`. The list now permits this
  operation hint, with a positive regression; destructive subresources remain
  denied. No failed first run is counted as a pass.
- P5 fixes cover descriptor-relative source/cache reads, key restoration,
  runtime admin-secret filtering and matching export groups to recorded heads.
  Lean's receipt consumer now bounds/canonicalizes varints, checks exact target
  slots, requires authority signatures for target jobs, and rechecks cached
  envelope identity.

## Known open boundaries

The audit does **not** declare all high findings closed. Networked P5 workers
have raw store access and share the controller's Unix account. A synthetic
sentinel test demonstrates out-of-workspace reads. A brokered store interface
and a restricted worker execution environment are needed; hiding a few
environment variables is not that boundary.

Untrusted package execution and trusted kernel replay currently occur in the
same Lean process. The controller accepts that process's output as its
verdict. OS sandboxing protects the host but does not establish verdict
integrity inside that process. An automated subagent safety check blocked the
proposed adversarial reproduction; the follow-up was restricted to defensive
code review. No successful verdict-forgery experiment is claimed.

The checker sandbox's precise resource guarantees, tests and overhead are
recorded in the sandbox notes; memory/process limits must not be overstated.
An unreproduced historical SIGSEGV is not considered explained merely because
bounded replay passes.

## Handed off

- The proposed checker-verdict forgery reproduction was refused by an
  automated subagent review. It was skipped; only the defensive code review
  and architectural finding are retained. No exploit result is claimed.
- The sandbox agent's output-related mutation completion was also refused.
  It was stopped rather than retried. Its integration test is explicitly
  ignored with a handed-off reason, and no successful mutation verdict for
  that subtask is claimed. Ordinary resource configuration tests and
  legitimate Lean checks continue independently.

## Ed25519 checkpoint

The user's priority update requests committing signature hardening first.
Lean now rejects identity and other small-order public keys and signature
points. Rust's shared verifier uses `ed25519-dalek::verify_strict`; receipts,
job envelopes, certificates, revocations, fences and P3 RPC all call that
shared path. Anti-entropy's separate framed transport already used
`verify_strict`; W2 adds its own weak pinned-key regression and guard-removal
mutation. `P3Security` covers weak keys and genuine signed receipt fixtures.
`scripts/check-ed25519.sh` runs the two Rust paths and the isolated Lean
mutation suite. Remaining W2 work is intentionally a later checkpoint.

## Proposed plan.md and README.md sentences

“W2 hardens RPC admission, key-file handling, storage ingress, workspace paths
and Lean receipt consumers, and adds rootless validator process containment.
The threat model and remaining hostile-worker and checker-trust boundaries
are documented in docs/w2-security.md.”

## Verification in progress

Commands and final counts are appended after integration. Early local results:
store/control library tests 22/22; S3 gateway unit tests 3/3; eleven initial
security mutations detected. These predate the additional bounded S3 read and
sandbox changes and are not the final integrated verdict.

The first full TLC attempt accidentally used a newer local TLC jar. It was
stopped, the repository-pinned v1.7.4 jar (SHA-256
`936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88`) was
copied read-only from the existing installation, and complete suites restarted.
Only the pinned-toolchain rerun is eligible for the final archive.

Ed25519 checkpoint validation: both Rust verifier regressions passed and both
strict-to-relaxed mutations were detected; P3Security passed with genuine signed
fixtures and all six Lean guard mutations were detected. Full output is under
`results/w2/ed25519` and `results/w2/p1-security-mutation-logs`.

## Finish pass: salvage checkpoint (2026-10-21)

Reviewed all 17 worktree commits. Store worktree commits 33765e0, efb9eb8,
3a48635, 7e563a2, 71173e9, 308b4b8 and 1f0e77e are already integrated as
92236ff, 774e98f, 205c232, 107fe38, 86b13f5, 4e3c664 and 4de6210.
Control worktree commits f2076c7, 2ac3a0c, 40bcc53, 2218715, 0d6d493,
9e6dac8, 28ecac3 and 9d8f50f are already integrated as 42aeea0, 5ebcc35,
ef4c75c, 62543e5, dc3c77a, 7152ff5, 5ee85f9 and 8717b6a. Their nonidentical
patches preserve later statement-pinning, cancellation, sandbox and log-redaction
fixes. No implementation was dropped; replaying their older trees was unnecessary.

Salvaged the two genuinely missing chaos commits e73c13e and 6f5cfe3:
runtime-before-FDB teardown on return/unwind, opt-in crash reporting and capture,
exit smoke regression, and the explicit admission that the no-shutdown A/B arm
is not a detected mutation. Preserved all 100 untracked result files from the
chaos worktree, redacting any FDB connection credentials. No cores or keys were
among these untracked files. Stopped the two orphan worktree services (PIDs
337555 and 339061) and abandoned sandbox process 2031770 after inspection.
Other instances are untouched; new runs use only w2b-* instances.

The retained 61/62 failure is a tombstone freshness assertion after an ambiguous
commit, and the pagination failure is an ambiguous setup commit. Existing fixes
check durable effects and retry idempotent setup. The newly recovered evidence
includes a 150-round pagination run with seed 77003 and 428 faults, plus six-worker
stress and 12,000 faulted process exits without a reproduced crash. These are
historical results, not new verification of this integrated revision.

## Final summary (finish pass, 2026-10-28)

Instances: P2 `w2c-chaos` (six fdbservers, triple, netsplit; ports 31400–31450) and its
anti-entropy peer `w2c-peer` (31600–31650); P3 cluster `w2c-p3` (31500–31550, under
`~/paralean-p3-w2c`). No other instance or clone was touched. Disk was pruned first
(salvaged worktrees' and incremental cargo targets, about 25 GB); nothing cited was removed.

### 1. The previous manager's uncommitted work

Kept, committed at `4784f33`: the explicit `libtest-mimic` main for the five chaos suites,
the shutdown contract test and its mutation, the mutation-parser fix and the exit-race
strictness. Changed: the same main for the three other FDB suites (and later for every
FDB suite of P2 and P3); `deny(dead_code)` so a test left out of a list cannot compile;
the property suite reads its existing regression seeds instead of a new file. Dropped
from the commit: test-deployment `keys.json` files (private seeds) and the 48 MB crashed
binary (its SHA-256 is kept).

### 2. Chaos failure and SIGSEGV root causes

- **SIGSEGV: root-caused with stacks.** A process leaving `main` with FDB's network
  thread still running races libfdb_c's own exit-time destructors. glibc runs
  `__cxa_finalize` for libfdb_c, which frees the client's globals while
  `fdb_run_network` still uses them. `examples/exit_race.rs` reproduces it without
  faults in about 1% of exits right after a `Database` is dropped (27/3000). The
  controls are all 0/1000: leaking the database, exiting with requests in flight, a
  20 ms gap, and the stop-and-join fix. Every captured core shows the same two-thread
  stack. This is the `seed-77003` fixture crash after `test result: ok`, and the exit
  shape of the pre-`667dcf6` stress worker (no core of that process exists). It is also
  why 12,000 later CLI exits did not crash: the CLI drops its runtime first. Details are
  in `w2-chaos-notes.md`.
- **61/62: not a pagination bug.** The retained failure is round 19,
  `t8_tombstone_guards`, a freshness assertion after an ambiguous commit. The round-9
  pagination failure was an ambiguous setup commit. Both test bugs were fixed earlier.
- **Fix: W2-48.** Every FDB test suite stops FDB before exit, and `paralean-p3`, `plr`
  and the P5 bridge use `meta::run_main`.
- **Chaos on the final merged code:** seeds 22021, 77003, 99173 and 4242 gave **108/108**
  suite summaries under **117** injected FDB faults, with no signalled process.

### 3. Merge of origin/main `a5dfc5c` (merge commit `fd20d4e`)

There were 19 source conflicts, plus generated logs that were regenerated rather than
hand-merged. Both sides' semantics are kept. Where they collided, W2's limits now hold
on W3/W4/W5 code:
- W2-42: W4's validation routes are scoped per workspace.
- W2-43: over-cap snapshot entries spill into W4 replay rows.
- W2-44: the request-ID bound runs before shard routing.
- W2-45: imports use the per-path import verifier.
- W2-41: the controller runs W4's GC by default.

The required mutation cases:
- **W3 agent-key registry:** grant, revocation and controller deletion grant, one path
  mutation each (W2-46).
- **W4 sharded controller RPCs:** a live two-shard strict-vector test (W2-47), plus the
  scoping, routing-bound and spill cases above.
- **W5 LSP publication:** a subagent audit, reviewed here, found and fixed W2-49 to
  W2-53, one High. It adds 13 editor-bridge mutants and repairs a broken one.

Re-verification found three more problems, all fixed:
- W2-54: a W3 import bug, also present on origin/main.
- W2-55: the sandbox root tmpfs was writable.
- Several W2/W4 tests and scripts were invalidated by the merge: role key files, the W4
  index, the 256-byte bound, verdict formats, the peer Garage socket, and a P5 mutation
  copy.

### 4. Re-verification (final tree)

| Suite | Result |
| --- | --- |
| Veil `check-veil.sh` | 34 modules; axiom audit 7,359 declarations, stock axioms only |
| TLC (pinned v1.7.4) | 35 positive, 193 negative/expected-outcome, 4 wide, 29 hardened; `archive-verification.sh --verify` passes |
| P2 workspace (`w2c-chaos`, peer `w2c-peer`) | 163 passed, 0 failed |
| P2 guard mutations `check-mutations.sh` | 49/49 detected; W2-54's `mutate-author-cert-error` detected |
| W2 security mutations `check-w2-security.sh` | 36/36 detected |
| Ed25519 paths `check-ed25519.sh` | 12/12 Rust path mutations; Lean 24/24 security mutations |
| s3-guard mutations | 4/4 |
| FDB shutdown contract | pass; `mutate-no-network-shutdown` killed |
| P3 tests (`impl/p3/scripts/test.sh`) | 113 passed, 0 failed, 4 ignored (live benchmarks; the fork test skips without a fork build) |
| P3 mutations `check-mutations.sh` | 39 cases. In the full run, 38 were detected and `mutate-no-checker-cgroup` survived: at load ~45 the RSS poll stopped every burst. The test now requires a cgroup kill (`NoVerdict::Memory { cgroup }`). After that change: baseline 5/5, mutant detected 3/3, rerun on the final tree also detected; `mutate-writable-sandbox-root` (W2-55) detected |
| W4 controller / GC / history mutations | 10/10, 6/6, 15/15 |
| P3-remote gate (`remote-gate.py`, stock Lean, `w2c-chaos`) | 14/15 PASS. The failing check is "clean export of a copy": its stock build needs a Mathlib checkout at `.deps/mathlib`, which this clone lacks (`ws-export` reports `mathlib: package directory not found`). This is environmental, not a code result |
| P5 unit tests | 91 passed, 2 environment-gated skips |
| P5 editor-bridge mutants / security mutations / revoke guard | 46/46 / 15/15 / killed |
| P4 rename unit / mutants | 25 passed / 18 killed |
| W2 adversarial and isolation | P3 `adversarial` 15/15 and `sandbox` 13/13 inside the P3 run; Lean `lean_security.py` pass |

### Not done

- **P1 G1–G6:** not run.
- **The gate's clean-export check:** needs a local Mathlib checkout (`.deps/mathlib`).
- **The live P5 integrated gate:** not run. It needs model-driven workers and an SSH LSP
  worker.
- **Fork-mode checks:** not run. This clone has no Paralean fork build, and using
  another clone's build was out of bounds.
- **W2-12 and W2-13 remain OPEN** (hostile P5 workers with raw store access; package code
  in the checker's verdict process).
- **Original stress-worker crash:** explained by its exit shape and the reproduced
  mechanism, but not by its own core, which never existed.

Final tree: `59a0346` (pushed as `w2-security`); this line is added in the following commit.

## Addendum: residual issues (2026-10-28)

- **W2-13 fixed.** The validator splits each check. `source-check` contributes only
  evidence; `kernel-check`, a fresh sandboxed process that elaborates no capsule, gives
  the verdict (`Paralean/KernelCheck.lean`, `checker.rs`).
  - On the 97 core fixtures it agrees with the old checker. With forged evidence it still
    rejects every negative fixture.
  - P3 tests: 114 passed, 0 failed, 4 ignored.
  - `forged_frontend_acceptance_cannot_pass_the_kernel_check` passes, and
    `mutate-verdict-from-frontend` is detected.
  - Cost: about 0.6–0.8 s more per check. Because agents are trusted, the split is
    opt-in (`PARALEAN_CHECKER_SPLIT=on`) and off by default; the default path is the
    single `check-group` process as before.
- **W2-12 accepted, not fixed.** P5's coding agents are trusted in the operating mode, so
  hostile workers are outside the threat model. No worker sandbox was added.
- **Smaller residuals fixed:**
  - `ws.py` stages its receipt and plan privately (W2-20).
  - The S3 gateway allows at most 4 connections per source, within the global 16.
  - Garage `/metrics` requires a token (W2-40).
  - The LSP router's stderr forwarding is bounded and `registry_symbols` skips malformed
    records (folded into W2-52).
- **Results:** W2 security mutations 41/41; P5 tests 95 (2 skipped); editor-bridge
  mutants 55/55; s3-guard tests 8/8.
