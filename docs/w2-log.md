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
