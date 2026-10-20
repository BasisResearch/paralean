# W5: LSP to controller wiring

Started from `fee94d9` on branch `w5-lsp-wiring`, 2026-10-20. The parent
delegated controller integration, transactional rename, and Lean recapture /
method discovery to three GPT-6 Sol agents, and owns review, formal modeling,
SSH measurements, integration verification and commits.

## Isolation

W5 owns `.runs/w5/cluster`, instance `p5-w5`, FDB port 23589, Garage
23639–23641, S3 gateway 23633 and validator 23691. The attempted choices 5289
and 19333 were occupied; startup refused them before touching their services.
Source `impl/p5/scripts/w5-env.sh` to reproduce this configuration.
Private P1 build artifacts were copied from P4; shared caches are not rebuilt.
TLC initially used one worker per run while private builds were active.
After builds finished, the full hardened suite was restarted with three TLC
workers and a 4 GB heap; the earlier partial run remains under `.runs/w5`.
Initial free space under `/data` was 244 GB.

The SSH test uses a separate user-space `sshd` bound to localhost port 22955,
with private host/client keys and a pinned known-hosts file under `.runs/w5`.
Its authenticated host reports `aws-dev`. Editor and worker roots are distinct.
The delay proxy delays both encrypted byte streams without modifying network
settings. `tc` is installed, but this session lacks `CAP_NET_ADMIN`, so the
userspace proxy supplies the added latency. This is a real loopback SSH
test, not a second physical machine.

## Protocol model before implementation

`verification/tla/EditorWiring.tla` models three finite scenarios:

- Publication requires a validator receipt, explicit action or policy, and
  the captured document/environment/generation stamp still being current.
  Policy advancement invalidates old editor sessions.
- Rename requires every participant, complete dependency inventory, valid
  plans and current stamps, with one atomic change of the buffer set.
- Derived legacy field metadata requires identity matching and verified
  replay; it does not replace signed capsule bytes.

Checks passed: publication 178 distinct states, rename 872, private replay 5.
Eleven guard removals produce the expected safety counterexamples; three
reachability cases establish publication, rename and replay are possible.
The scenarios and mutations are wired into the normal check scripts. The full
default suite passed all 24 positive scenarios and 99 expected-outcome cases.
All four wide scenarios and all 29 hardened cases passed their expected
outcomes. Re-archiving with `--tla-only` and then `--verify` both passed,
retaining all 156 cases and checking their current-source provenance.
These are finite boundary models: receipt verification, semantic plans and
source replay enter as subsystem verdicts. No new unbounded Lean proof is
claimed. Existing Veil proof artifacts remain unchanged.

## SSH evidence

`impl/p4/tests/ssh_gate.py` sends actual LSP frames through the router and SSH
to a separately rooted persistent Lean worker. It edits an unsaved buffer,
checks error and clean diagnostics, exact source/version, hover, goals and
completion. The initial ten-sample baseline passed using the existing P4 fork
and frozen P4 library. Evidence: `impl/p4/results/w5-ssh-baseline.json`.
The added-delay run also passed. Initial p50/p95 milliseconds:

| Request | SSH baseline | SSH, 40 ms each direction |
|---|---:|---:|
| Error diagnostics after edit | 206.27 / 455.20 | 290.84 / 506.70 |
| Clean diagnostics after edit | 205.10 / 206.65 | 286.02 / 288.77 |
| Hover | 1.98 / 7.24 | 83.22 / 86.79 |
| Goals | 1.56 / 1.83 | 82.99 / 85.58 |
| Completion | 180.98 / 547.77 | 248.92 / 606.23 |

These ten-sample measurements include the first request and are descriptive
results on a shared host. `impl/p4/tests/ssh_benchmark.sh` creates its own
daemon, keys, pinned host identity and roots for reproduction. The SSH checkpoint
was pushed as `744dbec`.

The final pinned-fork runtime also passed both ten-sample runs, through the
reproduction script's dedicated port 22956. Reports are
`impl/p4/results/w5-ssh-final-{baseline,delayed}.json`. Final p50/p95 ms:

| Request | SSH baseline | SSH, 40 ms each direction |
|---|---:|---:|
| Error diagnostics after edit | 214.37 / 722.93 | 296.08 / 687.62 |
| Clean diagnostics after edit | 211.36 / 233.29 | 292.90 / 334.84 |
| Hover | 5.31 / 65.07 | 87.07 / 123.01 |
| Goals | 5.15 / 7.41 | 90.12 / 113.95 |
| Completion | 247.67 / 1498.06 | 339.25 / 852.34 |

Cold-start requests are included. These figures describe this shared-host run,
not a WAN throughput or capacity claim.

## Controller and policy integration

`impl/p4/controller_bridge.py` connects explicit `paralean/capture` and
`paralean/publish` requests to the frozen P5 task. Document notifications do
not publish. Publication requires the exact privately captured buffer,
target/file contract, owning workspace and dispatch epoch, and the existing
P2/P3 validator receipt. The backend rechecks source bytes, editor stamps and
authoritative policy after validation, immediately before the guarded store
commit. Its response reports a successful commit even when that publication
itself advances the environment.

`policy-state` reads live validator revocations even before any group exists.
The controller's one-second polling feed combines this with current registry
and receipt state and pushes `paralean/environmentChanged`. It invalidates
sessions and captures, fences the old worker before remote synchronization,
and resumes only after synchronization and initialization. Failed policy
queries or synchronization keep the workspace unavailable. Responses wait for
an in-flight policy decision and then undergo normal stamp checks. This is a
polling-backed push feed, not an FDB watch or zero-latency revocation claim.

P5 provisions dedicated, ownership-marked SSH roots with pinned host keys,
worker credentials and public trust. Provisioning commands use null stdin
so they cannot consume editor protocol frames. Policy updates mirror the
trust/cache/source state and replay unsaved buffers into the new worker.
The remote relay reaps Lean descendants when its SSH stream closes.

The local live gate passed private invalid-draft refusal, private successful
capture, stale publish refusal, receipt publication, current target validation,
stock export, worker-key revocation refusal and idle session expiry after an
authority-signed store revocation. A fresh SSH gate additionally passed a
second target using the first published proof through `remote%` after policy
feed synchronization. The complete integrated gate passed all nine checks
under `.runs/w5/integrated-complete`: ten target contracts, exact dependency
closure, desktop deletion, store discovery/recovery, stock export and the
scripted SSH LSP worker. The final `.runs/w5/final-certified` rerun also passed
all nine checks, including trust-source refresh, task binding, SSH trust-file
propagation and live revocation. This is an integration correctness gate,
not a scaling comparison. The committed final reports are
`impl/p4/results/w5-integrated-gate.json` and `w5-lsp-{local,ssh}.json`.

Attached P5 sessions pin controller keys/trust to the state directory and
worker store/work/keys/trust/visibility to each provisioned root. An
environment-file override is refused both at attachment and on later reload.
The feed refreshes public trust before its authoritative probe without
rewriting source files. The live trust-file check reformats unchanged trust
decisions to exercise byte-identity propagation; the separate signed
revocation check changes actual store admission.

The first integrated attempt passed all eight original recovery checks and
all ten target contracts, then exposed SSH startup input consumption. The
first debug SSH run also exposed missing public trust in remote roots.
Both defects have regression tests and guard mutations; their failed runs
remain under `.runs/w5` rather than being presented as passing evidence.

## Transactional rename scope

The rename implementation commits server-owned replay buffers, not a claim
that an arbitrary editor will atomically apply a WorkspaceEdit. The parent
independently passed three real Lean tests: successful two-workspace edits,
wrong-anchor refusal, and incomplete-inventory refusal. This fixture supplies
the dependency inventory; Lean produces the actual definition and rename
results. An `.ilean` source index is required for imported source provenance.

**Published-rename blocker:** the read-only probe against the real P3 method
fixture finds duplicate package identities in Alice's and Bob's projections.
Bob's signed `Use` capsule contains `x.field`, but the editable `Use.lean`
contains only a `remote%` stub. Current rename refuses this case and changes
no buffers. General published cross-workspace rename needs capsule-aware
materialization/refactoring and certified dependency/source coverage. The
ordinary imported-source fixture is not evidence that this is implemented.

The store limitation is concrete: `Rga.View.of` creates rename maps only for
same-name collision losers (`impl/p1/Paralean/Rga.lean`), not for signed
user-requested rename events. P2's T1 publishes one group at a time
(`impl/p2/crates/store/src/meta.rs`); `plr publish --plan` loops over groups and requires
each marker's author to be its publishing workspace. Anti-entropy also delivers
per group. Full published rename therefore needs either a certified rename
event with a complete affected-closure fence and atomic visibility, or a
multi-group, multi-author publication certificate and delivery bundle.
Reusing the current rendering map or sequential T1 calls would not provide
the requested atomicity.

The private fork builds at `bd12276840543d83766ce66c82cf260d818b8d83`.
The parent replayed all eight patches from the pinned upstream commit in a
separate private checkout and reproduced that hash.

## Legacy recapture and method discovery

Bob can use `x.field` without an explicit load of Alice's `Foo.field`. The
same published fixture fails on the previous P4 runtime with
`Unknown constant Foo.field` and succeeds on W5. Ordinary field notation
also passes with Paralean disabled and with mode enabled but no store.

The legacy fixture was genuinely captured with missing field metadata and
then signed and published normally. The production runtime was restored
before testing it. A fresh child replays its receipt-checked exact dependency
closure, checks replay success and original declaration/source identity, and
validates recovered field spans. The overlay is keyed by signed capsule ID
and stays in process memory. The fixture passes selective field rewriting
and direct remote replay while capsule bytes, ID and receipt remain unchanged.
A failed helper leaves the old fail-closed diagnostic in place.

Eleven isolated source mutation cases cover receipt verification, replay
success/count, declaration/source identity, and span ordering, bounds, dot,
token target, target shape and UTF-8 validity. All 22 guarded/mutated
observations pass: each guarded input fails for its specific expected reason
and each corresponding mutant accepts it. Empty/inverted spans also fail
later checks, so those redundant checks are not counted as independent
mutation detections.
`impl/p1/scripts/w5_recapture_mutations.py` reproduces these cases without
changing the production runtime. Reports are under `impl/p4/results/w5-*`.

## Reproduction and focused verification

The parent independently verified the final focused suite:

| Check | Result |
|---|---:|
| P5 unit/integration tests under the W5 environment | 50 passed, none skipped |
| Rename unit tests | 25 passed |
| Two-worker real Lean rename fixtures | 3 passed |
| Editor/provision/router source mutants | 31 detected |
| Compiled Rust authority-guard mutant | 1 detected |
| Rename source mutants | 18 detected |
| Isolated Lean recapture source mutants | 11 detected |
| Full P5 recovery + SSH LSP gate | 9 checks passed |

The 61 implementation mutation cases require assertion failures or the
specific expected rejection; compilation errors do not count as detections.
`impl/p4/results/w5-focused-verification.json` records counts, source hashes
and runtime identity. The same tree also passed the ordinary editor regression
with worker death/recovery, both ten-sample SSH conditions, the signed legacy
fixture, and the old/new runtime method-discovery comparison.

With the private runtime built, focused checks are:

```bash
source impl/p5/scripts/w5-env.sh
python3 -m unittest discover -s impl/p5/tests -v
python3 impl/p5/tests/mutate_editor_bridge.py
python3 impl/p5/tests/mutate_revoke_guard.py
python3 impl/p4/tests/rename_transaction_test.py
python3 impl/p4/tests/rename_mutation_test.py
python3 impl/p4/tests/rename_real_lean_test.py -v
bash impl/p4/tests/ssh_benchmark.sh
```

Live store fixtures additionally require the owned cluster from
`impl/p5/scripts/cluster-up.sh`. `w5_recapture_gate.py` documents the separate
legacy preparation and restored-runtime verification steps; its mutation
runner takes that signed fixture and an isolated build directory.
`gate.py --lsp-worker --lsp-ssh-* --lsp-revoke-policy` runs the full recovery
gate and SSH child. Use a fresh state directory, deployment and dedicated
remote root for each run. The W5 store and SSH daemon were stopped after the
live checks; no shared services were stopped.

The complete model/archive reproduction is:

```bash
TLC_WORKERS=1 TLC_HEAP=3g bash scripts/check-tla.sh
TLC_WORKERS=1 TLC_HEAP=3g bash scripts/check-tla-negative.sh
TLC_WORKERS=2 TLC_HEAP=3g bash scripts/check-tla.sh --wide
TLC_WORKERS=3 TLC_HEAP=4g bash scripts/check-tla-hardened.sh
bash scripts/archive-verification.sh --tla-only
bash scripts/archive-verification.sh --verify
```

## Proposed documentation sentences

For plan.md: “W5 connects stamped private editor capture to controller-owned,
receipt-validated publication and adds policy invalidation and transactional
buffer refactoring; see docs/w5-log.md for verified scope and limits.”

For README.md: “The LSP/controller integration and reproducible SSH latency
gate live in impl/p4 and impl/p5; docs/w5-log.md records their evidence.”
