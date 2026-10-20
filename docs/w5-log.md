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
TLC runs use one worker each. Initial free space under `/data` was 244 GB.

The SSH test uses a separate user-space `sshd` bound to localhost port 22955,
with private host/client keys and a pinned known-hosts file under `.runs/w5`.
Its authenticated host reports `aws-dev`. Editor and worker roots are distinct.
The delay proxy delays both encrypted byte streams without modifying network
settings. This is a real loopback SSH test, not a second physical machine.

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
The complete hardened suite is still running before re-archiving.

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

## Integration review in progress

Controller publication uses the existing P2/P3 receipt and frozen-target
checks. Review identified and requested fixes for unsaved buffers omitted
from rename inventory, capture process identity after edits/restarts, and
reporting a successful publication after its registry update.

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
Unloaded generalized-method discovery passed its first live store fixture:
Bob used `x.field` without an explicit load of Alice's `Foo.field`. The signed
legacy-capsule replay fixture and final frozen runtime checks are in progress.

## Proposed documentation sentences

For plan.md: “W5 connects stamped private editor capture to controller-owned,
receipt-validated publication and adds policy invalidation and transactional
buffer refactoring; see docs/w5-log.md for verified scope and limits.”

For README.md: “The LSP/controller integration and reproducible SSH latency
gate live in impl/p4 and impl/p5; docs/w5-log.md records their evidence.”
