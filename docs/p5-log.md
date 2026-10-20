# P5 autonomous controller work log

Workstream `m-p5`, started 2026-10-20 on aws-dev from
`7df9aceeff08d673703c9579145b5fb68c476c9a` (`origin/main`).
Ownership is `impl/p5/` and the end-to-end scripts. No changes to plan.md,
README.md, P2, P3 or the LSP are intended.

## Execution and interfaces

The implementation is delegated into three disjoint scopes: Python controller and
ordinary coding-agent adapters; P2/P3 backend and durable task journal; task,
regression tests and end-to-end/benchmark drivers. The requested subagent model
`gpt-6.1-sol` was rejected by the available tool; these agents use `gpt-6-sol`.
The parent reviews, integrates, runs live verification and commits.

The reusable Lean library contains completed declarations only. Frozen statements,
the dependency graph, worker assignment, attempts and run status remain private
controller metadata in the store. The backend boundary isolates moving P2/P3 APIs.
The entry point is `python3 impl/p5/paralean.py run TASK.toml`.

The initial upstream inspection found that `plr validate` and `plr publish` on
`7df9ace` have no target bindings, although P3's validator and P2 publication
transaction already support them. A successful build or a target-free receipt
does not establish P5's fixed-contract gate. This integration is tracked explicitly.

## Isolation and resources

Only instance `PARALEAN_INSTANCE=p5-m-p5` is operated here:
`/data/home/kirancodes/paralean-p5-m-p5-cluster`, FDB 5089, Garage
18839–18841, delete-denying S3 gateway 18833, validator 18891.
P5 wrapper scripts verify instance ownership; shutdown checks PID command lines.
Existing P2 service binaries are read-only inputs. No other cluster is stopped or
changed. At startup `/data` had 273 GB available (71% used).

The Lean fork is the read-only `paralean-fork` installation at
`dfc13cc6be6563cc399d306887c2d8df294e001c`. P1 and Rust build artifacts were copied
from the `paralean-p3-remote` checkout at exactly `7df9ace`, then rebuilt as needed.
The final export must build with stock Lean
`193c3589a4fc16c4059261ab38cfa365eb24f323` (`nightly-2026-10-03`).
Lean threads default to one and Cargo jobs to two. Eight logical workspaces may
be benchmarked with a lower physical concurrency cap; results must state both.

## Integration versions

Initial fetch and the subsequent setup fetch both saw `origin/main=7df9ace`.
`origin/m-targets`, `origin/m-p2`, and `origin/m-p4` were absent at those fetches.
No unpushed branch is treated as tested integration.

The next published dependency was `origin/m-p4=3adea8f` (collision tooling and
history-preserving projection branches). P5 was rebased onto it. It changes
`impl/p4/` and its log only, so the P2/P3 binary interfaces remain at `7df9ace`.
`m-targets` and `m-p2` were still absent at this integration checkpoint.

Both remaining branches subsequently landed: `m-targets=463e6d8` and
`m-p2=323bd48`. P5 was rebased onto each, preserving P4's changes. Sequential
rebases change the copied upstream commit hashes; the original branch hashes
above identify the patches tested. The P5 adapter was updated for the new
authenticated validator API, using its authority signer and pinned validator
public keys. P2/P3 release binaries and the P5 bridge were rebuilt together.
Warm checking remains disabled; these runs measure the cold checker.

A later fetch found P4 `fade5b3` (persistent Lean worker routing and editor
state fences). P5 was rebased onto it before the Codex adapter smoke and scaling
runs. It changes only P4 and its log; the P1/P2/P3/P5 gate implementation is
unchanged. The latest fetch before scaling still found main `7df9ace`, targets
`463e6d8`, P2 `323bd48` and P4 `fade5b3`.

## Gate and benchmark status

Initial live trial: ten addition lemmas proved by ordinary Claude Code CLI
workers, ten frozen statement contracts validated against signed receipts and
current target heads, and all sixteen declared dependency edges found in the
checked package closures. The controller was killed after partial publication,
its local task file and working state were removed, and recovery by task ID
retained the published group IDs and completed all ten targets.

The initial export failed because P1's environment unconditionally supplied a
nonexistent Mathlib checkout even for this core-only task. P5 now removes that
environment variable for tasks without Mathlib imports. Retrying the same
recovered task exported ten modules, built them with stock Lean `193c3589`, and
re-encoded all ten groups identically; P2 committed catalogue
`937a66a3eea816ce81273f00b73f2e5b3405d022a0a8de49d085ed43fd537340`.
The stock build took 5.623 s. This initial trial is superseded by the realistic List gate recorded below.

Seven tests pass under the sourced P5 environment, including comparing the
private contract compiler's type hash with actual P1 capture, rejection of an
ill-typed contract, dependency-edge checking, simulated publication conflict
retry, and controller recovery after deleting local state.

The task journal's live put/get/list/idempotent retry checks pass. Authority keys
are sealed with AES-GCM under a separate deployment recovery secret, rather
than the workers' S3 credential. Workers do not inherit this recovery secret or
Garage administration credentials. This does not claim OS isolation between
mutually hostile processes running under the same Unix account.

Before the final upstream integration, the realistic List gate passed all eight
checks in `impl/p5/results/pre-integration-gate.json`: ten frozen contracts,
sixteen actual dependency edges, remote helper projections, task discovery by
store enumeration, deletion of the entire desktop including TASK.toml, recovery
preserving acknowledged groups, and stock export. The run took 175.955 s including
export (166.317 s through target validation). A separate clean build of the
initial export, with no Paralean environment variables or copied build cache,
also passed on stock Lean; see `impl/p5/results/isolated-stock.json`.

All seven live adversarial checks passed before integration
(`impl/p5/results/pre-integration-adversarial.json`): invalid DAG, missing target,
changed statement, stale epoch, successful retry under a fresh epoch, stale task
journal writer, and idempotent assignment. This found a P5 bug: capture can return
an older rejected draft as well as the edited candidate. The adapter now selects
the candidate whose capsule text matches the current file before asking the
validator to check it.

## Integrated live evidence

The integrated List gate passed all eight checks in
[`integrated-gate.json`](../impl/p5/results/integrated-gate.json). Ordinary Claude
Code workers proved a generic map-length helper, eight reverse/map
specializations and their conjunction. All ten frozen statement hashes matched
signed validator receipts and the current target heads; all sixteen required
package dependency edges were present. The gate killed the controller after two
publications, deleted the whole desktop directory including TASK.toml and keys,
enumerated the surviving store to rediscover the task ID, and completed recovery
with the acknowledged group IDs unchanged. Deployment credentials and compiler
installations are external inputs, not recovered desktop state.

The run took 134.584 s including export, with 126.731 s through target validation.
The stock export contained ten modules and re-encoded all ten groups identically;
its build took 2.991 s. The final P2 catalogue was
`5560b8cde53a2ad995e4e118e847965fdc4aeee167a86988ea719bc1f75a722f`.
The gate's controller metrics exclude export costs because its driver exports
in a separate command. All seven integrated live adversarial checks also passed;
see [`integrated-adversarial.json`](../impl/p5/results/integrated-adversarial.json).

The actual generated source is retained in
[`list-export/`](../impl/p5/results/list-export/). An independent clean build used
stock Lean `193c3589` with no Paralean environment variables, no remote services
and no copied build cache: ten oleans, 5.753 s, success. See
[`list-isolated-stock.json`](../impl/p5/results/list-isolated-stock.json).
This establishes that the delivered library contains ordinary Lean source;
the task scheduling metadata is not part of that library.

The configurable Codex adapter also passed a live two-target dependent task,
including both fixed contracts and a stock export, in 86.863 s. Its worker sandbox
allows network access for `remote%` demand fetching. See
[`codex-smoke.json`](../impl/p5/results/codex-smoke.json). The tested CLI versions
are Claude Code 2.1.304 and codex-cli 0.156.1; Python is 3.14.4 and Cargo is 1.98.1.
Credentials were taken from the existing box configuration and are not in the
result artifacts.

## Review hardening before final measurements

Parent review and delegated regression review found two completion edge cases:
a completed run trusted an existing export directory, and the final catalogue
selected all cached revisions rather than the exact live export closure. P5 now
rechecks current heads and rebuilds the export on completed recovery. A small
P5 Lean helper calls the same P1 `Remote.view` and `Catalog.ofStore` functions as
`ws-export`, so the checkpoint selects the built live closure and rejects stale
dependencies. Historical revisions remain in the store.

The upstream `plr checkpoint` command also leaves required targets and target
checks empty. P5's target-bound checkpoint adapter instead records every frozen
contract's checked group and assignment in the P2 snapshot and build receipt.
It captures an additional stock `lake build` log to supply a real log hash and
compiler commit. P2's existing T5 checks its catalogue fence but does not check
target records. P5 therefore checks every required target's owner, epoch and head
in the same FDB transaction that marks its journal complete. A stale completion
write fails even if a catalogue was already produced. This is the P5 completion
point; an older catalogue remains a historical build, not a fresh completion
claim. No P2 or P3 source changes implement these guards.

The journal now authenticates its complete canonical payload with HMAC-SHA256
under a domain-separated recovery-secret key. Its signed sequence must match the
FDB head. Both normal loading and store-only recovery verify this before trusting
the task specification or restoring keys. Tampered, unsigned and replayed payloads
are rejected. Earlier unsigned prototype journals are intentionally unsupported;
all final runs use fresh deployments. This prevents workers from forging accepted
controller metadata with their store credentials, but does not provide availability
against a malicious store writer or OS isolation under the shared Unix account.

The final sourced local suite passes 17 tests, including new cases for changed
completed heads, corrupt existing export output, exact snapshot selection,
noncurrent dependencies, journal authentication and signed-sequence replay.

The final live adversarial rerun passed all ten checks, including target-bound
checkpoint contents, accepted current completion and rejected stale completion
after reassignment. The first attempt passed the new checks but one missing-target
check encountered a native bridge `SIGSEGV` during a store read before reaching
its assertion; the complete rerun passed. No native-client retry or upstream
change hides that failure. The final P2 integration is `32549af` (gray-failure and
coordinator-replacement scripts/evidence only); the Rust API is unchanged.

## Latest upstream integration

After the hardened gate passed, another fetch found targets `bd081a4`, P2
`c727a58` and P4 `bae5195`. P2 had rebased onto its integrated `p2-rest` merge;
P4 now changes P1 and pins fork `99967f1ee50a1ee82bb178359ad95b723c8196a2`.
The branch was rebased onto all three, preserving P2's merge history. Recreating
that merge omitted some original manual resolutions, so the published P2 tree
and P3 tombstone/certificate integration were explicitly restored. Relative to
`c727a58`, P2 differs only by the published m-targets Cargo.lock, T1 dependency
certificate guards and Writer signer visibility. This is integration resolution,
not additional P5 store functionality. P1, the fork patches and P4 match
`bae5195` exactly. Both P3 logs and the P2 log retain their upstream versions.

P5 reads the already-built P4 fork installation without changing it and rebuilds
its own P1 artifacts. It also now calls P2's new native FDB network shutdown API
before its bridge process exits, matching P2's CLI lifecycle. The earlier native
bridge crash remains a recorded observation; this change addresses the newly
available shutdown contract without claiming its cause was proven.

## Proposed sentences for plan.md and README.md

These are proposals to update after verification, not edits to those files.

- plan.md P5: “An autonomous controller in `impl/p5` provisions private working
  copies, dispatches ordinary Codex or Claude Code CLI workers against fixed
  targets, persists task scheduling separately from library declarations, and
  exports stock Lean source; see [p5-log](p5-log.md) for gate results and limits.”
- README.md: “The P5 autonomous entry point and reproducible task drivers live
  in `impl/p5`; [docs/p5-log.md](docs/p5-log.md) records the tested integration
  versions, recovery evidence and scaling measurements.”
