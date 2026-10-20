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
The stock build took 5.623 s. This initial trial is not the final gate report:
the realistic list task, adversarial retry checks and scaling runs remain.

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

## Proposed sentences for plan.md and README.md

These are proposals to update after verification, not edits to those files.

- plan.md P5: “An autonomous controller in `impl/p5` provisions private working
  copies, dispatches ordinary Codex or Claude Code CLI workers against fixed
  targets, persists task scheduling separately from library declarations, and
  exports stock Lean source; see [p5-log](p5-log.md) for gate results and limits.”
- README.md: “The P5 autonomous entry point and reproducible task drivers live
  in `impl/p5`; [docs/p5-log.md](docs/p5-log.md) records the tested integration
  versions, recovery evidence and scaling measurements.”
