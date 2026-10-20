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

## Gate and benchmark status

Implementation and verification are in progress. No P5 gate or scaling result is
claimed at this checkpoint. The final section will distinguish passes, failures,
blocked requirements and measured quantities.

## Proposed sentences for plan.md and README.md

These are proposals to update after verification, not edits to those files.

- plan.md P5: “An autonomous controller in `impl/p5` provisions private working
  copies, dispatches ordinary Codex or Claude Code CLI workers against fixed
  targets, persists task scheduling separately from library declarations, and
  exports stock Lean source; see [p5-log](p5-log.md) for gate results and limits.”
- README.md: “The P5 autonomous entry point and reproducible task drivers live
  in `impl/p5`; [docs/p5-log.md](docs/p5-log.md) records the tested integration
  versions, recovery evidence and scaling measurements.”
