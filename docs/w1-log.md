# W1: Lean replay and identity bugs

Work began 2026-10-20 on `w1-lean-bugs`, based on
`fee94d9be23d9e9902cb006b1e8cdfaa3bcf809c` (`origin/main`).

## Scope and safety

The work covers the M08 `by_cases!` replay failure, the scope of export
identity for module-dependent literals, and fresh stock/fork G1–G6
measurements. Exact declaration-ID validation must remain mandatory.
The historical export identity denominator is 1,142: its 26 mismatches
include four core fixtures and 22 Mathlib groups, rather than 26 Mathlib
groups in addition to the core four.

Three GPT-6-sol agents were delegated disjoint implementation, identity
proof/model, and gate measurement tasks. The primary agent reviews and
integrates their changes and runs validator certification.

Builds and measurements use private caches under this worktree. Shared
Mathlib/toolchain installations are copy sources only. Initial free space
on `/data` was 244 GiB. Heavy work is limited to six processes across the
team. Any services started for certification use a W1-specific prefix
and ports.

## Investigation

The historical M08 failure is reproduced in
`impl/p3/results/m-targets-cold-M08-private.log`: stored declaration
`f5a1a2428cd2…`, replayed declaration `b20f7eca3d55…`.
`sourceReplay` chooses `Mathlib.ParaleanReplay` while capture runs under
`Mathlib.Tactic.ByCases`. Lean's generated macro helper includes this
module name in a literal in the declaration body. The canonical encoder
preserves literal bytes, and the validator correctly rejects the result.

The correction restores the captured module context when
the replay closure has one source module. Identity encoding and validator
acceptance checks are unchanged. A replay model and mutation case preceded
the implementation. Mixed-module closures retain the synthetic module;
this change makes no universal replay-completeness claim for such closures.
No fork patch or fork rebuild is needed.

Targeted fork reproduction preserves the historical M08 package
`4cb846e8e10a561a786626acb401de0870008bb7e08a975539752eb086a795d4`
and declaration
`f5a1a2428cd23c4930dd18c0dfed5c2b5e8d81c1429f48e99e1b0315f9f22bfa`.
The patched cold `check-group` returns `ok: true` without diagnostics.
M08 source, kernel, and isolated replay each pass 3/3 groups.

The five fork hook fixtures pass against a private copy of the pinned
`99967f1ee50a1ee82bb178359ad95b723c8196a2` installation, including the mode-off
fixture. Evidence: `fork/results/w1-fork-subset.json`.

## Identity scope

[The identity analysis](w1-identity.md) inventories the 26 historical export
mismatches and explains why a universal quotient of module-dependent name
literals cannot preserve their observable values. The interface notes now
state the narrower claim explicitly. No literal normalization or export
validator exception was added.

The real `register_simp_attr` witness passes on stock and fork: two identical
commands elaborated in different modules contain different module-name
values in their generated initializer bodies. Logs:
`verification/results/w1/identity-stock.log` and `identity-fork.log`.
The Lean proof separates declaration-name rendering from observable values
inside terms. Initializer materialization remains a separate existing effect
coverage mechanism; it does not establish exact export-body identity.

## Results

Work in progress; measurements and the final verification summary will
be recorded here after review.
