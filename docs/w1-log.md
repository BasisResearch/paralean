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

The proposed correction is to restore the captured module context when
the replay closure has one source module. Identity encoding and validator
acceptance remain exact. A replay model and mutation case precede the
implementation; focused tests must demonstrate both successful replay
and rejection of changed declaration bytes.

## Results

Work in progress; measurements and the final verification summary will
be recorded here after review.
