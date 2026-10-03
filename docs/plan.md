# Implementation plan

This delivery covers design, TLA+ checks and Veil/Lean verification. The distributed
Lean fork itself is subsequent implementation work.

## P0 — Pin the baseline and interfaces

Lean: `nightly-2026-10-03`, commit `193c3589a4fc16c4059261ab38cfa365eb24f323`.
Mathlib nightly: `0575336843263378752eeb5f4c75a612327768a2`; matching toolchain and
successful build/test [CI run](https://github.com/leanprover-community/mathlib4-nightly-testing/actions/runs/37115079169).
This is upstream build evidence, not a local full Mathlib rebuild.

Preserve a stock binary. Freeze encoding, receipts, source capsules, revision rules,
durable acknowledgement and snapshots. Reproduce baseline builds before modifying
Lean. Formal tooling separately pins Veil and Lean 4.32.0.

Gate: baseline Mathlib build, extraction corpus and protocol verification pass.

## P1 — Local declaration replay and stock export

Capture completed groups, exact dependencies and frontend capsules. Reconstruct
compatible environments in one process with a local content-addressed store.
Replay using the stock kernel before adding network transport.

Cover theorems, definitions, structures, inductives, mutual groups, well-founded
recursion, private/generated declarations, instances, simp attributes, scoped
notation, macros and initialization effects. Reject changed targets, new axioms,
`sorryAx`, bypass options and transitive version conflicts.

Export two workspaces, including B→A→B dependencies, into a clean stock-Lean build.
Record cases requiring larger source capsules. Keep source/line mappings usable.

Gate: replay and clean export agree with reference behavior. This is the critical
engineering feasibility gate.

## P2 — Storage and eventual registry

Implement immutable writes, hash verification, durable acknowledgements, anti-entropy,
recovery, causal revisions and conflict diagnostics. Put an existing durable store
behind the modeled interface before inventing a storage system.

Inject duplicate/reordered/lost messages, partitions, killed workers, incomplete
uploads, corrupt bytes, validator timeouts and allowed disk loss. Convert model
counterexamples into protocol regression fixtures. Keep GC disabled.

Gate: no unvalidated/under-replicated publication; convergence; checkpoint recovery,
including loss of the desktop's last manifest hash. Exercise storage enumeration
and causal head reconstruction, not only fetch-by-known-ID.

## P3 — Distributed checks and transparent imports

Add immutable job envelopes, trusted validators, compatibility checks and remote
declaration availability. Pin commands; complete async checks before publication.
Add retry deduplication, cancellation, memory limits and queue backpressure.

Run ordinary agents across machines/worktrees. B must use A's completed helper while
A continues its file. Change an upstream definition and verify invalidation, stale
response rejection and retained old snapshots.

Gate: unchanged agent workflow, adversarial validation, clean exports, fork Lean/
Mathlib tests and measured transfer/checking costs.

## P4 — Distributed LSP

Implement worker routing, URI mapping, search/source aggregation and exact document
version/environment/generation checks. Preserve completion, diagnostics, hover,
goals, rename and cancellation. Keep RPC references session-affine.

Gate: editor tests across death/reconnect; no stale states; measured p50/p95 latency.

## P5 — Autonomous controller

One entry point provisions workspaces, dispatches ordinary agents with fixed targets,
handles conflicts/recovery and exports the final project. AND/OR metadata remains
separate from the reusable library.

Gate: end-to-end multi-agent task, every required contract validated, stock build,
desktop-loss recovery and reproducible scaling benchmarks.

## Deferred changes

Kernel-level lazy body loading needs profiling and a separate correctness argument.
GC, changing membership, shared-writer failover and Byzantine storage change the
protocol assumptions and require new models/proofs. Collaborative text editing is
independent of proof-term representation.

Parallelize storage, indexing and proofs after interfaces freeze. Source/frontend
reproducibility is the critical path. Estimate implementation time only after P1
measures capsule size and unsupported frontend effects.
