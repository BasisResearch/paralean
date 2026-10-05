# Paralean

Design and formal verification for distributed Lean proof development.

Share completed declaration groups and exact dependency versions. Discover remote
helpers through ordinary Lean tools. Concurrent unrelated declarations of one name
are recorded as a registry conflict; every workspace view keeps the name for the
lineage with the lowest lineage key and renames the others deterministically. Keep
recoverable checkpoints and export source that builds with stock Lean.

- [Architecture and requirements](docs/architecture.md)
- [Lean internals and required changes](docs/lean-integration.md)
- [Implementation plan](docs/plan.md)
- [Store choice and refinement argument](docs/store.md)
- [Verification scope and reproduction](verification/README.md)

The repository contains TLA+ models, finite model checks, kernel-checked Veil/Lean
proofs, small Lean boundary experiments and a P1 prototype (`impl/p1`). The
prototype is a library and CLI on stock Lean `nightly-2026-10-03`, not a fork. It
captures command groups, replays them from a local content-addressed store, exports
to a clean stock build and renders `remote%` working copies. Its
[gate report](docs/p1-gate.md) records G1 to G6 passing on
21 fixture files and an 18-module Mathlib sample; to reproduce it, see
[impl/p1/README.md](impl/p1/README.md). There is no Lean fork, network service, object-store adapter or
distributed LSP yet.

The proposed fork base is Lean `nightly-2026-10-03`, paired with its successful
Mathlib nightly CI revision. Verification separately uses pinned Veil on Lean 4.32.0.

```sh
bash scripts/bootstrap-verification.sh
bash scripts/check-tla.sh
bash scripts/check-tla-negative.sh
bash scripts/check-veil.sh
```

The proofs cover atomic groups, immutable dependency graphs, collision handling,
quorum durability, guarded publication/checkpoints and convergence (under receive
fairness and eventual permanent stabilisation). They also
cover request/receipt binding, required-target completion and catalog recovery
after losing the local checkpoint ID. [Protocol obligations](verification/PROTOCOL-OBLIGATIONS.md)
lists the claims and boundaries. Checker/exporter/storage interfaces and fairness
assumptions remain explicit. The future implementation and its performance are
not proved.

Recovery ancestry is proved equivalent to recorded parent paths. Required targets
permit alternative checked result objects. A connected two-worker execution covers
group admission, receipt acceptance, durable completion and subsequent disk loss.

The strengthened [joint protocol](verification/veil/PROTOCOL.md) requires a durable
catalogue record before completion. Publication also retains a distinct durable
discovery marker. Recovery and discovery use physical quorum scans after local IDs
and indexes are lost. These guards share the same typed store.

The [hardened protocol](verification/veil/HARDENED.md) closes six gaps found in
review, five with transition guards. Staging a group needs a verified validator
receipt whose object is that group's ID; with `receipt_sound` (a verified receipt
names a valid group) this holds even when workers skip their own validity check.
The receipt is bound to the group ID only, not to worker, request, policy or
checker version. `HeldReceipt` reads the global in-flight packet set, which any
actor may extend, so on reachable states the guard is equivalent to the static
fact that a verified receipt for the group exists; the substance is the
`receipt_sound` assumption. Binding the signature to policy and checker version is
an implementation contract. Each target has a reassignable owner whose
publications are fenced by an epoch, so alternative proofs form a chain across
handovers. Catalogue first writes and commit certificates are fenced in the store.
Discovery reads per-replica acknowledgement certificates, and commits need the
committer's own reply quorum. All five guards are proved together on one joint
step. The sixth fix, group membership that follows real Lean naming including
auto-named instances, is a separate refinement of `member` (`LeanNames`) that
`Hardened` does not import. Liveness is not restated for the hardened protocol.

The earlier boundary experiments run with an installed stock Lean binary:

```sh
bash experiments/run.sh /path/to/lean/bin/lean
```

Their recorded run used Lean 4.34.1. The AND/OR experiment concerns private task
scheduling; it does not authorize sharing unfinished proofs as library facts.
