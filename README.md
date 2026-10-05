# Paralean

Design and formal verification for distributed Lean proof development.

Share completed declaration groups and exact dependency versions. Discover remote
helpers through ordinary Lean tools. Concurrent name collisions produce eventual
errors. Keep recoverable checkpoints and export source that builds with stock Lean.

- [Architecture and requirements](docs/architecture.md)
- [Lean internals and required changes](docs/lean-integration.md)
- [Implementation plan](docs/plan.md)
- [Verification scope and reproduction](verification/README.md)

The repository contains TLA+ models, finite model checks, kernel-checked Veil/Lean
proofs and small Lean boundary experiments. It does **not** yet contain a Lean fork,
network service, object-store adapter, source exporter or distributed LSP.

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

The [hardened protocol](verification/veil/HARDENED.md) closes five gaps found in
review. Publication needs a validator receipt for the exact group, and this holds
even when workers skip their own validity check. Each target has a reassignable
owner whose publications are fenced by an epoch, so alternative proofs form a
chain across handovers. First catalogue writes are fenced in the store. Discovery
reads per-replica acknowledgement certificates, and commits need the committer's
own reply quorum. Group membership follows real Lean naming, including
auto-named instances. All four transition guards are proved together on one joint
step. Liveness is not restated for the hardened protocol.

The earlier boundary experiments run with an installed stock Lean binary:

```sh
bash experiments/run.sh /path/to/lean/bin/lean
```

Their recorded run used Lean 4.34.1. The AND/OR experiment concerns private task
scheduling; it does not authorize sharing unfinished proofs as library facts.
