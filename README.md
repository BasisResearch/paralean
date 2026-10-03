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

The proofs cover admission, immutable dependency graphs, collision handling,
quorum durability, guarded publication/checkpoints and fair convergence. Trusted
checker/exporter/storage interfaces and fairness assumptions are explicit. They
do not prove the future implementation or its performance.

The earlier boundary experiments run with an installed stock Lean binary:

```sh
bash experiments/run.sh /path/to/lean/bin/lean
```

Their recorded run used Lean 4.34.1. The AND/OR experiment concerns private task
scheduling; it does not authorize sharing unfinished proofs as library facts.
