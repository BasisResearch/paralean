# W1 validator certification

`summary.json` and `certification.json` are the final checker measurement.
The two source reports partition M01–M18 into odd and even module numbers.
Each report row is emitted only after the store audit succeeds.
`capture.json` records the corresponding fresh capture counts.

The checker uses the final two-pass export lookup. Its checker ID is
`705c50ee338a2f69f5407963e9d98df5546bb2a69ef2adcb4fabf85cdbd6c2d2`.
`provenance.json` records production source and binary SHA-256 hashes,
the Mathlib pin, and the fork pin. The older complete certification under
`first-lookup-fix/` is supplementary evidence from the earlier lookup repair.

Reproduce using private copies of the pinned fork and Mathlib, a warm
checker built against the same P1 library, and a dedicated P3 cluster:

```sh
cargo test --release --manifest-path impl/p2/Cargo.toml \
  -p paralean-control --test mathlib_throughput \
  -- --ignored --nocapture --test-threads=1
```

The test reads its executable, Mathlib, store, and cluster settings from the
P3 environment. W1 ran two disjoint `PARALEAN_P3_MEASURE_MODULES` selections
with one warm checker per module and batch size 32. Both shards must finish
before combining the reports:

```sh
python3 impl/p3/scripts/aggregate-mathlib-certification.py impl/p3/results/w1
```

The aggregator requires exactly 18 distinct modules and 1,105 groups,
agreement with capture, one checker/toolchain identity, no validation
failures, complete publication, and unchanged private Mathlib build outputs.
`base-before.json` and `base-after.json` summarize a SHA-256 manifest of
the main and dependency build trees, including OLean sidecars.
`impl/p3/scripts/hash-lean-build.py ROOT OUTPUT` reproduces those manifests.
Timing totals sum module elapsed times on a shared machine; they are not
an isolated performance comparison.
