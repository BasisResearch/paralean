# P1 prototype: local declaration replay and stock export

`impl/p1` is a Lean 4 library and CLI (`paralean`) that captures declaration groups at
command granularity, stores them content-addressed, replays them (source, stock kernel,
isolated) and exports them to a clean stock-Lean package. It runs on the stock nightly
`leanprover/lean4-nightly:nightly-2026-10-03` (commit
`193c3589a4fc16c4059261ab38cfa365eb24f323`), with no fork. The gate report is
[docs/p1-gate.md](../../docs/p1-gate.md); the corpus and thresholds are in
[docs/p1-corpus.md](../../docs/p1-corpus.md).

## Reproduce

Requirements: [elan](https://github.com/leanprover/elan), git, python3, about 7 GB of disk
for the Mathlib cache. Everything is put inside the repository; nothing depends on paths
outside it.

```sh
impl/p1/scripts/bootstrap.sh            # toolchain (checked to be 193c3589), fixtures, paralean
impl/p1/scripts/bootstrap.sh --mathlib  # also Mathlib at the versions.json pin + `lake exe cache get`
impl/p1/scripts/run-all.sh              # the whole gate (needs --mathlib above)
impl/p1/scripts/run-all.sh --no-mathlib # fixtures, F14, F15, negatives, F-async only
```

`bootstrap.sh` installs the toolchain with elan if needed and fails unless `lean --githash`
is the pinned commit. With `--mathlib` it fetches
`mathlib4-nightly-testing@0575336843263378752eeb5f4c75a612327768a2` into `.deps/mathlib`,
runs `lake exe cache get`, and checks with `lake build --no-build` that the cache covers the
corpus modules. It never starts a Mathlib build; if the cache is missing it stops and says
so.

Logs go to `impl/p1/results/`; work directories (stores, exports) to `.runs/p1/`. Every
default can be overridden (all scripts source `scripts/env.sh`):

| variable | default | meaning |
|---|---|---|
| `PARALEAN_RUNS` | `<repo>/.runs/p1` | stores and exports |
| `PARALEAN_BIN` | `impl/p1/.lake/build/bin/paralean` | the CLI |
| `PARALEAN_MATHLIB` | `<repo>/.deps/mathlib` | Mathlib checkout with its `.olean` cache |
| `PARALEAN_TOOLCHAIN` / `ELAN_TOOLCHAIN` | `leanprover/lean4-nightly:nightly-2026-10-03` | toolchain the elan proxies resolve to |
| `PARALEAN_LAKE` | elan's `lake` | `lake` used for stock export builds (e.g. a frozen source build) |
| `PARALEAN_SYSROOT` | `lean --print-prefix` | Lean installation `paralean` loads `Init`/`Lean` from |
| `PARALEAN_RESULTS` | `impl/p1/results` | where `run-all.sh` writes logs |
| `TMPDIR` | `<repo>/.runs/tmp` | scratch |

A script fails with a message naming the missing piece (toolchain, binary, Mathlib
checkout, Mathlib cache) instead of running against a wrong one. `paralean` itself refuses
to start when the Lean installation it would load is not the commit it was built with
(previously a wrong default toolchain gave "incompatible header" on `Init.olean` at the
first capture).

Per-set scripts: `run-core.sh` (F01–F13), `run-crossws.sh` (F14), `run-mathlib.sh [WORKDIR]
[M01 …]`, `run-negative.sh` (N1–N6, version conflict, duplicate instance). Gate summaries:
`scripts/g2.py WORKDIR` (membership and name classes), `scripts/g4.py WORKDIR [SET…]`
(`#print axioms` and source/line mappings of the export), `scripts/summarize.py`. The
Track B scripts (`run-transparent*.sh`, `remote-*.sh`, `async-cost.sh`) use GNU `time`
and were run on Linux only.

### Toolchain provenance

The recorded gate run of 2026-10-05 (aws-dev, Linux x86-64) built and ran everything with
elan's `nightly-2026-10-03`, but the corpus protocol and the P0 reference data use a frozen
source build of the same commit (`~/p0-deps/lean-stock-193c3589`). The two report the same
`Lean.githash`; only the version string in `.olean` headers differs, and the release
binary rejects the source build's `Init.olean` (p0-log.md). Results are reproducible with
elan alone. To use a source build instead, put it first on `PATH`, set
`PARALEAN_SYSROOT` and `PARALEAN_LAKE` to it, and use a Mathlib built by it (the cache's
`.olean` headers carry the release version string).

## On the Paralean Lean fork

`fork/build.sh` builds the fork; then `PARALEAN_LEAN=fork` makes every script use it instead of
elan's toolchain (its `lean`/`lake` first on `PATH`, `fork/GITHASH` as the pin, Mathlib in
`.deps/mathlib-fork`, work in `.runs/p1-fork`):

```sh
fork/build.sh
PARALEAN_LEAN=fork impl/p1/scripts/bootstrap.sh --mathlib   # builds only the corpus' Mathlib closure
PARALEAN_LEAN=fork PARALEAN_RESULTS=impl/p1/results/fork impl/p1/scripts/run-all.sh
```

`Paralean/Fork.lean` selects at build time: compiled against the fork, P1 uses the fork's
hooks in place of its library workarounds (collector, `simp` record, canonical instance names
including derived ones, no axiom fallback); compiled against stock Lean, nothing changes.
`PARALEAN_FORK_HOOKS` selects per hook at run time (`0` = library workarounds; a list such as
`sync,noaxiom,instnames,collector`). Exports then build with the fork in Paralean mode, so
deriving handlers regenerate the canonical names. Results: [docs/fork-log.md](../../docs/fork-log.md).

## Layout

| file | role |
|---|---|
| `Paralean/Capture.lean` | per-command capture: membership, name classes, dependencies, capsule |
| `Paralean/InstName.lean` | canonical instance names (hook on the `declaration` elaborator) |
| `Paralean/Hooks.lean` | process-wide elaborator hooks (`simp` used-lemma record, instance names) |
| `Paralean/Fork.lean` | bridge to the fork's hooks (build-time and per-hook run-time selection) |
| `Paralean/Driver.lean` | capture driver, transparent prelude, commit of a file's groups |
| `Paralean/Store.lean` | content-addressed store; `audit/` holds rejected groups |
| `Paralean/Replay.lean` | source and kernel replay |
| `Paralean/Export.lean`, `Materialize.lean` | stock export, initializer modules |
| `Paralean/Encode.lean`, `Sha256.lean` | canonical encoding and IDs |
| `tools/Axioms.lean` | axiom dump used by `g4.py` |
| `fixtures/` | P1-only fixtures (F-async, N4/N5 inputs, conflict, duplicate instance) |
