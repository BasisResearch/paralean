# P0 running log

Phase P0 of [the plan](plan.md): pin the baseline and the interfaces. Times are UTC.
Machine: 32 cores, 123 GiB RAM, Linux 7.0 (x86_64). All builds, caches and temp
files are under `~` on `/data` (`TMPDIR=~/tmp`).

## 2026-10-05

### Toolchain

- `.deps/lean4` HEAD is `193c3589a4fc16c4059261ab38cfa365eb24f323` (tag
  `nightly-2026-10-03`), clean tree.
- elan: `elan toolchain install leanprover/lean4-nightly:nightly-2026-10-03` took 11 s.
  It reports `Lean (version 4.36.0-nightly-2026-10-03, x86_64-unknown-linux-gnu,
  commit 193c3589a4fc16c4059261ab38cfa365eb24f323, Release)`, and `Lean.githash`
  returns the same commit. Mathlib's `leanprover/lean4:nightly-2026-10-03` toolchain
  string resolves to this toolchain.
- Source build, first attempt: `cmake --preset release` failed with `Could NOT find
  LibUV`. The libuv runtime package is installed but the `-dev` package is not.
  Rather than modify the system with sudo, I built libuv v1.51.0 (the system
  version) from source into `~/p0-deps/libuv`. I removed the shared objects so Lean
  links it statically, then reran with
  `PKG_CONFIG_PATH=~/p0-deps/libuv/lib/pkgconfig`.
- Source build: `cmake --preset release && make -C build/release -j32`. Wall time
  8 min 45 s, peak RSS of a single process 1.93 GB, exit 0. `ldd` shows no libuv
  dependency.
- The source binary reports `Lean (version 4.36.0-pre, commit
  193c3589a4fc16c4059261ab38cfa365eb24f323, Release)`, and `Lean.githash` gives the
  same commit as elan. Only the version *string* differs, because the release
  workflow sets a special version description and the plain preset does not.
  **Consequence:** identity must key on the commit, never on `Lean.versionString`.
  The source binary loads the cache-built Mathlib `.olean` files without error.
- Pinned reference: `build/release/stage1` was copied to
  `~/p0-deps/lean-stock-193c3589` and made read-only. SHA-256:
  `lean 1a3c9d564b6c2c6ddffcbf106a25c92945d5c7a23c54a152437218eae43fc62c`,
  `lake ca81f0653a10dfaf4456d5e99aa0e29a5075b4efae29b0841f2c9c1d22a32b3f`,
  `leanc d077394f3c14ab85d36e1b0cf69a9bcfa5aff7d37f0f743cfc55a8b9373d986e`.

### Mathlib

- `.deps/mathlib`: fetched `0575336843263378752eeb5f4c75a612327768a2` from
  `mathlib4-nightly-testing` (depth 1). `lean-toolchain` =
  `leanprover/lean4:nightly-2026-10-03` (matches). All eight dependency checkouts match
  `lake-manifest.json` revisions.
- `lake exe cache get` **worked**: 8997 files in 47 s wall. `lake build --no-build`
  then reported all 18009 jobs up to date. `.lake/build/lib/lean` is 6.1 GB
  (9017 `.olean` files including dependencies). Reported to parent as usable by P1.
- Full local build started 04:05 in a separate copy, `.deps/mathlib-local`. It is
  the same checkout with every `.lake/build` and `.lake/packages/*/.lake` removed.
  It runs with the frozen source-built stock binary on `PATH` (no elan), via
  `lake build`. A sampler records aggregate RSS of the build's process tree every
  5 s.
- **Full local build: PASS.** Finished 04:23:19 UTC. `Build completed successfully
  (18009 jobs)`, 0 errors, 0 warnings. Wall time 18 min 39 s; 29,859 s user and
  2,236 s system CPU (8.9 CPU-hours, 2868 % average CPU). Peak RSS of a single
  process 3.03 GB. Peak aggregate RSS of the build tree 46.9 GB (p50 30.6 GB, p95
  40.9 GB, 5-s samples). Output: 8,999 `.olean` files, 1.75 GiB (Mathlib's own:
  8,593 files, 1.69 GiB); 53,986 `.olean*` files including `.olean.server` and
  `.olean.private`, 5.43 GiB; `.lake` 13 GB in total.
- **Cache vs local equivalence** (`results/p0/scripts/compare-oleans.py`): of
  26,993 `.olean*` data files in both trees, 26,984 are byte-identical except for the
  header's version field (bytes 7–0x28: `4.36.0-nightly-2026-10-03` vs `4.36.0-pre`;
  githash equal). Every `.olean` and `.olean.server` file matches. The 9 that differ
  are all `.olean.private`. Comparing constants (`DumpModule.lean`, name/kind/type
  hash/value hash) shows:
  - 6 of the 9 have identical constants and differ only in non-constant data;
  - 3 have one theorem whose proof term differs, with one or two more private
    `_simp_n`/`_abel_n` auxiliaries (`HomologicalComplex.mapBifunctorMapHomotopy.comm₁`,
    `Nat.Partrec.Code.evaln_mono._f`, `MonomialOrder.sPolynomial_decomposition`).
  All types agree everywhere. Rebuilding those modules locally is deterministic: the
  same bytes with `LEAN_NUM_THREADS` 1, 4 and 32, and the same sizes with the release
  binary as with the source binary. The cache difference therefore comes from the
  upstream CI environment; the exact cause is not identified. Conclusion: the cache
  is interface-equivalent (exported and server data identical) but not proof-term
  identical. The gate therefore rests on the real local build, not the cache.
- The release binary **rejects** the source build's own `Init.olean` (`incompatible
  header`), because headers store the version string. Mixing the release and source
  toolchains on one set of `.olean` files needs
  `-DLEAN_SPECIAL_VERSION_DESC=nightly-2026-10-03`.
- **Tests: PASS.** `lake test` (MathlibTest driver) on the local build: 416 test
  modules built, 0 failures, 0 warnings, wall 2 min 15 s, peak RSS 6.85 GB.
  Logs: `results/p0/mathlib-{build,test}.log.gz`, RSS trace
  `results/p0/mathlib-build-rss.txt`.
- Reported to the parent twice: once the cache tree was usable, and after the local build.

### Boundary experiments

- `experiments/run.sh` with elan `v4.34.1` (the recorded baseline; no earlier log
  had been kept), elan `nightly-2026-10-03`, and the frozen source build: all three
  pass 14/14 checks with identical output apart from the `--version` line. Runtime
  is about 2.2 s. **No behavioural difference** from 4.34.1. Logs are in
  `results/p0/experiments-*.log`.

### Extraction corpus

- Defined in [p1-corpus.md](p1-corpus.md). 16 fixture families (21 files) under
  `corpus/fixtures` (stock-Lean Lake package) plus `corpus/mathlib-fixtures`, six
  negative fixtures, and 18 fixed Mathlib modules (`corpus/modules.txt`).
- `corpus/tools/CommandDecls.lean` is a reference oracle. It elaborates a file
  command by command (synchronously) and records each command's added constants with
  name classes and its persistent-extension deltas. Output goes to
  `corpus/reference/`.
- Findings that feed the interface freeze:
  1. Auto-named instances (`instInhabitedBoxNat`) and deriving outputs
     (`instReprBox`) are **public** under Lean's spelling classifier
     (`isAutoDeclOrPrivate_Internal`). LEAN-NAMES.md treats `instFooNat` as
     generated. The classifier must use capture-time provenance.
  2. Consumers realize constants under `_private.*` spellings
     (`….match_1.eq_1`, `….splitter`, `….casesOn._arg_pusher`) and `*._unary.induct`.
     WF definitions realize `eq_def` eagerly inside the defining command. Correction
     after the P1 notes: `isReservedName` does cover the private match equations and
     splitters. The first oracle run tested `isPrivateName` first and mislabelled them;
     it is fixed and rerun. `_unary.induct` and `_arg_pusher` still need provenance
     ("created by `realizeConst`").
  3. Eager inductive auxiliaries (`casesOn`, `noConfusion`, `ctorIdx`, `injEq`,
     `_sizeOf_inst`, …) are scoped-generated under Lean's classifier.
  4. Every Mathlib file at this pin is a `module` with `public import`,
     `@[expose] public section` and `meta section`. In a module, `meta def` outside a
     public section gets a private name. Capsules must carry visibility state.
  5. `native_decide` now emits an auxiliary **axiom**
     `<decl>._native.native_decide.ax_1_1`. Under `debug.skipKernelTC`, an ill-typed
     theorem is accepted and `#print axioms` reports **no axioms**. Stock Lean
     accepts all six negative fixtures, with at most a warning.

### Oracle run (final)

`MATHLIB=.deps/mathlib-local bash corpus/run-oracle.sh`: 39 inputs, 0 errors.
Fixtures: 167 commands, 101 groups, 9,631 source bytes, 36 reserved and 13
scoped-private constants. Mathlib M01–M18: 1,409 commands, 1,046 groups, 243,082
source bytes, 161 reserved and 283 scoped-private constants.

### Interface freeze

- `docs/p0-interfaces.md`, draft v0: encoding, base manifest, names, groups, frontend
  effects, capsules, receipts, revisions, typed store, markers, certificates,
  snapshots, catalogue and fencing. The P0 findings are folded in: provenance
  classification, canonical member numbering, both the version string and the
  commit pinned, and interface-level replay equality.
- Parent addition (transparent workspaces), added as §11: publication records
  carrying the file path, anchor, Lamport time and author; `remote%` and its four
  checks; canonical rendering; a per-file RGA sequence with tombstones; Lamport
  collision renaming (target names keep the owner rule); the git projection. §11.5
  changes the protocol (collision errors become deterministic renames) and is
  **not** covered by the existing proofs (OPEN-15).
- Elab.async decision (§4.3): capture **also** pins `Elab.async = false` through
  `BaseManifest.options`. Identity is independently made invariant to scoped
  spellings and `addDecl` order by canonical member numbering. OPEN-14 tracks
  dropping the pin.
- P1's `p1-interface-notes.md` folded in: spelling normal form, binder macro scopes
  erased, `frontendDeps`, effect groups for `attribute` commands (resolves OPEN-5's
  default), and package-ID pinning accepted pending OPEN-22/23.
- 23 open decisions are marked.

### Store choice and interface triage (later on 2026-10-05)

- [store.md](store.md): FoundationDB for metadata (markers, revisions, receipts,
  certificates, catalogue, fence, tokens, target records), S3 for payloads, payload
  written and hash-verified before any metadata names it. etcd is rejected on size;
  DynamoDB is the fallback under the same mapping. The refinement argument maps the
  modelled store to one abstract replica (`W = R = {{σ}}`), each committed
  transaction to a fixed sequence of model steps, and paginated scans to model scans
  through grow-only key spaces. It states what it does not cover: unresolved unknown
  commit outcomes, deletion and GC, backup restore, cross-region, and the stores' own
  guarantees. OPEN-9 is marked resolved pending sign-off.
- `Elab.async`: the v1 position is now P1's measured decision (off everywhere, not
  overridable; ×1.39 wall on M01–M18, ×2.2 worst file). OPEN-14 becomes the fork
  target of restoring asynchronous interactive elaboration.
- §13 triage: OPEN-1, 2, 10, 18 (marker bytes, if P2 stores §11.1 markers), 22, 23
  and 24 block P2, each with a proposed resolution awaiting a decision. OPEN-26 is
  new: a rendered collision rename is not committable under Groups' `buildable` and
  `current`. Open decisions: 23 (OPEN-8, 9 and 15 resolved; OPEN-26 added).

### Sign-off (later on 2026-10-05)

The user signed off: OPEN-9 (store.md, self-hosted FoundationDB plus an
S3-compatible payload store; option (a), a consensus database for the few
coordinated records), OPEN-24 (auto-named instances are public and collide, with
stable hashed names), OPEN-14 (`Elab.async` off everywhere in v1), and OPEN-1, 2,
10, 18, 22 and 23 as proposed in [p0-interfaces.md](p0-interfaces.md) §13. P1
must adopt OPEN-22 (`self <memberIdx>`), OPEN-23 (group-ID kernel deps) and
OPEN-24 (instance names) and re-measure G2/G4.

## Gate status

| Item | Status | Numbers |
|---|---|---|
| Toolchain pinned (source build = elan, same commit) | PASS | elan and source report `193c3589…`; source build 8 min 45 s; frozen copy `~/p0-deps/lean-stock-193c3589` |
| Baseline Mathlib build (local, from scratch) | PASS | 18,009 jobs, 0 errors, 18 min 39 s, peak RSS 3.03 GB per process / 46.9 GB aggregate, `.olean` 1.75 GiB (5.43 GiB all parts) |
| Mathlib tests | PASS | `lake test`: 416 modules, 0 failures, 2 min 15 s |
| `cache get` | worked | 8,997 files, 47 s; interface-equivalent to the local build (all exported/server data identical; 3 private proof terms differ) |
| Boundary experiments on the pinned nightly | PASS | 14/14, output identical to 4.34.1 |
| Extraction corpus | PASS (defined; stock baseline) | 21 fixture files + 18 Mathlib modules, oracle 0 errors; 6 negatives; gates G1–G6 set for P1 |
| Protocol verification | PASS (unchanged) | `verification/` not modified; recorded results stand (verification/results/README.md) |
| Store choice and refinement argument | PASS (signed off 2026-10-05) | `docs/store.md`: FoundationDB metadata, S3 payloads, payload before metadata; refinement to one abstract replica with stated exclusions; resolves OPEN-9 |
| Interface freeze | P2-blocking decisions made | `docs/p0-interfaces.md`: all 7 OPENs that block P2 decided 2026-10-05; the remaining OPENs are P1/P3/P5 work. P1 must adopt OPEN-22/23/24 and re-measure G2/G4 |
