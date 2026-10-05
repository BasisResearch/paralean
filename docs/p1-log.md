# P1 log — local declaration replay and stock export

Running log. Newest entries at the bottom.

## 2026-10-05

- Started from scratch (no prior P1 files). Read README, plan (P1), architecture,
  lean-integration, LEAN-NAMES, HARDENED and experiments.
- Toolchain `leanprover/lean4-nightly:nightly-2026-10-03` installed by P0; it reports
  `4.36.0-nightly-2026-10-03`, commit `193c3589a4fc16c4059261ab38cfa365eb24f323`.
- Project at `impl/p1/` (own lakefile, pinned `lean-toolchain`). Uses the stock
  nightly as a library; no fork.
- Probe findings (`impl/p1/tests/Probe.lean`, pinned nightly):
  - A library host must call `enableInitializersExecution` before `importModules
    (loadExts := true)`; otherwise the header import fails and every name in the file
    is unknown.
  - With `Elab.async := false`, `Frontend.processCommand` steps one command at a
    time. `Environment.getLocalConstantInfos` lists every constant, including async
    and realized ones; `constants.map₂` does not (it missed every `def`).
  - Reserved names (`fib.eq_1`, `ack.eq_def`, `match_1.eq_n`, `match_1.splitter`)
    appear in the *consumer's* command, as LEAN-NAMES predicts. Match equations are
    realized as **private** names (`_private.<Mod>.0.Probe.ack.match_1.eq_1`), so
    their spelling depends on the consumer's module.
  - `_private.<Mod>.0.PSigma.casesOn._arg_pusher` is a realized, non-reserved name
    keyed on a *base* constant. The classifier treats it as a scoped realized auxiliary.
  - `Probe.fib._unsafe_rec` is an unsafe auxiliary of an ordinary structural
    definition, so a blanket "reject unsafe members" rule would reject ordinary code.
    The kernel already forbids safe constants from using unsafe ones.
  - Effect detection: comparing extension-state pointers is noisy (`namespace`/`end`
    touch every scoped extension). Comparing the count of exported (`.private` level)
    entries per persistent extension gives a clean per-command touch set.
  - `import all` requires `module`, and a plain `import` cannot see another file's
    `private` names. So the exporter must rename private names whenever a consumer
    lands in a different output module (B→A→B forces this split).
- Renaming design chosen: a group whose public surface is empty (a `private` decl or an
  anonymous `instance`) is *relocated*. Its capsule is emitted inside `namespace
  _pl_<gid>` under its original namespace, with the `private` keyword blanked. Consumers
  get `open <ns>._pl_<gid>`. This needs no rewriting of proof bodies, and generated
  instance names become group-unique automatically.
- Implemented: `Sha256`, canonical `Encode` (hash-consed names/levels/exprs; constant refs
  as `base`/`self`/`dep pid`/`res base suffix`), `Model`, `Store` (CAS, re-hash on read),
  `Render` (capsule → source), `Capture` (per-command diff, classifier, deps, axioms,
  bypass options, relocation edits), `Driver` (transparent prelude), `Replay` (source,
  kernel, isolated).
- Identity normalization found necessary by replay mismatches:
  - hygienic **binder names** embed module + hash (`x._@.M.632112219._hygCtx._hyg.5`):
    encoded with macro scopes erased (kernel ignores binder names);
  - hygienic **universe parameter names** (`v._@...`) in `noConfusionType`: renamed
    injectively by position (`v._hyg_<i>`), an alpha-renaming;
  - unsafe recursive auxiliaries (`fib._unsafe_rec`) must be added via `mutualDefnDecl`;
  - re-realized reserved names (e.g. `ack.eq_1` needs `ack.match_1`) must be interleaved
    with the group's own declarations in one topological order.
- **Milestone: first round trip** (Probe1: def, theorem, enum inductive with deriving,
  structure, structural and WF recursion, simp-based proofs, private def, class, anonymous
  instance, simp lemma, mutual inductives, `rw` on WF equations): capture 14 groups;
  source replay 14/14 identical declaration IDs; kernel replay 14/14 accepted (88 decls,
  4 reserved names re-realized from the base group); isolated replay with exact
  dependencies 14/14.
- Exporter (`Paralean/Export.lean`): segment layout (cross-file dependency edges strictly
  raise the segment index, so the module graph is acyclic), capsule rendering with
  relocation, pinned `lean-toolchain`, clean stock `lake build`, then in-process
  `importModules` of the **built `.olean`s** and re-encoding of each group from that
  environment; the result must equal the stored declaration ID.
- Finding: under stock asynchronous elaboration, auxiliary proofs get different names
  (`aux_pos._proof_1_1` vs `_proof_1` synchronously). Capture runs synchronously, so
  exported modules pin `set_option Elab.async false`. This is still a stock build, but
  identity of `_proof_n` auxiliaries depends on the elaboration mode. The P0 interface
  must fix the mode, or the identity must be taken modulo auxiliary naming.
- **Milestone: first clean stock export** (Probe1, 14 groups incl. relocated `private def`
  and anonymous instance): stock `lake build` OK; 14/14 groups identical in the built
  oleans.
- B→A→B (`corpus/fixtures/crossws`): B's first capture rejects `helper_c` (`helper`
  unknown; stays a private draft). A then captures `helper` against B's published
  `helper_b`. B re-captures: the prelude defers A's group until B's file re-produces
  `helper_b` with the identical package ID, injects it mid-file (root scope), and then
  `helper_c` elaborates. Replay: source 3/3, kernel 3/3, isolated 3/3.
- **Milestone: B→A→B export**: two agent files → three modules `ws_b.B` → `ws_a.A` →
  `ws_b.B.Part2`; stock `lake build` OK; 3/3 groups identical in the built oleans.
- Corpus work (docs/p1-corpus.md by P0). Fixes found by running it:
  - workspace imports (`import Fixtures.F10SimpAttrDecl`) are satisfied by the transparent
    prelude and contribute their own base imports transitively;
  - section-local effects (`local notation`, `attribute [local …]`, `open scoped`) travel as
    capsule text and are never published; their constants are scaffolding;
  - `scoped` commands are never relocated (relocation would rescope them);
  - constants named in source but absent from the term (`simp [defeqLemma]`) are frontend
    deps (from `TermInfo`);
  - names with macro scopes need a component-array JSON encoding;
  - hygienic decl names are numbered per group in creation order;
  - imported base environments are cached per process (each `importModules` maps regions
    that are never freed: isolated replay hit 27 GB before, 1.6 GB after);
  - module system (F15, all of Mathlib): capsules carry the section header
    (`@[expose] public noncomputable meta section`) and the import lines as written; no
    relocation inside modules; same-file export segments use `public import all`;
  - in a `module`, imported theorems are axiom-shaped: the axiom audit uses Lean's
    `collectAxioms` (precomputed per-module data) for base constants;
  - export of a Mathlib file renames the module under the same root
    (`Mathlib.ParaleanExport.…`); the export lakefile reuses Mathlib's `.lake/packages`
    (`packagesDir`) so no network fetch happens; verification imports the built
    `.olean`s with explicit artifacts, as Lake does, because Lean's search path resolves a
    root package from the first directory containing it;
  - replay sessions use a module under the captured groups' root, and anonymous instances
    get their generated name pinned explicitly (`instance /-pl:gen-/ instFoo …`); Lean's
    generated instance names depend on the module root and on module-locality of the
    referenced constants.
- Negative fixtures: N1 (sorryAx), N2 (new axiom + dependent), N3 (skipKernelTC),
  N4 (changed target, via a contract pinned from a reference store), N5 (upstream
  revision: re-elaboration fails; the target contract would also differ), N6
  (native_decide auxiliary axiom), all rejected. A concurrent version conflict
  (two partitioned stores merged) excludes both heads from the prelude, rejects the
  consumer and makes export refuse the closure.
- Parent decisions received: `Elab.async` forced off everywhere (capture now *rejects* any
  command or scope that sets it); the F-async soundness fixture; transparent workspaces
  (Track B, after this gate).
- F-async (`impl/p1/fixtures/fasync/FAsync.lean`, `results/fasync*.log`):
  - kernel-only failure: a tactic assigns `True.intro` to the goal `1 = 2`; the
    elaborator does not type-check assignments, so only the kernel rejects it;
  - late-tactic failure: `simp` leaves an unsolved goal;
  - stock behaviour, **same under async on and off**: the failed theorem stays in the
    environment (after a kernel failure as an axiom-backed constant, after a tactic
    failure with a `sorryAx` proof). The next declaration that uses it elaborates
    **without an error of its own**; `#print axioms` then shows `[FA.kernelBad]` or
    `[propext, sorryAx]`. With async on, when the command returns the theorem is
    already visible as a `theorem` and no error has been reported yet; with async off
    the error is reported by the time the command returns;
  - (a) capture publishes neither bad theorem nor its user (elab error; unresolvable
    reference to an unpublished constant);
  - (b) a forged "worker says OK" publication of all four groups is rejected by the
    validator on independent grounds: kernel type mismatch, `sorryAx` in the
    axiom audit, and dependency on a rejected group. Kernel replay no longer needs
    source replay to name constants;
  - (c) cancellation (hook after N commands, and `SIGKILL` mid-Mathlib-file) leaves
    staged objects but no file record, so nothing is published.
- Classifier made provenance-based after the G2 comparison with P0's oracle (first try
  matched 771/1049 commands; it had hidden `alias`, `@[to_additive]`, `@[ext]`,
  notation and `initialize` names as "generated"). Now scoped = private, relocation
  names, internal names outside public roots, and instances that an anonymous
  `instance` or `deriving` generated. Result: 1026/1026.
- `initialize` materialization: groups with initializer effects (and their closure)
  are exported to a scratch Lake package, built with stock Lean and imported with
  explicit artifacts. Their constants map back to package identities. F10Use and F13Use
  now capture (the F13 consumer had aborted the host process before).
- Isolated replay retries each failure with the same-file prefix capsule: it fixes
  38/39 (all simp/attribute-state cases); the remaining one is a module-dependent
  literal.
- **Gate run (final):** see [p1-gate.md](p1-gate.md). Source replay 1224/1225, kernel
  1225/1225, isolated exact-deps 1186/1225 (fixtures 118/120 → G1 fixtures FAIL at 100 %;
  Mathlib 1068/1105 = 96.7 % → FAIL at 98 %; both PASS with the diagnosed file-prefix
  capsule: 120/120 and 1104/1105), G2 1026/1026, G3 pass, G4 22/22 builds with 1116/1142
  byte-identical groups in the built oleans, G5 6/6, G6 pass, F-async pass.
- **Track B (transparent workspaces)**, see [p1-transparent.md](p1-transparent.md):
  - `remote%` elaborator: receipt check, byte-exact published header, closure loaded
    from the store independent of imports, theorems statement-only with a
    receipt-backed placeholder proof, defs/instances/structures re-elaborated. The
    support modules were converted to the module system (`module`, `meta` section) so
    that Mathlib `module` projections can import the elaborator;
  - placement CRDT (RGA over publication records), canonical projection, working copies
    (publish/sync/pull), git projection with teammate-authored commits;
  - B→A→B through `remote%` in two copies: every projection file elaborates standalone;
    projection hashes identical in both copies and for concurrent inserts exchanged in
    both orders; `git diff` shows only the agent's drafts; export 3/3 identical;
  - 7/7 forged `remote%` uses rejected with errors (unknown ID, edited statement, other
    name, nested use, wrong key, missing receipt, conflicting local dependency);
  - 993 Mathlib groups (7 modules) as all-`remote%` projections: 0 errors, 0 proof
    objects read, 730 statement-only theorem loads, 220 full re-elaborations;
    ×1.22 local capture and ×1.60 stock sync `lean` (no speedup from skipping proofs;
    per-element overhead dominates).
- **Round 2** (user request: header meaning, visibility, collision renaming, namespaces,
  draft placement, G1 hook):
  - `remote%` header check: the declared name resolved in the current scope must be the
    loaded published member; the written statement is elaborated in the pre-load
    environment with the visibility hook suspended, and must be definitionally equal to
    the published statement (Lean's section-variable rules: needed + `include` +
    instance-implicit, or binders peeled for definitions). New forgery tests:
    wrong namespace and local-instance reinterpretation, both rejected (10/10 total);
  - visibility through name resolution (`Paralean/Visibility.lean`, reserved-name
    predicate and action registered at host start-up), replacing the text-scan prelude.
    A closed `isLoading ()` term was evaluated once by the compiler; it now takes the
    queried name;
  - rule-4 collision renaming (`renamesOf`, `renameText`): consistent in projection,
    loading, visibility, capture and export; four-copy exchange gives identical hashes;
    the rename arrives as the winner's commit; the export builds 3/3;
  - draft namespaces: machine-generated close/reopen blocks around elements; drafts
    re-split around new publications;
  - G1: `simp`/`simp_all` used-lemma hook (builtin-table wrapper, stock run first, full
    state restore; `saveState`/`restore` keep name generators, which had shifted
    `_proof_n` names and broken export identity until fixed); attribute-set rule for
    other tactics; effect targets limited to workspace constants (base-constant targets
    had split the export and lost a `register_option` import); `set_option`
    dependencies. Isolated replay 1186 → 1222/1225; fixtures 120/120; Mathlib 99.7 %.
  - `remote%` cost after the meaning check: ×2.5 local capture (was ×1.22), 0 errors over
    993 groups.
