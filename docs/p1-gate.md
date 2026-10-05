# P1 gate report: local declaration replay and stock export

Date 2026-10-05. Implementation: `impl/p1/` (Lean 4 library and CLI on the stock nightly
`193c3589`, no fork). Corpus and thresholds: [p1-corpus.md](p1-corpus.md) (P0).
Reproduce with `impl/p1/scripts/run-all.sh`. Logs are in `impl/p1/results/` (`summary.md`,
`g2.txt`, `stats-*.txt`, `negative.log`, `fasync*.log`, `async-cost.tsv`).
Notes: [interface findings](p1-interface-notes.md), [fork hooks](p1-fork-hooks.md),
[running log](p1-log.md).

## Verdict (round 2, after the `simp` hook; first-round numbers are in the log)

| Gate | Status | Measured |
|---|---|---|
| G1 replay, fixtures (100 % required) | **PASS** | per group in a fresh session with exact dependencies: 120/120. The `simp` used-lemma hook plus the attribute-set rule (see below) closed the 2 F10 gaps |
| G1 replay, Mathlib (≥ 98 %, 0 silent) | **PASS** (99.7 %) | per group, exact dependencies: 1102/1105. The 3 remaining groups carry diagnostics: 2 `grind` proofs (fixed by the file-prefix capsule) and M08's module-dependent literal. 0 silent failures |
| G1 kernel | PASS | stock kernel accepts 1225/1225 transported groups; 41 reserved names re-realized, never transported |
| G2 membership and classes | PASS | 1026/1026 commands' public sets equal the oracle after the provenance corrections; 0 reserved names published; 0 commands split; 0 multi-command groups; every group without a public name has an anchor |
| G3 capsule size | PASS | fixtures: max capsule 390 B (≤ 4 KiB); per-group capsule/command ratio p50 ≤ 5.5 and p95 ≤ 6.6. Mathlib: p50 1.5–3.8 (≤ 4), p95 2.1–9.8 (≤ 16), max 2,868 B (≤ 64 KiB), total 0.53 MB = 2.2× source (≤ 6×); 0 groups above the p95 bound |
| G4 export build | PASS (build); identity 97.7 % | 22/22 exports build with stock `lake build` (21/21 fixture files, F14 as 3 modules; 18/18 Mathlib modules). Of declaration groups re-encoded from the **built `.olean`s**, 1116/1142 are byte-identical to the stored declaration ID. All 26 mismatches are `initialize`/`register_simp_attr`/local-syntax quotation bodies with module-dependent name literals (diagnosed) |
| G5 negatives | PASS (with one deviation) | 6/6 rejected for the required reasons, N3 by the validator's kernel re-check. Deviation: rejected groups are kept in the store as unpublished audit objects ("0 staged" is not met literally) |
| G6 B→A→B | PASS | (a) `helper_c` fails ("Unknown identifier `helper`"), no group published; (b) A's group pins B's `helper_b` package ID, and `helper_c` pins A's; (c) export = 3 modules `ws_b.B → ws_a.A → ws_b.B.Part2`, acyclic, stock build OK, 3/3 identical |
| F-async soundness | PASS | (a) neither bad theorem nor its user is published; (b) forged publication rejected by the validator independently; (c) cancelled or killed capture publishes nothing; (d) recorded below |

**Feasibility:** command-granularity capture, content-addressed storage, stock-kernel
replay and clean stock export work at Mathlib scale on this corpus, and G1–G6 pass (G5
with the audit-storage deviation below). With the `simp` used-lemma hook and the attribute-set rule, exact-dependency
capsules suffice for 99.8 % of groups. Two classes remain open: `grind` (2 groups, which
need a `grind` lemma record) and module-dependent name literals in `initialize`-style
bodies (26 groups; identity cannot be module-independent).

## Per-set results (final run)

| set | groups | source replay | kernel replay | isolated (exact deps) | export | identical in stock oleans | capsule B median / p95 / max |
|---|---|---|---|---|---|---|---|
| core F01–F13 | 103 | 103/103 | 103/103 | 103/103 | OK | 81/85 (+18 effect-only) | 224 / 333 / 390 |
| F14 B→A→B | 3 | 3/3 | 3/3 | 3/3 | OK | 3/3 | 202 / 227 / 227 |
| F15 module | 7 | 7/7 | 7/7 | 7/7 | OK | 6/6 (+1) | 195 / 298 / 298 |
| F16 Mathlib attrs | 7 | 7/7 | 7/7 | 7/7 | OK | 6/6 (+1) | 215 / 334 / 334 |
| M01–M18 | 1,105 | 1104/1105 | 1105/1105 | 1102/1105 | 18/18 OK | 1020/1042 (+63) | per module in `results/summary.md` |

"Source replay" re-elaborates the closure's capsules in one session and requires the
identical declaration ID. That is stronger than G1's interface equality: it covers
names, classes, types, all values including proofs, and exact dependency IDs. "Kernel
replay" adds the *stored* terms to a base kernel environment with `addDeclCore` and
audits axioms. "Isolated" replays each group's exact closure in a fresh session.
Groups count every command that adds a constant or a frontend effect. P0's oracle
counts only commands adding constants (101 fixtures and 1,046 Mathlib groups); the
extra groups are effect-only (`attribute`, module docs, notation).

## Cases requiring larger source capsules

Round 1 (exact dependencies only) had 39 isolated failures: 22 roots and 17 cascades. 21
of the roots were `simp`/`grind` uses of `@[simp]`/`@[grind]` lemmas proved by `rfl`,
which never appear in the proof term. Round 2 closes them with two dependency sources
(`impl/p1/Paralean/Hooks.lean` and `Capture.lean`):

- **`simp`/`simp_all` used-lemma record** (hook). A process-wide builtin wrapper runs the
  stock elaborator unchanged, replays the same call on a full state snapshot to read
  `stats.usedTheorems`, and restores the stock post-state exactly. Export identity is
  verified unchanged. Capture turns the recorded lemmas into frontend dependencies.
- **Attribute-set rule** for tactics without a lemma record (`simpa`, `dsimp`, `grind`,
  `norm_num`, …): such a command depends on the same-file groups that registered
  simp/grind-set lemmas.
- Also fixed: effect groups with members (e.g. `compile_inductive%`) register their
  workspace targets, and `set_option X` depends on the group that declared `X` (or on the
  initializer groups, for trace classes).

Remaining (3/1225), all diagnosed:

- M03 `ascFactorial_eq_ascFactorialBinary` and M16 `bicompl_map_eq_of_injective`: both
  `grind`; the proof terms differ in isolation; the file-prefix capsule fixes them. An
  exact fix needs a `grind` used-lemma record (fork-hooks item 11).
- M08 `by_cases!`: module-dependent literal; no capsule fixes it.

## Unsupported frontend effects (diagnosed, never guessed)

| Effect | Where | Groups | Handling |
|---|---|---|---|
| module-dependent name literals in bodies (`initialize`, `register_simp_attr`, `register_option`, quotations of local syntax) | F10, F13, M17, M08 | 26 | stated in `unsupported:module-dependent-literal` (flagged at capture for 23; the other 3, the F13 `IO.Ref`/trace-class/option initializers, are flagged only by export verification). Builds and runs, but its declaration ID differs per module |
| `initialize` effects through a same-module prelude | F10Use, F13Use | consumers | **supported by materialization**: initializer groups are built as stock modules and imported. Without it, the consumer fails, and `#f13_check` aborts the host process (`[init]` constant evaluated in its own module) |
| `Elab.async` changes `_proof_n` spelling | all | — | pinned off; any change is rejected (`reject:async-override`) |
| mixed private/public commands; `scoped` anonymous instances | none in corpus | 0 | `unsupported:mixed-visibility`; scoped commands are not relocated (`info:scoped-not-relocated`) |
| section `attrs` other than `expose`; `omit` of instance binders | none in corpus | 0 | `unsupported:section-attrs` |

## F-async (soundness)

Fixture `impl/p1/fixtures/fasync/FAsync.lean`. `FA.kernelBad : 1 = 2` is closed by a
tactic that assigns `True.intro`; the elaborator never type-checks the assignment, so
only the kernel rejects it. `FA.lateBad` fails in `simp`. Each has a user in the same
file.

- (d) Stock behaviour is the same under async on and off. The failed theorem stays in
  the environment: after a kernel failure it is re-added as an axiom
  (`AddDecl.lean:189-214`, `addAsAxiom`), and after a tactic failure it gets a
  `sorryAx` proof. The next declaration that uses it elaborates **without any error
  of its own**, and `#print axioms` shows `[FA.kernelBad]` or `[propext, sorryAx]`.
  With async on, when each command returns the theorem is already visible as a
  `theorem` and no error has been reported yet (`AddDecl.lean:160-175` publishes the
  signature before the kernel task runs). With async off the error has been
  reported by then.
- (a) Capture publishes only `FA.fine` and two frontend groups. All four bad
  declarations are rejected (elaboration error; reference to an unpublished
  constant).
- (b) A forged publication of all four (with the ill-typed and `sorryAx` terms the
  worker held) is rejected by the validator on independent grounds: kernel type
  mismatch, `sorryAx` in the axiom audit, and dependency on a rejected group. No
  worker signal is consulted. Kernel replay names constants by identity when source
  replay fails, so it is independent of source replay.
- (c) Cancellation after N commands, and `SIGKILL` mid-file on Mathlib.Order.Basic,
  leave 2 and 142 staged objects respectively but no file record, so nothing is
  published.

## Cost of `Elab.async := false` (stock `lean`, best of 3)

Fixtures F01–F16 and FAsync: 5.5 s → 5.9 s wall. Mathlib M01–M18: 11.7 s async → 16.3 s
sync wall (×1.39); worst case M18 0.77 s → 1.68 s (×2.2). Total CPU time goes down
(24.6 s → 22.4 s). Per-file data: `results/async-cost.tsv`.

## P1 costs

Capture of M01–M18: 20.8 s, versus 16.3 s for stock synchronous `lean` (×1.28, including
encoding and the axiom audit). Whole-module source replay: 50.0 s (×3.1). Kernel replay:
≤ 0.12 s per module. Export build: 1.6–5.7 s per Mathlib module, against the pinned
checkout's packages, with no network.

## Deviations from the corpus protocol

- Builds use the elan toolchain `leanprover/lean4-nightly:nightly-2026-10-03` (commit
  `193c3589`), not P0's frozen binary path.
- Publication happens per file capture: one file record at the end. The protocol's
  per-group receipts and acknowledgements are P2/P3.
- G4's `#print axioms` comparison with the oracle build was not run separately.
  Byte-identical groups have identical axioms; the 26 differing groups are listed above.
