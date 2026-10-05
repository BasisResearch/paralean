# P1 gate report: local declaration replay and stock export

Date 2026-10-05. Implementation: `impl/p1/` (Lean 4 library and CLI on the stock nightly
`193c3589`, no fork). Corpus and thresholds: [p1-corpus.md](p1-corpus.md) (P0).
Notes: [interface findings](p1-interface-notes.md), [fork hooks](p1-fork-hooks.md),
[running log](p1-log.md).

## Reproduce

```sh
impl/p1/scripts/bootstrap.sh --mathlib   # elan toolchain (checked: 193c3589), fixtures, paralean,
                                         # Mathlib at the versions.json pin + `lake exe cache get`
impl/p1/scripts/run-all.sh               # every gate; logs in impl/p1/results/
```

Everything lives in the repository (`.runs/p1`, `.deps/mathlib`); every path can be
overridden, and scripts stop with a message when a dependency is missing. Details:
[impl/p1/README.md](../impl/p1/README.md). No Mathlib build is needed: the gate uses the
pinned cache.

**Two runs are reported.**

- **Local (this report's numbers unless marked).** macOS arm64, elan toolchain,
  Mathlib from `lake exe cache get`, the final binary (canonical instance names,
  encoding v2 with canonical numbering and group-ID pins, audit namespace). Logs:
  `impl/p1/results/local-darwin/`. The machine was shared with other jobs (load 40–90),
  so its times are not comparable.
- **AWS (first gate, marked *aws*).** Linux x86-64 (`aws-dev`), elan toolchain, the
  previous binary. Logs: `impl/p1/results/*.log`. Its timing and `Elab.async` cost
  figures below are from that run.

**Toolchain provenance.** Both runs used elan's `leanprover/lean4-nightly:nightly-2026-10-03`.
The corpus protocol (p1-corpus.md, G4) names P0's frozen source build
`~/p0-deps/lean-stock-193c3589` instead. Both are commit `193c3589`; only the version string
in `.olean` headers differs (p0-log.md), and the release binary rejects the source build's
`Init.olean`. No run used the frozen binary. To do so, set `PARALEAN_SYSROOT` and
`PARALEAN_LAKE` to it and use a Mathlib built by it (`impl/p1/README.md`).

## Verdict

| Gate | Status | Measured (local run) |
|---|---|---|
| G1 replay, fixtures (100 % required) | **PASS** | per group in a fresh session with exact dependencies: 120/120 (core 103, F14 3, F15 7, F16 7; the G4 probe fixture adds 8/8). *aws*: 120/120. The first round (exact dependencies only) did **not** pass: 118/120, failing on F10. It passed only after round 2 added the `simp` used-lemma hook and the attribute-set rule (below); those were added after the first measurement |
| G1 replay, Mathlib (≥ 98 %, 0 silent) | **PASS** (99.9 %) | 1104/1105. The remaining group is M08 `by_cases!`, a module-dependent literal, with a diagnostic. *aws*: 1102/1105; the two `grind` groups that failed there (M03, M16) now pass, consistent with canonical numbering ignoring auxiliary spellings (their isolated proof terms had differed). Round 1 on *aws*: 1068/1105 = 96.7 %, a FAIL before the hook. 0 silent failures |
| G1 kernel | PASS | stock kernel accepts 1225/1225 transported groups; reserved names re-realized, never transported |
| G2 membership and classes | PASS (with 5 explained instance spellings) | auto-named instances and deriving outputs are now **public** (p0-interfaces.md §3.1). 1122/1127 commands' public sets equal the oracle's; the 5 differences are all instance spellings (below). 0 reserved names published; 0 commands split; 0 multi-command groups; every group without a public name has an anchor. *aws* (old classification, instances excluded): 1026/1026 |
| G3 capsule size | PASS | fixtures: max capsule 390 B (≤ 4 KiB). Mathlib: max 2,868 B (≤ 64 KiB); per-module p50 ratio ≤ 3.8, p95 ≤ 9.8; 0 groups above the p95 bound |
| G4 export build | PASS (build); identity 97.7 % | 23/23 exports build with stock `lake build` (fixtures, F14 as 3 modules, F15, F16, G4 probe, 18/18 Mathlib modules). 1116/1142 groups re-encoded from the **built `.olean`s** equal the stored group ID; the 26 others are module-dependent literals (diagnosed). `#print axioms`: 1445/1448 public members have exactly the reference build's axiom set, 0 differ; the 3 others are M13's `@[to_dual]` names derived from canonical instance names, which the reference does not contain (G2 below). Source/line mappings: 5/5 diagnostics of the exported modules resolve to the agent file and line (100 %), and all 5 match a stock diagnostic of the agent file at that line (4 distinct lines). The corpus itself produces no diagnostics on accepted code; the 5 come from the G4 probe |
| G5 negatives | **PASS** | 6/6 rejected for the required reasons, N3 by the validator's kernel re-check of the audit copy. **0 staged**: rejected groups are written only to the store's `audit/` namespace, never to the publishable `objects/`/`meta/` (per negative: publishable objects 0, audit objects 1–2). *aws*: rejected groups were kept beside published ones (deviation, now fixed) |
| G6 B→A→B | PASS | (a) `helper_c` fails ("Unknown identifier `helper`"), no group published; (b) A's group pins B's `helper_b`, `helper_c` pins A's; (c) export = 3 modules `ws_b.B → ws_a.A → ws_b.B.Part2`, acyclic, stock build OK, 3/3 identical |
| F-async soundness | PASS | (a) neither bad theorem nor its user is published; (b) forged publication rejected by the validator independently; (c) a capture cancelled after 4 commands, or `SIGKILL`ed 20 s into Mathlib.Order.Basic, leaves 0 objects (`results/local-darwin-cancel.log`; *aws*: 2 and 142 orphaned, unpublished objects); (d) below |
| Instance collisions | PASS | `instance : Inhabited (Nat × String × Bool)` in two workspaces → the same canonical name → `version-conflict` after merging, and export refuses; in one workspace → `instance name collision` error (`impl/p1/fixtures/instdup`) |

**Feasibility:** command-granularity capture, content-addressed storage, stock-kernel
replay and clean stock export work on an 18-module Mathlib sample (1,105 groups) and the
fixtures, and G1–G6 pass. With the `simp` used-lemma hook and the attribute-set rule,
exact-dependency capsules suffice for 1224 of 1225 groups. One class remains open:
module-dependent name literals in `initialize`-style bodies (26 groups whose identity
cannot be module-independent, and M08's isolated replay).

### G2: instance spellings

Capture names an anonymous `instance` `instFoo…_<8 hex>` (p1-interface-notes.md §6) and
records the stock spelling, which the comparison maps back. 78 anonymous instances in the
corpus were named this way; all are public. The five commands whose public sets still
differ from the oracle's:

- M13 L382, L593, L786: `@[to_dual]` on an anonymous instance. The dual instance's name is
  translated from the base's canonical name (`Pi.instMinForall_d560181b` from
  `Pi.instMaxForall_d560181b`), where the oracle has the translation of the stock name.
  The derived name is a function of the base name, so it collides exactly when the base
  does.
- M16 L677, L770: stock Lean named these `instTransTransGen_mathlib_1` and
  `instTransReflTransGen_1` because an earlier instance of the file had taken the
  unsuffixed name. With canonical names the earlier instance is `…_624233da`, the later
  `…_0e2330ee`: the environment-dependent `_1` disappears, which is the point of the
  scheme.

### G4: axioms and source mappings

`scripts/g4.py` (with `tools/Axioms.lean`) compares the axioms of every public member of
each export, as `#print axioms` reports them (`collectAxioms`), with the reference build of
the agent's file: the corpus fixture package, a stock compile of F16, or the Mathlib cache.
It then runs stock `lean` on every export module and maps each diagnostic back through the
group header (`-- paralean group <id> (<ws>/<file>:<start>-<end>)`) to the agent's file and
line. The corpus's accepted code produces no diagnostics, so the mapping check uses a
probe fixture (`impl/p1/fixtures/diagmap`) with five deprecation and unused-variable
warnings, including one in a multi-line command.

## Per-set results (local run; *aws* in `impl/p1/results/summary.md`)

| set | groups | source replay | kernel replay | isolated (exact deps) | export | identical in stock oleans | capsule B median / p95 / max |
|---|---|---|---|---|---|---|---|
| core F01–F13 | 103 | 103/103 | 103/103 | 103/103 | OK | 81/85 (+18 effect-only) | 222 / 316 / 390 |
| F14 B→A→B | 3 | 3/3 | 3/3 | 3/3 | OK | 3/3 | 202 / 227 / 227 |
| F15 module | 7 | 7/7 | 7/7 | 7/7 | OK | 6/6 (+1) | 195 / 298 / 298 |
| F16 Mathlib attrs | 7 | 7/7 | 7/7 | 7/7 | OK | 6/6 (+1) | 215 / 334 / 334 |
| G4 probe (diagmap) | 8 | 8/8 | 8/8 | 8/8 | OK | 7/7 (+1) | — |
| M01–M18 | 1,105 | 1104/1105 | 1105/1105 | 1104/1105 (*aws* 1102) | 18/18 OK | 1020/1042 (+63) | per module in `results/local-darwin/summary.md` |

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

Remaining in the local run (1/1225): M08 `by_cases!`, a module-dependent literal; no
capsule fixes it.

The *aws* run also had M03 `ascFactorial_eq_ascFactorialBinary` and M16
`bicompl_map_eq_of_injective` (both `grind`; the file-prefix capsule fixed them). With
encoding v2 they replay with exact dependencies. The likely reason is that their isolated
proof terms differed only in the spelling of scoped auxiliaries, which v2 no longer
hashes (inferred from the change, not separately diffed). A `grind` used-lemma record
(fork-hooks item 11) is still the exact fix for `grind` dependencies.

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
- (c) Capture writes nothing until the file is committed. A capture cancelled after 4
  commands and a capture `SIGKILL`ed 20 s into Mathlib.Order.Basic leave 0 objects, 0
  metadata and 0 file records (local). The *aws* run, before buffering, left 2 and 142
  orphaned objects without a file record (unpublished, but staged).

## Cost of `Elab.async := false` (*aws*, stock `lean`, best of 3)

Fixtures F01–F16 and FAsync: 5.5 s → 5.9 s wall. Mathlib M01–M18: 11.7 s async → 16.3 s
sync wall (×1.39); worst case M18 0.77 s → 1.68 s (×2.2). Total CPU time goes down
(24.6 s → 22.4 s). Per-file data: `results/async-cost.tsv`.

## P1 costs (*aws*)

Capture of M01–M18: 20.8 s, versus 16.3 s for stock synchronous `lean` (×1.28, including
encoding and the axiom audit). Whole-module source replay: 50.0 s (×3.1). Kernel replay:
≤ 0.12 s per module. Export build: 1.6–5.7 s per Mathlib module, against the pinned
checkout's packages, with no network.

## Deviations from the corpus protocol

- Builds use the elan toolchain `leanprover/lean4-nightly:nightly-2026-10-03` (commit
  `193c3589`), not P0's frozen binary path (see "Toolchain provenance").
- Publication happens per file capture: one file record at the end. The protocol's
  per-group receipts and acknowledgements are P2/P3.
- G1 fixtures passed only in round 2, after the `simp` hook and the attribute-set rule
  were added in response to the round-1 failures. The thresholds were not changed.
- Derived instances (`deriving`) keep the deriving handler's spelling; only anonymous
  `instance` commands get the canonical OPEN-24 name. Renaming derived instances needs
  the fork (fork-hooks item 14).
- `Elab.async`: exports pin it off (OPEN-14). An experiment exporting the core fixtures
  without the pin (`results/local-darwin/core-async-export.log`) verifies 79/85 groups:
  the 4 module-dependent groups as usual, plus 2 whose proof auxiliaries are spelled
  `_proof_1_1` under async elaboration. Group identity no longer depends on those
  spellings (canonical numbering), but the export verifier still finds scoped members by
  spelling, so OPEN-14 also needs position-based matching there.
