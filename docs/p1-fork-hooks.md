# P1: places where the fork needs a hook

P1 runs on the stock nightly (`193c3589`) as a library, with no patches. Each item below
is a workaround P1 uses today and the exact Lean source location where a fork hook would
replace it. Paths are relative to `src/` of `.deps/lean4` at the pinned commit.

| # | Need | P1 workaround | Fork location |
|---|---|---|---|
| 1 | `Elab.async` forced off, not overridable (parent decision) | host sets `Elab.async := false`; capture **rejects** any command or scope that changes it; exports pin `set_option Elab.async false` | option `Lean/CoreM.lean:35`; default forced on in `Lean/Elab/Frontend.lean:291-292` (`Elab.async.setIfNotSet opts true`) and `Lean/Server/FileWorker.lean:432-433`; `set_option` elaboration should reject the name |
| 2 | Capture at command boundaries, including nested `realizeConst` | diff `Environment.getLocalConstantInfos` before/after each `Frontend.processCommand`; extension touches by exported-entry counts | `Lean/AddDecl.lean` `addDecl` (lines ~101-215) and `Lean/Meta/Basic.lean:2787` `realizeConst`; a per-command collector would avoid the O(n) diff |
| 3 | Failed declarations must not be usable downstream | capture refuses: elab errors reject the command; consumers fail to encode a reference to an unpublished constant; the validator re-checks | `Lean/AddDecl.lean:189-214` (`addAsAxiom`): after a kernel failure the theorem is re-added as an **axiom** "to avoid follow-up errors", so the next declaration elaborates without error. Under async, `AddDecl.lean:160-175` publishes the signature (`setEnv async.mainEnv`) before the kernel task runs |
| 4 | `_proof_n` names independent of elaboration mode | pin async off | `Lean/CoreM.lean:75` `DeclNameGenerator` (`parentIdxs`/`mkChild`) gives `_proof_1_1` in async branches |
| 5 | Generated instance names independent of module root | capsules spell the generated name explicitly (`instance /-pl:gen-/ instFoo …`); replay modules keep the agent root; exported Mathlib files are renamed under the `Mathlib.` root | `Lean/Elab/DeclNameGen.lean:219-237` `mkBaseNameWithSuffix` (project suffix from `getMainModule.getRoot` and module-locality of referenced constants) |
| 6 | Module-independent bodies for `initialize`/local-syntax quotations | detected and reported (`unsupported:module-dependent-literal`); identity of such groups cannot be module-independent | name literals produced by hygiene (`_@.<Module>.<hash>._hygCtx`) in `initialize` expansion and syntax quotations; a fork could key hygiene contexts by group instead of module |
| 7 | Private names visible across export segments | relocation into `<ns>._pl_<gid>` for non-module files; `public import all` for module files | `Lean/Modifiers.lean:23` `mkPrivateName` / `Lean/PrivateName.lean:29` |
| 8 | `initialize` effects through transparent imports | consumers of initializer groups import a stock-built module (materialization) | `Lean/Compiler/InitAttr.lean:198-203` `runInitAttrs` only for imported modules; evaluating an `[init]` constant from the same module aborts the host process (uncaught C++ `lean::exception` in F13InitUse) |
| 9 | Re-realize reserved names in a validator | `executeReservedNameAction` in the source-replayed frontend environment, then `addDeclCore` | `Lean/ReservedNameAction.lean:38`; realization needs elaborator extensions (`WF.eqnInfoExt`, `Structural.eqnInfoExt`, matcher info), so a kernel-only validator cannot do it |

## Hooks implemented in the P1 host (round 2)

These are installed process-wide at host start-up, in Lean's builtin tables, so
nothing is imported into user environments. The fork would make them native.

| # | Hook | P1 implementation | Fork location |
|---|---|---|---|
| 10 | Record the lemmas `simp`/`simp_all` actually used (G1: `rfl` `@[simp]` lemmas never appear in the term) | `Paralean/Hooks.lean`: `tacticElabAttribute.addBuiltin` puts a wrapper ahead of `evalSimp`/`evalSimpAll`. The stock elaborator runs first, unchanged. The same call is then replayed on a full snapshot of the Core/Meta/Term/Tactic state (including name generators and caches, which `saveState`/`restore` keep) to read `stats.usedTheorems`. The post-state is restored exactly, and a `SimpUsed` info leaf is added for capture. Export identity is unchanged (verified) | `Lean/Elab/Tactic/Simp.lean:792-822`: push `stats.usedTheorems` from `evalSimp`/`evalSimpAll` instead of recomputing; the dry run also consumes heartbeats |
| 11 | Same for tactics without a lemma record (`simpa`, `dsimp`, `grind`, `norm_num`, …) | conservative rule: a command using such a tactic depends on the same-file groups that registered simp/grind-set lemmas | `Lean/Elab/Tactic/Simpa.lean`, `dsimpLocation` (returns no stats, `Simp.lean:824`), `Lean/Meta/Tactic/Grind/*` (E-matching instances used) |
| 12 | Published declarations visible by name, on demand, without imports | `Paralean/Visibility.lean`: `registerReservedNamePredicate`/`registerReservedNameAction` at start-up, active only in working-copy environments and suspended during loads | `Lean/ResolveName.lean:101-103` `containsDeclOrReserved` and `Lean/ReservedNameAction.lean:46` `realizeGlobalName`, which would consult the live registry |
| 13 | `set_option` of an option declared in the workspace | dependency on the `register_option` group (a constant of that name), or on every initializer group (trace classes) | option declarations would carry provenance |

Residual G1 cases (2 of 1,225): both are `grind` calls (M03 `ascFactorial_eq_ascFactorialBinary`,
M16 `bicompl_map_eq_of_injective`). Their proof terms differ in isolation even with
every same-file simp/grind-set lemma in the closure; the same-file prefix fixes them.
Exact fix: hook 11 for `grind`.
