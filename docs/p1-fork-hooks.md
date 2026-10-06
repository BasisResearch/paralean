# P1: places where the fork needs a hook

P1 runs on the stock nightly (`193c3589`) as a library, with no patches, and on the Paralean
fork of that commit ([fork/](../fork/README.md), commit `63380ffa`). The first two tables list
each workaround P1 uses on stock Lean and the Lean source location a fork hook replaces. The
last section lists what the fork implements and which workarounds P1 drops on it. Paths are
relative to `src/` of the Lean checkout at the pinned commit.

| # | Need | P1 workaround | Fork location |
|---|---|---|---|
| 1 | `Elab.async` forced off, not overridable (parent decision) | host sets `Elab.async := false`; capture **rejects** any command or scope that changes it; exports pin `set_option Elab.async false` | option `Lean/CoreM.lean:35`; default forced on in `Lean/Elab/Frontend.lean:291-292` (`Elab.async.setIfNotSet opts true`) and `Lean/Server/FileWorker.lean:432-433`; `set_option` elaboration should reject the name |
| 2 | Capture at command boundaries, including nested `realizeConst` | diff `Environment.getLocalConstantInfos` before/after each `Frontend.processCommand`; extension touches by exported-entry counts | `Lean/AddDecl.lean` `addDecl` (lines ~101-215) and `Lean/Meta/Basic.lean:2787` `realizeConst`; a per-command collector would avoid the O(n) diff |
| 3 | Failed declarations must not be usable downstream | capture refuses: elab errors reject the command; consumers fail to encode a reference to an unpublished constant; the validator re-checks | `Lean/AddDecl.lean:189-214` (`addAsAxiom`): after a kernel failure the theorem is re-added as an **axiom** "to avoid follow-up errors", so the next declaration elaborates without error. Under async, `AddDecl.lean:160-175` publishes the signature (`setEnv async.mainEnv`) before the kernel task runs |
| 4 | `_proof_n` names independent of elaboration mode | pin async off | `Lean/CoreM.lean:75` `DeclNameGenerator` (`parentIdxs`/`mkChild`) gives `_proof_1_1` in async branches |
| 5 | Generated instance names independent of module root and environment | anonymous `instance` commands are named canonically by hook 14 and the capsule spells the name (`instance /-pl:gen-/ instFoo_<8 hex> …`); derived instances keep the handler's spelling, a `_n` suffix on one is rejected as a collision (`instance-name-clash`), and exported Mathlib files are renamed under the `Mathlib.` root so the handler regenerates the same name | `Lean/Elab/DeclNameGen.lean:219-237` `mkBaseNameWithSuffix` (project suffix from `getMainModule.getRoot` and module-locality of referenced constants), `:243-251` `mkUnusedBaseName` (`_n`) |
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
| 14 | Canonical instance names (p0-interfaces.md §3.2, OPEN-24): `<stock base without _n or project suffix>_<first 8 hex of H("v0/insttype", type)>` | `Paralean/InstName.lean`: a builtin `declaration` elaborator ahead of the stock one. For an anonymous, source-written `instance` it elaborates the command once with the stock elaborator to read the final type, restores the whole command state, and elaborates it again with the canonical name. An existing declaration of that name is reported as a collision, never renamed. Instances synthesized by deriving handlers are left alone, because a stock export re-runs the handler and cannot be given a name | `Lean/Elab/DeclNameGen.lean:262` `mkInstanceName` (would compute the name from the elaborated header type directly, without the second elaboration) and `Lean/Elab/Deriving/Util.lean:95` `mkInstName` (same scheme for derived instances and their `instFoo.repr` auxiliaries) |

Residual G1 cases (2 of 1,225): both are `grind` calls (M03 `ascFactorial_eq_ascFactorialBinary`,
M16 `bicompl_map_eq_of_injective`). Their proof terms differ in isolation even with
every same-file simp/grind-set lemma in the closure; the same-file prefix fixes them.
Exact fix: hook 11 for `grind`.

## Implemented in the fork (fork/, `63380ffa`)

The fork carries five hooks, all off unless the process enables them (`LEAN_PARALEAN=1`, or
`Lean.Paralean.setConfig`), so it behaves as stock Lean otherwise. impl/p1 detects the fork
when it is compiled (`Paralean/Fork.lean`). It then uses each hook in place of its library
workaround, per hook at run time (`PARALEAN_FORK_HOOKS`, default all). On stock Lean it keeps
the workarounds. Results: [fork-log.md](fork-log.md).

| fork hook | item above | Lean source (fork) | P1 workaround dropped on the fork |
|---|---|---|---|
| 1 `Elab.async` pinned off | 1, 4 | `Lean/Elab/Frontend.lean` `runFrontend`, `Lean/Server/FileWorker.lean` `setupFile`, `Lean/Elab/SetOption.lean` `elabSetOption` | none in the host (it already sets the option); exports and every `lean`/`lake` run with `LEAN_PARALEAN` are pinned by the frontend, not by a `set_option` line, and `set_option Elab.async true` is an error. Capture's `async-override` rejection stays as policy for source that names the option |
| 2 per-command declaration collector | 2 | `Lean/Environment.lean` `Environment.declMark`, `Environment.addedDeclsSince` | the O(n) diff of `getLocalConstantInfos` per command (`Capture.runCommands`). It also reports provenance: constants created by `realizeConst` are flagged, which Lean's spelling classifier cannot see (`_arg_pusher`, `_unary.induct`; capture logs them as `note:provenance`) |
| 3 no axiom fallback | 3 | `Lean/AddDecl.lean` `addDeclCore.doAdd` | reliance on later commands failing to encode a reference to an unpublished constant. A rejected declaration is not in the kernel environment, so a later declaration that uses it fails in the kernel. The collector marks it `checked = false` and capture rejects the command (`kernel-rejected`) |
| 4 `simp` used-lemma record | 10 | `Lean/Elab/Tactic/Simp.lean` `recordSimpUsed` (from `evalSimp`, `evalSimpAll`) | `Hooks.recordingSimp`/`recordingSimpAll`, the dry-run replay of every `simp`/`simp_all` call on a full state snapshot |
| 5 canonical instance names | 5, 14 | `Lean/Paralean/InstName.lean` `canonicalInstanceName`, `predictInstanceName`; `Lean/Elab/Declaration.lean` `elabCanonicalInstance`; `Lean/Elab/Deriving/Util.lean` `mkInstName`; `Lean/Elab/Deriving/Basic.lean` `runDerivingHandler`, `processDefDeriving` | `InstName.canonicalInstanceElab`, which elaborated every anonymous instance twice. Derived instances are now canonical too, so the `instance-name-clash` check for `_n` derived names no longer fires for them, and exports build with `LEAN_PARALEAN=1` so the handlers regenerate the same names. Capture checks every name the fork chose against the library's computation (`instance-name-mismatch`) |

Still workarounds on the fork: items 6–9, 11–13 (hygiene keyed by module, private names across
segments, `initialize` in the same module, re-realization in a validator, lemma records for
`simpa`/`dsimp`/`grind`, on-demand visibility, option provenance), and anonymous instances
inside `mutual` blocks (stock names, `unsupported:noncanonical-instance`).
