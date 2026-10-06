# Fork log: the minimal Paralean Lean fork

Date 2026-10-06, aws-dev (Linux x86-64, 32 cores, shared; builds at `-j12`). The fork is
Lean `193c3589` (`nightly-2026-10-03`) plus six patches ([fork/](../fork/README.md)), commit
**`63380ffa`** (`fork/GITHASH`). Hooks and the workarounds they replace:
[p1-fork-hooks.md](p1-fork-hooks.md#implemented-in-the-fork-fork-63380ffa).

## Hooks and patch sizes

All hooks are off unless `LEAN_PARALEAN` (or `Lean.Paralean.setConfig`) enables them.

| patch | hook | Lean source | src + / − | tests + |
|---|---|---|---|---|
| 0001 | mode switch | `Lean/Paralean/Mode.lean` (`Config`, `getConfig`, `setConfig`, `apiVersion`) | 81 / 0 | 29 |
| 0002 | 1 `Elab.async` pinned off | `Lean/Elab/Frontend.lean` `runFrontend`; `Lean/Server/FileWorker.lean` `setupFile`; `Lean/Elab/SetOption.lean` `elabSetOption` | 13 / 4 | 28 |
| 0003 | 2 per-command declaration collector | `Lean/Environment.lean` `Environment.declMark`, `Environment.addedDeclsSince` | 56 / 0 | 0 |
| 0004 | 3 no axiom fallback | `Lean/AddDecl.lean` `addDeclCore.doAdd` | 5 / 2 | 136 |
| 0005 | 4 `simp` used-lemma record | `Lean/Elab/Tactic/Simp.lean` `recordSimpUsed` (called from `evalSimp`, `evalSimpAll`) | 21 / 0 | 42 |
| 0006 | 5 canonical instance names | `Lean/Paralean/InstName.lean` `canonicalInstanceName`, `predictInstanceName`; `Lean/Elab/Declaration.lean` `elabCanonicalInstance`; `Lean/Elab/Deriving/Util.lean` `mkInstName`; `Lean/Elab/Deriving/Basic.lean` `runDerivingHandler`, `processDefDeriving` | 435 / 3 | 109 |
| | total | 12 source files | **611 / 9** | 344 |

Of hook 5's 435 lines, about 170 are the SHA-256 and canonical type text ported byte for byte
from `impl/p1/Paralean/InstName.lean`.

## Build

- `fork/build.sh` from an empty directory: clone `lean4-nightly` at the pin (depth 1), `git am`
  the patches (committer = author, committer date = author date), `cmake --preset release`,
  `make stage1 -j12`. **15 min 56 s** wall (nice 5, shared machine), exit 0; `lean --githash` =
  `63380ffa…` = `fork/GITHASH`. Applying the patches in a second clone gave the same commit hash,
  so the githash is reproducible from the patches alone. The build tree is 6.2 GB.
- Development tree: `/data/home/kirancodes/Documents/code/lean4-paralean`, branch `paralean`
  (its build was removed after `build.sh` reproduced it, for disk).

## Lean test suite

At this pin `tests/lean/run` is `tests/elab` (3,317 tests) and `tests/elab_fail` (315). I ran
every ctest pile except Lake's own tests (Lake is unchanged): `elab`, `elab_fail`, `docparse`,
`server`, `server_interactive` (FileWorker is touched), `compile`, `compile_bench`, `elab_bench`,
`pkg`, `misc`, `misc_dir`, lint. Logs: `fork/results/`.

- **Default mode (hooks off): 4339/4340 pass** in 8 min. The one failure,
  `elab/async_systems_info.lean`, raises its own process priority (`setPriority pid 3`), which is
  denied because I ran ctest under `nice -n 5`. Stock `lean` (`~/p0-deps/lean-stock-193c3589`)
  fails it the same way under `nice` and both pass without it. **No regressions.**
- **The five fork tests** (`tests/elab/paralean{Sync,Collector,Simp,InstNames,Off}.lean`) pass on
  the development build and on the `build.sh` build.
- **Paralean mode** (`LEAN_PARALEAN=1` for the whole `elab`, `elab_fail`, `server_interactive`
  piles; informative, since stock expectations assume stock behaviour): 3629/3786 pass. None of
  the 157 failures is a crash in hook code. With every hook except `sync`, 57 remain, all
  intended: 24 print canonical instance names, 16 refer to an instance by its stock name,
  11 declare a duplicate instance (now a collision, not `_n`), 5 see the follow-up kernel error
  after a kernel failure, 1 prints a canonical name in its own panic message. The other 100
  come from synchronous elaboration: message order, `_proof_1` where stock async gives
  `_proof_1_1` (the P1 finding), and 14 server tests. Five of those (`cancellation*`,
  `issue13705*`) deadlock by design, because they block one theorem body and wait for a later
  command, which only async elaboration runs. This is the OPEN-14 cost of pinning the server
  synchronous. Classifier: `fork/results/classify-ctest.py`.

## P1 gate on the fork

`PARALEAN_LEAN=fork impl/p1/scripts/bootstrap.sh --mathlib` then `run-all.sh`, logs in
`impl/p1/results/fork/`. The Mathlib cache is for the stock toolchain, so bootstrap built only
the closure of the 18 corpus modules and F16's imports with the fork: 2,360 jobs (1,398 Mathlib
modules plus dependencies) in **6 min** wall, 1.4 GB. Mathlib and the G4 reference fixtures
are built with Paralean mode **off** (stock names); captures and exports run with every fork
hook. Exports build with the fork's `lake` and `LEAN_PARALEAN=1`, so deriving handlers
regenerate the canonical names (a stock build cannot, see below). Recorded stock results:
[p1-gate.md](p1-gate.md) (local run).

| Gate | stock (recorded) | fork |
|---|---|---|
| G1 replay | source 1224/1225, kernel 1225/1225, isolated 1224/1225 (fixtures 120/120; Mathlib 1104/1105) | **identical**: 1224/1225, 1225/1225, 1224/1225; the remaining one is still M08 `by_cases!` (module-dependent literal) |
| G2 membership/classes | 1122/1127, 5 explained instance spellings; 78 anonymous instances canonical | **1122/1127**, the same 5 (M13 `@[to_dual]` ×3, M16 stock `_1` ×2); **90** canonical instances: the same 78 anonymous ones with byte-identical names, plus **12 derived** instances (F03, F04, F08 ×5, F09, M11 ×3, M15) that the prototype had to leave stock; 0 reserved published; anchors complete |
| G3 capsules | max 390 B fixtures, 2,868 B Mathlib | identical sizes (`results/fork/summary.md`) |
| G4 export | 22/22 builds; identity 1116/1142; axioms 1445/1448; mappings 5/5 | **22/22** builds (fork `lake`, Paralean mode); identity **1116/1142**; axioms **1445/1448** (same 3 `@[to_dual]` names); mappings **5/5** |
| G5 negatives | 6/6, 0 staged; version conflict; duplicate instance | **same outcomes**, only IDs differ (the base githash is part of identity); duplicate-instance name `…_91913918` byte-identical |
| G6 B→A→B | pass | **pass** (`helper_c` fails on `helper`; 3 modules, 3/3 identical) |
| F-async | kernel-rejected theorem re-added as an axiom; its user elaborates without error | the user fails in the kernel (`unknown constant`), and capture rejects it as `kernel-rejected` through the collector even where the host saw no error |

Every instance name the fork chose in the gate (90) was recomputed by the library's
`InstName.canonicalName` and matched (`instance-name-mismatch`: 0). The first run had 3
mismatches in M01. They came from the new check running without the command's namespace
(`mkBaseNameWithSuffix` drops a head that matches the namespace: `Prod.instLE_…` inside
`namespace Prod`), not from the fork. Fixed in `Capture.lean` before the reported run.

**`simp` hook cost** (`scripts/simp-cost.sh`, `results/fork/simp-cost.tsv`): the same fork binary
captures with the native record and with the library's dry-run replay (every other fork hook
unchanged). Best of 5, user+sys CPU, because wall time on the shared box was too noisy for
2–5 s captures:

| module | groups | simp sites | native s | dry-run s | Δ s | dry-run / native | package IDs equal |
|---|---|---|---|---|---|---|---|
| M01 | 213 | 49 | 2.88 | 3.03 | 0.15 | 1.052 | yes |
| M03 | 83 | 26 | 2.01 | 2.00 | −0.01 | 0.995 | yes |
| M13 | 115 | 19 | 2.54 | 2.54 | 0.00 | 1.000 | yes |
| M16 | 211 | 25 | 2.33 | 2.36 | 0.03 | 1.013 | yes |
| M18 | 265 | 55 | 2.27 | 2.32 | 0.05 | 1.022 | yes |

On this corpus the dry run costs at most 5 % of capture CPU, about 3 ms per `simp` site. The
native record removes it and gives identical package IDs, which hash the simp-derived frontend
dependencies. The main gain is correctness rather than time: no second run of `simp` on a state
snapshot, so no double heartbeat use and no restore of state the stock elaborator did not
expect.

**Instance-name passes** (`fork/tools/InstNameStats.lean`, `fork/results/instname-passes.tsv`,
corpus files elaborated with `LEAN_PARALEAN=1`): all **80** anonymous instances, including those
deriving handlers write as anonymous `instance` commands, got their name from the header
prediction with **one** elaboration. The prototype elaborates each of them twice. All **10**
`mkInstName` derived instances took **two** handler runs (first under the stock name, then the
canonical one).

## Prototype workarounds removed on the fork

- Process-diff capture: `getLocalConstantInfos` before/after every command → the collector
  (`Fork.addedSince`), O(new declarations), with realization provenance and kernel status.
- `Hooks.recordingSimp`/`recordingSimpAll` (dry-run replay of `simp`/`simp_all` on a snapshot) →
  the native `SimpUsedInfo` leaf.
- `InstName.canonicalInstanceElab` (every anonymous `instance` elaborated twice, derived instances
  left stock) → the fork's canonical names for anonymous, derived and delta-derived instances.
- Reliance on downstream encoding failures for kernel-rejected declarations → no axiom fallback,
  plus `kernel-rejected` from the collector.
- `set_option Elab.async false` as the only pin in exports and fixtures → the frontend pin
  (`LEAN_PARALEAN`). The capture policy `reject:async-override` stays.

The workarounds stay in the library for stock Lean. A fork build selects per hook at run time
(`PARALEAN_FORK_HOOKS`, default all), and `simp-cost.sh` uses this.

## Not done, and caveats

- **Elaborator view after a kernel failure (hook 3).** Without the axiom fallback the kernel
  environment lacks the rejected declaration, but the elaborator still holds its unchecked
  preliminary info. So `#print axioms` on a later declaration that uses it reports no axioms (stock
  reported the fallback axiom); the later declaration itself fails in the kernel. Consumers must
  use the collector's `checked` or the kernel environment, as capture does.
- **Derived instances take two handler runs**; a per-handler type prediction (as for `instance`)
  would remove the second.
- **Anonymous instances in `mutual` blocks** keep stock names (`unsupported:noncanonical-instance`,
  none in the corpus); instances whose stock name has macro scopes keep it.
- **Exports are fork builds.** Canonical derived names cannot be reproduced by stock Lean, so
  "clean stock export" on the fork means a clean build with the fork in Paralean mode. A stock
  build of the same export would rename the 12 derived instances.
- **Server.** The sync pin makes the server tests that need concurrent elaboration deadlock
  (above); asynchronous interactive elaboration remains OPEN-14.
- `realizeConst` provenance is reported (`note:provenance`: `_arg_pusher`, `_unary.induct`) but
  does not yet change membership; classification still follows the spelling classifier, as in
  the recorded gate.
- Items 6–9 and 11–13 of p1-fork-hooks.md are not in the fork. The OPEN-14 async-export
  experiment (`core-async-export.log`) does nothing on the fork, because exports build pinned.
  The Track B scripts (`run-transparent*.sh`, `remote-*.sh`, `async-cost.sh`) were not rerun.
- Process note: while restarting the fork build I ran `pkill -f "lake build"`. On this shared
  machine that could have stopped another session's `lake build` running at that moment. Later
  stops were by PID only.

## Sentences for plan.md and README.md

For plan.md, P1 (after "Gate: replay and clean export agree with reference behavior."):

> The Paralean Lean fork (`fork/`, Lean `193c3589` + 6 patches, commit `63380ffa`) implements
> the P1 hooks natively: `Elab.async` pinned off, a per-command declaration collector, no axiom
> fallback after kernel failures, a `simp` used-lemma record and canonical instance names for
> anonymous and derived instances. On the fork the P1 gate gives the same G1–G6 results as on
> stock, with 12 more instances named canonically ([fork-log](fork-log.md)).

For plan.md, P3 (gate paragraph):

> The fork passes Lean's own test suite with its hooks off (4339/4340; the one failure is
> environmental and also fails on stock); in Paralean mode the differences are the intended
> ones plus server tests that need asynchronous elaboration (OPEN-14).

For README.md (status):

> P1 also runs on a minimal Lean fork (`fork/build.sh`; `PARALEAN_LEAN=fork` for the P1
> scripts) that replaces the prototype's library workarounds with native hooks.
