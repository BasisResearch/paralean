# Paralean Lean fork

A minimal fork of Lean at the pinned nightly `nightly-2026-10-03`
(`193c3589a4fc16c4059261ab38cfa365eb24f323`). It carries the hooks Paralean needs, so the P1
prototype (`impl/p1`) can drop its library-side workarounds
([docs/p1-fork-hooks.md](../docs/p1-fork-hooks.md)). Build log and results:
[docs/fork-log.md](../docs/fork-log.md).

```sh
fork/build.sh            # clone at the pin, apply patches/, cmake + make stage1, check the githash
                         # -> .deps/lean4-paralean/build/release/stage1/bin/{lean,lake}
PARALEAN_LEAN=fork impl/p1/scripts/bootstrap.sh --mathlib   # P1 on the fork
PARALEAN_LEAN=fork impl/p1/scripts/run-all.sh
```

`build.sh` applies the patches with `git am`, using the author as committer and the author
date as committer date, so the patched commit is always `GITHASH` and `lean --githash` of
the build reports it. The build needs libuv with headers (see docs/p0-log.md for a
from-source libuv and `PKG_CONFIG_PATH`). It took 16 minutes at `-j12`
(`PARALEAN_JOBS`) on aws-dev, and the build tree is about 6 GB.

## Switching the hooks on

Every hook is **off** unless enabled, so the fork behaves as stock Lean by default. They are
enabled per process:

* `LEAN_PARALEAN=1` (or `all`) in the environment of `lean`, `lake` or the server, or a
  comma-separated subset `sync,noaxiom,simp,instnames`;
* or a host calls `Lean.Paralean.setConfig` before it creates environments (impl/p1 does this
  through `Paralean/Fork.lean`).

The switch is not an option, so `set_option` in user source cannot change it.
`Lean.Paralean.apiVersion` lets a library detect the fork when it is compiled.

## Hooks

| # | hook | Lean source | API / switch |
|---|---|---|---|
| — | mode switch | `src/Lean/Paralean/Mode.lean` | `Lean.Paralean.Config`, `getConfig`, `setConfig`, `LEAN_PARALEAN` |
| 1 | `Elab.async` pinned off | `Lean/Elab/Frontend.lean` `runFrontend`, `Lean/Server/FileWorker.lean` `setupFile`, `Lean/Elab/SetOption.lean` `elabSetOption` | `pinSync`: the frontend and the server force `Elab.async := false`; `set_option Elab.async true` is an error (`false` keeps the pin and is accepted) |
| 2 | per-command declaration collector | `Lean/Environment.lean` `Environment.declMark`, `Environment.addedDeclsSince` | always available (read-only). Every declaration added on the branch since a mark, in order, with `realized` (created by `realizeConst`) and `checked` (the kernel holds it with the same kind); waits for `env.checked` |
| 3 | no axiom fallback | `Lean/AddDecl.lean` `addDeclCore.doAdd` | `noAxiomFallback`: a declaration the kernel rejects is not re-added as an axiom |
| 4 | `simp` used-lemma record | `Lean/Elab/Tactic/Simp.lean` `recordSimpUsed`, called from `evalSimp`, `evalSimpAll` | `simpUsed`: a `Lean.Elab.Tactic.SimpUsedInfo` custom info leaf with the used declarations |
| 5 | canonical instance names | `Lean/Paralean/InstName.lean` `canonicalInstanceName`, `predictInstanceName`; `Lean/Elab/Declaration.lean` `elabCanonicalInstance`; `Lean/Elab/Deriving/Util.lean` `mkInstName`; `Lean/Elab/Deriving/Basic.lean` `runDerivingHandler`, `processDefDeriving` | `canonicalInstNames`: `<stock base without project suffix>_<first 8 hex of SHA-256("v0/insttype" NUL text(τ))>`, never `_n`; a clash is an error. `Lean.Paralean.takeInstNameLog` returns each choice with the stock name |

Hook 5 computes the name exactly as `impl/p1/Paralean/InstName.lean` does (same SHA-256, same
type text, same `normName`). impl/p1 checks every name the fork chooses against its own
computation (`instance-name-mismatch`).

* An anonymous `instance` is named from a prediction made on its header (binders, auto-bound
  implicits, the section variables the header mentions and instance-implicit ones over them).
  After elaboration the name is recomputed from the final type, and the command is elaborated
  a second time only if they differ (a section variable used only in the body, a universe
  fixed by the body).
* A deriving handler first runs under the stock names `mkInstName` returns. If any instance it
  declared needs a different canonical name, the state is restored and the handler runs again
  with `mkInstName` returning the canonical names, so the `instFoo.repr`-style auxiliaries
  follow. Every `mkInstName` handler (Repr, BEq, Hashable, Ord, ToJson/FromJson, ToExpr,
  DecidableEq on structures and inductives) therefore runs twice in Paralean mode. Handlers that
  write an anonymous `instance` (DecidableEq on enums, Nonempty, TypeName) go through the
  `instance` path.
* Delta deriving (`deriving instance C for d` with `d` a definition) names the instance from its
  closed type directly.

Not covered: anonymous instances inside `mutual` blocks (stock names; impl/p1 reports
`unsupported:noncanonical-instance`), and instances whose stock name has macro scopes.

## Tests

`tests/elab/paralean{Sync,Collector,Simp,InstNames}.lean` run with `LEAN_PARALEAN=1` (their
`.init.sh`); `tests/elab/paraleanOff.lean` checks that everything is stock without it.

## Patches

`patches/` is `git format-patch 193c3589` of branch `paralean`; one patch per hook:

| patch | source files | src + / − | tests + |
|---|---|---|---|
| 0001 mode switch | `Lean/Paralean/Mode.lean`, `Lean.lean` | 81 / 0 | 29 |
| 0002 hook 1 | Frontend, FileWorker, SetOption | 13 / 4 | 28 |
| 0003 hook 2 | Environment | 56 / 0 | 0 |
| 0004 hook 3 | AddDecl | 5 / 2 | 136 |
| 0005 hook 4 | Tactic/Simp | 21 / 0 | 42 |
| 0006 hook 5 | `Lean/Paralean/InstName.lean`, `Lean.lean`, Declaration, Deriving/Basic, Deriving/Util | 435 / 3 | 109 |
| total | 12 files | 611 / 9 | 344 |

`results/` holds the test-suite logs (default mode and Paralean mode) and their classification,
and `tools/InstNameStats.lean` the instance-name statistics tool (docs/fork-log.md).
