# P1 notes for the interface freeze

Findings from the P1 implementation (`impl/p1/`) that the frozen formats in
[p0-interfaces.md](p0-interfaces.md) must account for. P1 does not edit P0's file.
Each item gives the evidence and the choice P1 made.

## 1. Auxiliary names depend on `Elab.async`

- Evidence: synchronous elaboration (`Elab.async := false`) names a proof auxiliary
  `Probe.aux_pos._proof_1`. Stock `lake build` elaborates asynchronously by default and
  names the same auxiliary `Probe.aux_pos._proof_1_1`. The kernel terms, and therefore
  the declaration IDs, differ.
- P1 choice: capture runs synchronously, and every exported module pins
  `set_option Elab.async false`. With that pin, 14/14 probe groups and 3/3 B→A→B groups
  re-encode identically from the stock-built `.olean`s.
- **Decided (parent, 2026-10-05):** the fork forces `Elab.async false` everywhere:
  capture, validator, export and the `remote%` elaborator. The setting is not
  overridable; option changes are rejected with a diagnostic. P1 implements this for
  capture (`reject:async-override`) and pins it in replay and export. Fork locations:
  [p1-fork-hooks.md](p1-fork-hooks.md) item 1.
- Measured cost (stock `lean`, best of 3, `impl/p1/results/async-cost.tsv`): Mathlib
  M01–M18 wall 11.7 s → 16.3 s (×1.39); worst file M18 ×2.2; fixtures 5.5 s → 5.9 s.
  Total CPU time goes down (24.6 s → 22.4 s): the cost is lost within-file
  parallelism, not extra work.
- The stock elaborator publishes a theorem's signature before its kernel check
  finishes (async), and it re-adds kernel-rejected theorems as axioms in both modes.
  Publication must therefore never follow from "the command returned"; see the
  F-async results in [p1-gate.md](p1-gate.md).

## 2. Identity normalization

A declaration ID must not depend on the module a group was elaborated in. P1 encodes
identity after these normalizations; all were needed to make replay reproduce IDs:

| Module-dependent spelling | Example | Normalization |
|---|---|---|
| private prefix | `_private.M.0.P.aux` | strip prefix (scoped, group-keyed) |
| relocation namespace | `P._pl_61d5bb79.aux` | strip `_pl_*` component |
| `_aux` macro names | `_aux_Fix_Probe2___macroRules_…` | replace module with `$M` |
| hygienic decl names | `initFn._@.M.<hash>._hygCtx._hyg.2` | `initFn._hyg.<k>`, k = per-group creation order |
| hygienic binder names | `x._@.M.<hash>._hygCtx._hyg.5` | macro scopes erased (kernel ignores binder names) |
| hygienic universe params | `v._@.M….` in `noConfusionType` | renamed injectively by position, `v._hyg_<i>` |
| generated instance suffix | `instInhabitedProdNat_fix` | project suffix stripped from the identity; export keeps module roots so Lean regenerates it |

Hygienic *name literals inside terms* (e.g. `register_simp_attr`'s `initFn` bodies)
cannot be normalized; such groups are module-dependent and reported.

## 3. Constant references

The P1 encoding uses four reference forms: `base n` (pinned toolchain/library),
`self l`, `dep <package-id> l` (exact pin), and `res <ref> <suffix>` (a reserved name,
never transported). Dependencies pin **package** IDs (declaration content + capsule +
frontend dependencies), not bare declaration IDs, so two byte-identical declarations
with different capsules remain distinct packages.

## 4. Reserved names

"Reserved" is decided with Lean's own `isReservedName` in the producing environment. This
covers private-spelled match equations and splitters. Kernel replay re-realizes them via
`executeReservedNameAction` in the reconstructed frontend environment. It then adds them
with the stock kernel, interleaved with the consumer's own declarations in one
topological order: a WF equation such as `ack.eq_1` needs `ack.match_1` from the same
group.

## 5. Frontend dependencies

Kernel dependencies are not enough for capsules:

- Constants named in source but absent from the term (`simp [lemma]` with a
  definitional lemma) must be in scope. P1 adds every constant referenced by a
  `TermInfo` to the frontend dependencies.
- Syntax kinds and elaborators used by the command are resolved through the macro and
  elaborator attribute tables.
- `attribute [...] c` commands become effect groups that consumers of `c` depend on.
- Section-local effects (`local notation`, `attribute [local …]`, `open scoped`) are not
  published. Their text travels in the capsule of every later command in the section.
