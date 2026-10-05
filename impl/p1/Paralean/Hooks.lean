import Lean

/-!
Process-wide elaborator hooks (stand-ins for fork changes). Registered in Lean's builtin
tables at host start-up, so nothing is imported into the user's environment and
elaboration of user files is unchanged.

**`simp` used-lemma record (fixes the G1 capsule gap).** `simp` and `simp_all` may use
`@[simp]` lemmas, proved by `rfl`, that never appear in the resulting proof term, so they
are not kernel dependencies. Stock `evalSimp` discards the used-lemma set it computes.
The hook runs the public `mkSimpContext`/`simpLocation` pipeline on a saved state to learn
the used lemmas, restores the state, and then runs the stock builtin elaborator
unchanged. It records the used declarations as an info-tree leaf (`SimpUsed`), which
capture turns into frontend dependencies. Fork location: `Lean/Elab/Tactic/Simp.lean`
`evalSimp`/`evalSimpAll` (lines 792–822 at `193c3589`), which would push `stats.usedTheorems`
instead of recomputing.
-/

namespace Paralean.Hooks
open Lean Elab Tactic Meta

/-- Declarations a `simp` call used (info-tree payload). -/
structure SimpUsed where
  names : Array Name
  deriving TypeName

def usedDecls (s : Simp.UsedSimps) : Array Name :=
  s.map.toList.toArray.filterMap fun (o, _) => match o with
    | .decl n .. => some n
    | _ => none

/-- Full snapshot of every elaboration state layer (including name generators, macro
scopes and caches, which `saveState`/`restore` deliberately keep). -/
structure Snapshot where
  coreS : Core.State
  metaS : Meta.State
  termS : Term.State
  tacS : Tactic.State

def snapshot : TacticM Snapshot :=
  return { coreS := ← getThe Core.State, metaS := ← getThe Meta.State,
           termS := ← getThe Term.State, tacS := ← get }

def Snapshot.restoreAll (s : Snapshot) : TacticM Unit := do
  set s.coreS; set s.metaS; set s.termS; set s.tacS

/-- Run the stock elaborator `stock` first (unchanged behaviour), then replay the same
call on the pre-state with `observe` to read the used lemmas, and restore the stock
post-state exactly. Only an info leaf is added. -/
def withUsedLemmas (stx : Syntax) (stock : TacticM Unit) (observe : TacticM (Array Name)) :
    TacticM Unit := do
  let pre ← snapshot
  stock
  let post ← snapshot
  pre.restoreAll
  let used ← try observe catch _ => pure #[]
  post.restoreAll
  unless used.isEmpty do
    pushInfoLeaf (.ofCustomInfo { stx, value := Dynamic.mk ({ names := used } : SimpUsed) })

def recordingSimp : Tactic := fun stx =>
  withUsedLemmas stx (evalSimp stx) <| withMainContext do
    let r ← mkSimpContext stx (eraseLocal := false)
    let stats ← r.dischargeWrapper.with fun d? =>
      simpLocation r.ctx r.simprocs d? (expandOptLocation stx[5])
    return usedDecls stats.usedTheorems

def recordingSimpAll : Tactic := fun stx =>
  withUsedLemmas stx (evalSimpAll stx) <| withMainContext do
    let r ← mkSimpContext stx (eraseLocal := true) (kind := .simpAll) (ignoreStarArg := true)
    let (_, stats) ← simpAll (← getMainGoal) r.ctx (simprocs := r.simprocs)
    return usedDecls stats.usedTheorems

/-- Install the hooks (call before any environment is created). -/
def install : IO Unit := do
  tacticElabAttribute.addBuiltin ``Lean.Parser.Tactic.simp `Paralean.Hooks.recordingSimp recordingSimp
  tacticElabAttribute.addBuiltin ``Lean.Parser.Tactic.simpAll `Paralean.Hooks.recordingSimpAll recordingSimpAll

end Paralean.Hooks
