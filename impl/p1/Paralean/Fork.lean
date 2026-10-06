import Lean

/-!
Bridge to the Paralean Lean fork (`fork/`, docs/p1-fork-hooks.md).

Selected at **build time**: compiled against a toolchain that has `Lean.Paralean.apiVersion` (the
fork), the definitions below call the fork's hooks; against stock Lean they are stubs and
`available` is `false`. Selected again at **run time**, per hook: `PARALEAN_FORK_HOOKS=0` makes a
fork build use the library workarounds instead (the stock path), and a list such as
`PARALEAN_FORK_HOOKS=sync,noaxiom,instnames,collector` swaps out a single hook (here `simp`), which
is how a hook and its workaround are compared on one binary (`scripts/simp-cost.sh`).

| fork hook (docs/p1-fork-hooks.md) | fork API | library workaround it replaces |
|---|---|---|
| 1 `Elab.async` pinned off | `Lean.Paralean.Config.pinSync` | host option only |
| 2 declaration collector | `Environment.declMark` / `addedDeclsSince` | diff of `getLocalConstantInfos` |
| 3 no axiom fallback | `Config.noAxiomFallback`, `AddedDecl.checked` | reject on elaboration errors only |
| 4 `simp` used lemmas | `Lean.Elab.Tactic.SimpUsedInfo` leaf | `Hooks.recordingSimp` dry-run replay |
| 5 canonical instance names | `Lean.Paralean.takeInstNameLog` | `InstName.canonicalInstanceElab` (two elaborations, anonymous instances only) |
-/

namespace Paralean.Fork
open Lean Elab Command

/-- `#paralean_fork cmd* #paralean_stock cmd* #paralean_end` elaborates the first block if the
toolchain is the Paralean fork and the second otherwise. -/
syntax (name := forkSelect) "#paralean_fork" command* "#paralean_stock" command* "#paralean_end" : command

@[command_elab forkSelect] def elabForkSelect : CommandElab := fun stx => do
  let fork := (← getEnv).contains `Lean.Paralean.apiVersion
  for c in (if fork then stx[1] else stx[3]).getArgs do
    elabCommand c

/-- A declaration a command added (fork hook 2). -/
structure Added where
  info : ConstantInfo
  /-- created by `realizeConst` -/
  realized : Bool
  /-- the kernel accepted it -/
  checked : Bool

/-- Which fork hooks this process uses; the others are replaced by the library workarounds. -/
structure Use where
  sync : Bool := false
  noaxiom : Bool := false
  simp : Bool := false
  instnames : Bool := false
  /-- the declaration collector (always available on the fork; read-only) -/
  collector : Bool := false
  deriving Repr, Inhabited

def Use.all : Use := { sync := true, noaxiom := true, simp := true, instnames := true, collector := true }

/-- A canonical instance name the fork chose (fork hook 5). -/
structure ChosenName where
  canonical : Name
  stock : Name
  passes : Nat
  derived : Bool

#paralean_fork
/-- Compiled against the fork. -/
def available : Bool := true

/-- Set the fork's hooks for this process. -/
def setHooks (u : Use) : IO Unit :=
  Lean.Paralean.setConfig { pinSync := u.sync, noAxiomFallback := u.noaxiom, simpUsed := u.simp,
                            canonicalInstNames := u.instnames }

def declMark (env : Environment) : Nat := env.declMark

def addedSince (env : Environment) (mark : Nat) : IO (Array Added) := do
  return (← env.addedDeclsSince mark).map fun d => { info := d.info, realized := d.realized, checked := d.checked }

def simpUsed? (ci : CustomInfo) : Option (Array Name) :=
  (ci.value.get? Lean.Elab.Tactic.SimpUsedInfo).map (·.names)

def takeChosen : IO (Array ChosenName) := do
  return (← Lean.Paralean.takeInstNameLog).map fun r =>
    { canonical := r.canonical, stock := r.stock, passes := r.passes, derived := r.derived }
#paralean_stock
/-- Compiled against stock Lean: no fork hooks. -/
def available : Bool := false
def setHooks (_ : Use) : IO Unit := pure ()
def declMark (_ : Environment) : Nat := 0
def addedSince (_ : Environment) (_ : Nat) : IO (Array Added) := pure #[]
def simpUsed? (_ : CustomInfo) : Option (Array Name) := none
def takeChosen : IO (Array ChosenName) := pure #[]
#paralean_end

/-- The fork hooks this process uses. Fixed at start-up by `init`. -/
initialize useRef : IO.Ref Use ← IO.mkRef {}

def use : IO Use := useRef.get

/--
Decide fork hooks vs library workarounds for this process and enable the chosen fork hooks.
`PARALEAN_FORK_HOOKS` unset or `all`: every fork hook; `0`: none (the library workarounds, as on
stock Lean); otherwise a comma-separated list of `sync,noaxiom,simp,instnames,collector`.
`PARALEAN_STOCK_INSTANCE_NAMES` turns `instnames` off. On stock Lean nothing is used.
-/
def init : IO Use := do
  let u : Use ← if !available then pure {} else
    match (← IO.getEnv "PARALEAN_FORK_HOOKS") with
    | none | some "all" | some "1" => pure .all
    | some s => pure <| (s.splitOn ",").foldl (init := {}) fun u h => match h.trimAscii.toString with
      | "sync" => { u with sync := true } | "noaxiom" => { u with noaxiom := true }
      | "simp" => { u with simp := true } | "instnames" => { u with instnames := true }
      | "collector" => { u with collector := true } | _ => u
  let u := if (← IO.getEnv "PARALEAN_STOCK_INSTANCE_NAMES").isSome then { u with instnames := false } else u
  useRef.set u
  setHooks u
  return u

end Paralean.Fork
