import Lean
/-!
Elaborates Lean files with the fork's canonical instance names (run with `LEAN_PARALEAN=1`) and
prints every name chosen as `STAT file canonical stock passes derived` (other stdout lines are
the files' own messages). `passes = 1` means the first
name was already right (the header prediction for an `instance`, delta deriving); `passes = 2`
means the command or deriving handler was elaborated again.
Usage: LEAN_PARALEAN=1 LEAN_PATH=... lean --run fork/tools/InstNameStats.lean FILE MODULE
-/
open Lean Elab

unsafe def main : List String → IO Unit
  | [f, mod] => do
    initSearchPath (← findSysroot)
    enableInitializersExecution
    let input ← IO.FS.readFile f
    let _ ← runFrontend input {} f (mod.toName) (trustLevel := 1024)
    for r in ← Paralean.takeInstNameLog do
      IO.println s!"STAT\t{f}\t{r.canonical}\t{r.stock}\t{r.passes}\t{r.derived}"
  | _ => throw <| IO.userError "usage: InstNameStats FILE MODULE"
