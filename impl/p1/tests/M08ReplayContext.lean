import Paralean.Replay

open Lean Paralean

private def assertName (label : String) (actual expected : Name) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError s!"{label}: got {actual}, expected {expected}"

private def selectionChecks : IO Unit := do
  let mkGroup (module : Name) : GroupRec :=
    { (default : GroupRec) with capsule := { (default : Capsule) with module } }
  let metas : Std.HashMap String GroupRec := {}
  let metas := metas.insert "a" (mkGroup `Mathlib.Tactic.ByCases)
  let metas := metas.insert "b" (mkGroup `Mathlib.Tactic.ByCases)
  let metas := metas.insert "c" (mkGroup `Other.Module)
  let cat : Catalog := { metas }
  assertName "same module" (sourceReplayModule cat #["a", "b"])
    `Mathlib.Tactic.ByCases
  assertName "mixed module" (sourceReplayModule cat #["a", "c"])
    `Mathlib.ParaleanReplay
  assertName "explicit override" (sourceReplayModule cat #["a", "c"] (some `Chosen.Module))
    `Chosen.Module
  assertName "empty closure" (sourceReplayModule cat #[]) `ParaleanReplay

/-- Run with the store freshly captured from Mathlib/Tactic/ByCases.lean. -/
unsafe def main (args : List String) : IO Unit := do
  selectionChecks
  let [storeDir] := args | throw <| IO.userError "usage: M08ReplayContext.lean STORE"
  let store : Store := { root := storeDir }
  let files ← store.currentFiles
  let cat ← Catalog.load store files
  let gids := cat.order
  let imports := gids.foldl (fun acc gid => (cat.get! gid).capsule.imports.foldl
    (fun acc m => if acc.contains m then acc else acc.push m) acc) #[]
  let original ← sourceReplay cat gids imports
  unless original.results.all (·.ok) do
    throw <| IO.userError "original module context failed exact declaration-ID replay"
  let synthetic ← sourceReplay cat gids imports (module? := some `Mathlib.ParaleanReplay)
  let some oldMacro := synthetic.results.find? (fun r =>
    (cat.get! r.gid).cmdKind == `Lean.Parser.Command.macro_rules)
    | throw <| IO.userError "M08 macro_rules group missing"
  if oldMacro.ok || oldMacro.replayedDeclId == some (cat.get! oldMacro.gid).declId then
    throw <| IO.userError "synthetic module unexpectedly reproduced the M08 declaration ID"
  unless oldMacro.diags.any (·.code == "replay-mismatch") do
    throw <| IO.userError "synthetic module mismatch had no diagnostic"
  IO.println s!"M08 context: exact replay {original.results.size}/{original.results.size}; \
    old synthetic context rejected {oldMacro.replayedDeclId.getD "none"}"
