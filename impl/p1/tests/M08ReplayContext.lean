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

/-- Independently re-elaborate each capsule and compare its canonical encoding with
the immutable object, without adding a byte array to the production replay result. -/
private unsafe def byteChecks (store : Store) (cat : Catalog) (gids : Array String)
    (imports : Array Name) : IO Nat := do
  let module := sourceReplayModule cat gids
  let isModule := gids.any fun gid => (cat.get! gid).capsule.isModule
  let specs := gids.foldl (fun acc gid => (cat.get! gid).capsule.importSpecs.foldl
    (fun acc spec => if acc.contains spec then acc else acc.push spec) acc) #[]
  let hdr := if isModule then
      "module\n" ++ String.join (specs.toList.map (· ++ "\n"))
    else headerFor imports
  let (sess0, inputCtx, _, imps, hdrDiags, _) ← openSession hdr "<byte-replay>" module
  unless hdrDiags.isEmpty do
    throw <| IO.userError s!"byte replay header failed: {hdrDiags.map toString}"
  let fc0 : FileCtx := {
    workspace := "<byte-replay>", file := "<byte-replay>", module, imports := imps, input := hdr
    fileMap := inputCtx.fileMap, baseEnv := sess0.cmdState.env }
  let mut sess := sess0
  let mut checked := 0
  for gid in gids do
    let g := cat.get! gid
    let deps := relocatedDepsOf cat g false
    let src := renderCapsule g deps
    let mainAt := capsuleTextOffset g deps
    let capsuleCtx := Parser.mkInputContext src s!"<byte-capsule {g.short}>"
    let sessRef ← IO.mkRef sess
    let capsuleFile : FileCtx := { fc0 with input := src, fileMap := capsuleCtx.fileMap, file := s!"<byte-capsule {g.short}>" }
    let fcRef ← IO.mkRef capsuleFile
    let seen ← IO.mkRef false
    let st ← runCommands sess.cmdState capsuleCtx {} fun r => do
      if r.startPos ≥ mainAt && r.startPos < mainAt + g.capsule.text.utf8ByteSize &&
          !(← seen.get) then
        seen.set true
        let (sess', fc', out) ← analyze (← sessRef.get) (← fcRef.get) r
          (pidOverride? := some g.gid)
        sessRef.set sess'
        fcRef.set fc'
        match out with
        | .group replayed bytes =>
          let stored ← store.getObject g.declId
          unless bytes == stored && replayed.declId == g.declId do
            throw <| IO.userError s!"{g.short}: replayed canonical bytes differ from stored object"
        | .failed ds =>
          throw <| IO.userError s!"{g.short}: byte replay failed: {ds.map toString}"
        | .skipped reason =>
          throw <| IO.userError s!"{g.short}: byte replay skipped: {reason}"
      else
        for c in r.newConsts do
          sessRef.modify fun s => { s with scaffold := s.scaffold.insert c.name }
        if r.msgs.any (·.severity == .error) then
          throw <| IO.userError s!"{g.short}: byte replay scaffolding failed"
      return none
    unless ← seen.get do
      throw <| IO.userError s!"{g.short}: byte replay did not find the command"
    sess := { (← sessRef.get) with cmdState := st }
    checked := checked + 1
  return checked

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
  let byteCount ← byteChecks store cat gids imports
  unless byteCount == gids.size do
    throw <| IO.userError "byte replay did not cover every M08 group"
  let synthetic ← sourceReplay cat gids imports (module? := some `Mathlib.ParaleanReplay)
  let some oldMacro := synthetic.results.find? (fun r =>
    (cat.get! r.gid).cmdKind == `Lean.Parser.Command.macro_rules)
    | throw <| IO.userError "M08 macro_rules group missing"
  if oldMacro.ok || oldMacro.replayedDeclId == some (cat.get! oldMacro.gid).declId then
    throw <| IO.userError "synthetic module unexpectedly reproduced the M08 declaration ID"
  unless oldMacro.diags.any (·.code == "replay-mismatch") do
    throw <| IO.userError "synthetic module mismatch had no diagnostic"
  IO.println s!"M08 context: exact replay {original.results.size}/{original.results.size}; \
    canonical bytes equal {byteCount}/{gids.size}; \
    old synthetic context rejected {oldMacro.replayedDeclId.getD "none"}"
