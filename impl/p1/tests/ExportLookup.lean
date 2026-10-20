import Paralean.Export

open Lean Paralean System

/-- Run against a captured F13 store and its newly built exported `.olean`.
Checks the actual module-data order and duplicate use of one exported member. -/
unsafe def main (args : List String) : IO Unit := do
  let [storeDir, oleanPath] := args |
    throw (IO.userError "usage: ExportLookup.lean F13_STORE F13_EXPORTED_OLEAN")
  let store : Store := { root := storeDir }
  let cat ← Catalog.load store (← store.currentFiles)
  let gids := cat.order.filter fun gid => (cat.get! gid).capsule.file.endsWith "F13InitDecl.lean"
  unless gids.size == 4 do throw <| IO.userError s!"expected four F13 groups, got {gids.size}"
  let plan := planExport cat gids
  let some mod0 := plan.modules[0]? | throw <| IO.userError "missing F13 module"
  let m := mod0.name
  let arts : NameMap ImportArtifacts := ({} : NameMap ImportArtifacts).insert m
    (.ofArrays #[#[FilePath.mk oleanPath]])
  enableInitializersExecution
  let env ← importModules #[{ module := m }] {} (loadExts := true) (arts := arts)
    (level := .private)
  let (_, names, diags) := exportIdentity cat plan env
  unless diags.isEmpty do throw <| IO.userError s!"baseline lookup rejected: {diags}"
  for gid in gids do
    let g := cat.get! gid
    unless (names.getD gid #[]).size == g.members.size do
      throw <| IO.userError s!"baseline group {gid} has wrong member count"
    for (n, mr) in names.getD gid #[] do
      if mr.name.hasMacroScopes then
        unless exportHygieneKey? m n == exportHygieneKey? g.capsule.module mr.name do
          throw <| IO.userError s!"{gid}: exported member {n} has wrong raw hygiene key"
  let some refGid := gids.find? (fun gid => (cat.get! gid).capsule.startLine == 6) |
    throw <| IO.userError "missing line-six initializer"
  let duplicateId := "synthetic-duplicate-hygiene-member"
  let duplicate := { cat.get! refGid with gid := duplicateId }
  let cat2 := { cat with metas := cat.metas.insert duplicateId duplicate }
  let plan2 := { plan with modules := #[{ mod0 with groups := mod0.groups.push duplicateId }] }
  let (_, names2, diags2) := exportIdentity cat2 plan2 env
  unless diags2.any (fun d => d.code == "export-ambiguous") do
    throw <| IO.userError s!"duplicate captured group not rejected: {diags2}"
  unless (names2.getD duplicateId #[]).isEmpty do
    throw <| IO.userError "duplicate captured group reused the exported declaration"
  IO.println "PASS: F13 raw keys match; duplicate exported member rejected"
