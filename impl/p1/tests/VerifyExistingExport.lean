import Paralean

open Lean Paralean System

/-! Test-only verifier for an already-built export package. The production `export`
command first calls `writeExport` and `runBuild`; this runner reconstructs the same
catalogue and plan, then invokes the actual `verifyExport` without touching artifacts. -/
unsafe def main (args : List String) : IO UInt32 := do
  let [storeDir, outDir, libDir, sysrootDir] := args
    | IO.eprintln "usage: verify-existing STORE OUT P1_LIB SYSROOT"; return 2
  initSearchPath (FilePath.mk sysrootDir) [FilePath.mk libDir]
  let u ← Fork.init
  unless u.simp do Hooks.installSimp
  unless u.instnames do InstName.install
  enableInitializersExecution
  let store : Store := { root := storeDir }
  let files ← store.currentFiles
  let cat ← Catalog.load store files
  let ren ← if (← IO.getEnv "PARALEAN_STORE").isSome then Remote.renames else pure {}
  let cat := { cat with metas := cat.metas.fold (fun m k g => m.insert k (renamedGroup ren g)) {} }
  let plan ← exportPlanFor cat cat.order
  for d in plan.diags do IO.println s!"  {d}"
  if plan.diags.any (·.severity == "reject") then return 1
  let (nv, ne, ds) ← verifyExport cat plan (FilePath.mk outDir) ren
  let nd := cat.order.size - ne
  IO.println s!"verify: {nv}/{nd} declaration groups identical in the stock-built oleans; {ne} effect-only groups (build-checked)"
  for d in ds do IO.println s!"  {d}"
  return if nv == nd then 0 else 1
