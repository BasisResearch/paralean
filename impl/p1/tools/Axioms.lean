import Lean

/-!
G4 `#print axioms` comparison helper. Imports the given modules (from `LEAN_PATH`) and prints,
for every constant declared in one of them, one JSON line
`{"module": M, "name": N, "axioms": [...]}` with the same axiom set `#print axioms` reports
(`Lean.collectAxioms`). Run it once on the reference build and once on the export build;
`scripts/g4.py` compares the two by normalized name.

Usage: lean --run tools/Axioms.lean MODULE[=OLEAN]...
`MODULE=OLEAN` imports that module from an explicit `.olean` (as Lake does), which is needed
when the module's root (e.g. `Mathlib.ParaleanExport…`) also exists on `LEAN_PATH`.
-/

open Lean

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mut mods : Array Name := #[]
  let mut arts : NameMap ImportArtifacts := {}
  for a in args do
    match a.splitOn "=" with
    | [m, path] =>
      let m := m.toName
      mods := mods.push m
      let o : System.FilePath := path
      let mut files := #[o]
      for ext in ["olean.server", "olean.private"] do
        let f := o.withExtension ext
        if ← f.pathExists then files := files.push f
      arts := arts.insert m (.ofArrays #[files])
    | _ => mods := mods.push a.toName
  let env ← importModules (mods.map fun m => { module := m, importAll := true }) {}
    (loadExts := true) (level := .private) (arts := arts)
  let modSet : NameSet := mods.foldl (·.insert ·) {}
  for (n, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    unless modSet.contains m do continue
    let (axs, _) ← (collectAxioms (m := CoreM) n).toIO { fileName := "<axioms>", fileMap := default } { env }
    let j := Json.mkObj [("module", toString m), ("name", Json.arr (n.components.toArray.map
      fun c => match c with | .str _ s => Json.str s | .num _ k => Json.num k | .anonymous => Json.null)),
      ("axioms", toJson ((axs.map toString).qsort (· < ·)))]
    IO.println j.compress
  return 0
