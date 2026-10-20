import Paralean

open Lean Paralean System

/-! Read-only diagnostic for comparing a captured canonical group object with
its exact re-encoding from an already built export package. -/
unsafe def main (args : List String) : IO Unit := do
  let [storeDir, outDir, libDir, sysrootDir, sourceLine, destination] := args |
    throw <| IO.userError "usage: DumpExistingExportGroup STORE EXPORT LIB SYSROOT LINE OUTPUT"
  initSearchPath (FilePath.mk sysrootDir) [FilePath.mk libDir]
  let u ← Fork.init
  unless u.simp do Hooks.installSimp
  unless u.instnames do InstName.install
  enableInitializersExecution
  let store : Store := { root := storeDir }
  let cat ← Catalog.load store (← store.currentFiles)
  let plan ← exportPlanFor cat cat.order
  let arts ← exportArts plan (FilePath.mk outDir)
  let isMod := plan.modules.any (·.isModule)
  let env ← importModules (plan.modules.map fun m => { module := m.name, importAll := isMod })
    {} (loadExts := true) (arts := arts) (level := .private)
  let exportMods : NameSet := plan.modules.foldl (fun s m => s.insert m.name) {}
  let modName (c : Name) : Option Name := do
    let i ← env.getModuleIdxFor? c
    env.header.moduleNames[i.toNat]?
  let (ident, names, diags) := exportIdentity cat plan env
  unless diags.isEmpty do throw <| IO.userError s!"lookup diagnostics: {diags}"
  let mut found := false
  for gid in cat.order do
    let g := cat.get! gid
    if sourceLine != "all" && toString g.capsule.startLine != sourceLine then continue
    if g.members.isEmpty then continue
    found := true
    let ns := names.getD gid #[]
    unless ns.size == g.members.size do
      throw <| IO.userError s!"group {gid}: matched {ns.size}/{g.members.size} members"
    let memberSet : Std.HashMap Name Name := ns.foldl
      (fun s (n, mr) => s.insert n mr.local_) {}
    let rec resolve (fuel : Nat) (c : Name) : Except String Ref := do
      match fuel with
      | 0 => throw "depth"
      | fuel + 1 =>
        if let some l := memberSet[c]? then return .self l
        if let some (g', l) := ident[c]? then return .dep g' l
        if let some mm := modName c then
          if !exportMods.contains mm then return .base c
        if isReservedName env c then
          match reservedBase env c with
          | some (b, s) => return .res (← resolve fuel b) s
          | none => throw s!"reserved {c} without base"
        throw s!"unresolvable {c}"
    let mut members : Array EncMember := #[]
    for (n, mr) in ns do
      let some ci := env.find? n | throw <| IO.userError s!"missing exported constant {n}"
      let cls := match mr.cls with
        | "pub" => NameClass.pub | "pubAux" => .pubAux | _ => .scoped
      members := members.push { local_ := mr.local_, cls, info := canonLevelParams ci }
    let .ok bytes := encodeGroup baseId members (resolve 64)
        (WireCtx.ofMembers members cat.wireDep) |
      throw <| IO.userError "exported group encoding failed"
    let dest := if sourceLine == "all" then s!"{destination}/{g.capsule.startLine}.grp"
      else destination
    IO.FS.writeBinFile (FilePath.mk dest) bytes
    IO.println s!"line={g.capsule.startLine} captured={g.declId} exported={groupIdOf bytes} members={members.size}"
  unless found do throw <| IO.userError s!"no captured declaration group at line {sourceLine}"
