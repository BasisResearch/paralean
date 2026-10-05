import Lean
import Paralean.Replay
import Paralean.Crdt

/-!
Stock-Lean export.

1. Select the current published groups and reject transitive version conflicts.
2. Lay them out in modules. A group's segment index is the least index not below its
   file predecessor, not below same-file dependencies, and above dependencies from other
   files. Cross-file edges strictly increase the index, so the module graph is acyclic.
   B→A→B therefore becomes three modules from two agent files.
3. Render each group's capsule (scoped names relocated), write a Lake package pinned to the
   same toolchain, and build it with stock `lake build` in a clean directory.
4. Import the built `.olean`s in-process and re-encode each group's constants from the
   stock-built environment. The result must equal the stored declaration ID.
-/

namespace Paralean
open Lean System

structure ExportModule where
  name : Name
  groups : Array String
  imports : Array Name
  /-- Export modules that are earlier segments of the same agent file (`import all`). -/
  sameFile : Array Name := #[]
  isModule : Bool := false
  /-- Base import lines (module system: as written by the agent). -/
  baseSpecs : Array String := #[]

structure ExportPlan where
  modules : Array ExportModule
  moduleOf : Std.HashMap String Name
  diags : Array Diag

def allDeps (g : GroupRec) : Array String := g.deps ++ g.feDeps ++ g.feDepsConservative

def planExport (cat : Catalog) (gids : Array String) (isBase : Name → Bool := fun _ => false) :
    ExportPlan := Id.run do
  let mut diags := #[]
  for (n, a, b) in cat.conflicts gids do
    diags := diags.push ({
      severity := "reject", code := "version-conflict"
      msg := s!"{n} defined by {a.take 12} and {b.take 12}" } : Diag)
  -- a file is its path in the shared codebase (transparent workspaces share files)
  let fileOf (g : GroupRec) := ("", g.capsule.file)
  let mut seg : Std.HashMap String Nat := {}
  let mut last : Std.HashMap (String × String) Nat := {}
  for gid in gids do
    let g := cat.get! gid
    let f := fileOf g
    let mut k := last.getD f 0
    for d in allDeps g do
      if let some kd := seg[d]? then
        let dg := cat.get! d
        k := max k (if fileOf dg == f then kd else kd + 1)
    seg := seg.insert gid k
    last := last.insert f k
  -- module names: first segment keeps the agent module name; later ones are submodules
  let mut segsOf : Std.HashMap (String × String) (Array Nat) := {}
  for gid in gids do
    let g := cat.get! gid
    let f := fileOf g
    let k := seg[gid]!
    let ks := segsOf.getD f #[]
    unless ks.contains k do segsOf := segsOf.insert f (ks.push k)
  let mut moduleOf : Std.HashMap String Name := {}
  let mut order : Array Name := #[]
  let mut groupsOf : Std.HashMap Name (Array String) := {}
  let mut wsOfModule : Std.HashMap Name String := {}
  for gid in gids do
    let g := cat.get! gid
    let f := fileOf g
    let ks := (segsOf.getD f #[]).qsort (· < ·)
    let k := seg[gid]!
    -- an agent module that is also a base module (re-exporting a Mathlib file) is renamed
    -- under the same root, which keeps Lean's generated instance names unchanged
    let base := if isBase g.capsule.module then
        g.capsule.module.getRoot ++ `ParaleanExport ++ g.capsule.module.replacePrefix g.capsule.module.getRoot .anonymous
      else g.capsule.module
    let m := if ks[0]? == some k then base else base ++ Name.mkSimple s!"Part{k}"
    if let some w := wsOfModule[m]? then
      if w != g.capsule.file then
        diags := diags.push ({
          severity := "reject", code := "module-clash"
          msg := s!"module {m} comes from files {w} and {g.capsule.file}" } : Diag)
    wsOfModule := wsOfModule.insert m g.capsule.file
    moduleOf := moduleOf.insert gid m
    unless groupsOf.contains m do order := order.push m
    groupsOf := groupsOf.insert m ((groupsOf.getD m #[]).push gid)
  let modules := order.map fun m => Id.run do
    let gs := groupsOf.getD m #[]
    let mut imps : Array Name := #[]
    let mut same : Array Name := #[]
    let mut specs : Array String := #[]
    let mut isModule := false
    for gid in gs do
      let g := cat.get! gid
      isModule := isModule || g.capsule.isModule
      for sp in g.capsule.importSpecs do
        unless specs.contains sp do specs := specs.push sp
      for i in g.capsule.imports do
        unless i == `Init || imps.contains i do imps := imps.push i
      for d in allDeps g do
        if let some dm := moduleOf[d]? then
          unless dm == m || imps.contains dm do
            imps := imps.push dm
            let dg := cat.get! d
            if dg.capsule.file == g.capsule.file then
              same := same.push dm
    return { name := m, groups := gs, imports := imps, sameFile := same, isModule, baseSpecs := specs }
  return { modules, moduleOf, diags }

def modulePath (root : FilePath) (m : Name) : FilePath :=
  (m.components.foldl (fun p c => p / c.toString (escape := false)) root).withExtension "lean"

def renderModule (cat : Catalog) (m : ExportModule)
    (ren : Std.HashMap String (Std.HashMap Name Name) := {}) : String := Id.run do
  let mut out := ""
  if m.isModule then
    out := out ++ "module\n"
    let exportMods := m.imports.filter fun i => !(m.baseSpecs.any (·.endsWith s!" {i}"))
    for sp in m.baseSpecs do out := out ++ sp ++ "\n"
    for i in exportMods do
      out := out ++ (if m.sameFile.contains i then s!"public import all {i}\n" else s!"public import {i}\n")
  else
    for i in m.imports do out := out ++ s!"import {i}\n"
  out := out ++ s!"/-! Generated by paralean export. Each block is one captured group; the comment
names its package ID and the agent source location. Capture elaborates synchronously;
auxiliary names (`_proof_n`) differ under asynchronous elaboration, so it is pinned here. -/
set_option Elab.async false\n\n"
  for gid in m.groups do
    let g := cat.get! gid
    out := out ++ renderCapsule (renamedGroup ren g) (relocatedDepsOf cat g true) ++ "\n"
  return out

structure ExportResult where
  plan : ExportPlan
  buildOk : Bool
  buildLog : String
  buildMs : Nat
  verified : Nat
  effectOnly : Nat
  mismatches : Array Diag
  bytes : Nat

def toolchainPin : String := "leanprover/lean4-nightly:nightly-2026-10-03"

/-- Write the export package. Returns the plan. -/
def writeExport (cat : Catalog) (gids : Array String) (out : FilePath)
    (mathlib? : Option FilePath := none) (ren : Std.HashMap String (Std.HashMap Name Name) := {}) :
    IO (ExportPlan × Nat) := do
  let mut baseMods : NameSet := {}
  for gid in gids do
    let m := (cat.get! gid).capsule.module
    let isB ← try (← findOLean m).pathExists catch _ => pure false
    if isB then baseMods := baseMods.insert m
  let plan := planExport cat gids baseMods.contains
  if out.toString.length < 4 then throw <| IO.userError "refusing suspicious export dir"
  if ← out.pathExists then IO.FS.removeDirAll out
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "lean-toolchain") (toolchainPin ++ "\n")
  let roots := plan.modules.map fun m => s!"\"{m.name}\""
  -- reuse the pinned Mathlib checkout and its already-fetched packages: no network
  let (req, pkgs) := match mathlib? with
    | some p => (s!"\n[[require]]\nname = \"mathlib\"\npath = \"{p}\"\n",
                 s!"packagesDir = \"{p / ".lake" / "packages"}\"\n")
    | none => ("", "")
  IO.FS.writeFile (out / "lakefile.toml")
    s!"name = \"paralean_export\"\n{pkgs}defaultTargets = [\"Export\"]\n{req}\n[[lean_lib]]\nname = \"Export\"\nroots = [{", ".intercalate roots.toList}]\n"
  let mut bytes := 0
  for m in plan.modules do
    let p := modulePath out m.name
    if let some d := p.parent then IO.FS.createDirAll d
    let txt := renderModule cat m ren
    bytes := bytes + txt.utf8ByteSize
    IO.FS.writeFile p txt
  return (plan, bytes)

/-- Identity of an exported constant: `_pl_<short>` tag (if relocated) and normalized name. -/
def exportKey (m : Name) (n : Name) : Option String × Name :=
  let tag := n.components.findSome? fun c => match c with
    | .str .anonymous s => plComponent? s
    | _ => none
  (tag, normName m n)

/-- Explicit artifacts of the built export modules (as Lake passes them). -/
def exportArts (plan : ExportPlan) (out : FilePath) : IO (NameMap ImportArtifacts) := do
  let libDir := out / ".lake" / "build" / "lib" / "lean"
  let mut arts : NameMap ImportArtifacts := {}
  for m in plan.modules do
    let o := modulePath libDir m.name |>.withExtension "olean"
    let mut files := #[o]
    for ext in ["olean.server", "olean.private"] do
      let f := o.withExtension ext
      if ← f.pathExists then files := files.push f
    arts := arts.insert m.name (.ofArrays #[files])
  return arts

/-- Map the constants of the exported modules (in `env`) back to group identities. Returns
export name ↦ (package id, local), the per-group member names, and missing-member diags. -/
def exportIdentity (cat : Catalog) (plan : ExportPlan) (env : Environment)
    (ren : Std.HashMap String (Std.HashMap Name Name) := {}) :
    Std.HashMap Name (String × Name) × Std.HashMap String (Array (Name × MemberRec)) × Array Diag := Id.run do
  let exportMods : NameSet := plan.modules.foldl (fun s m => s.insert m.name) {}
  let modName (c : Name) : Option Name := do
    let i ← env.getModuleIdxFor? c
    env.header.moduleNames[i.toNat]?
  let mut byKey : Std.HashMap (Name × Option String × Name) Name := {}
  for (n, _) in env.constants.map₁.toList do
    if let some m := modName n then
      if exportMods.contains m then
        let (tag, l) := exportKey m n
        byKey := byKey.insert (m, tag, l) n
  let mut hygQueue : Std.HashMap (Name × Option String × Name) (Array Name) := {}
  for m in plan.modules do
    let some idx := env.getModuleIdx? m.name | continue
    let some md := env.header.moduleData[idx.toNat]? | continue
    for n in md.constNames do
      let (tag, l) := exportKey m.name n
      if l.components.getLast? == some `_hyg then
        hygQueue := hygQueue.insert (m.name, tag, l) ((hygQueue.getD (m.name, tag, l) #[]).push n)
  let mut ident : Std.HashMap Name (String × Name) := {}
  let mut names : Std.HashMap String (Array (Name × MemberRec)) := {}
  let mut diags := #[]
  for m in plan.modules do
    for gid in m.groups do
      let g := cat.get! gid
      let tag := if g.capsule.relocate then some g.short else none
      let mut ns := #[]
      for mr in g.members do
        let hyg? : Option Name := match mr.local_ with
          | .num p _ => if p.components.getLast? == some `_hyg then some p else none
          | _ => none
        let found := match hyg? with
          | some base =>
            let q := hygQueue.getD (m.name, tag, base) #[]
            if q.isEmpty then none else some q[0]!
          | none => byKey[(m.name, tag, renameName (ren.getD gid {}) mr.local_)]?
        if let some base := hyg? then
          let q := hygQueue.getD (m.name, tag, base) #[]
          unless q.isEmpty do hygQueue := hygQueue.insert (m.name, tag, base) (q.extract 1 q.size)
        match found with
        | some n => ident := ident.insert n (gid, mr.local_); ns := ns.push (n, mr)
        | none => diags := diags.push ({
            severity := "reject", code := "export-missing"
            file := g.capsule.file, line := g.capsule.startLine
            msg := s!"exported module {m.name} lacks member {mr.local_}" } : Diag)
      names := names.insert gid ns
  return (ident, names, diags)

/-- Re-encode every exported group from the stock-built environment. -/
unsafe def verifyExport (cat : Catalog) (plan : ExportPlan) (out : FilePath)
    (ren : Std.HashMap String (Std.HashMap Name Name) := {}) : IO (Nat × Nat × Array Diag) := do
  let arts ← exportArts plan out
  enableInitializersExecution
  let isMod := plan.modules.any (·.isModule)
  let env ← importModules (plan.modules.map fun m => { module := m.name, importAll := isMod })
    {} (loadExts := true) (arts := arts) (level := .private)
  let exportMods : NameSet := plan.modules.foldl (fun s m => s.insert m.name) {}
  let modName (c : Name) : Option Name := do
    let i ← env.getModuleIdxFor? c
    env.header.moduleNames[i.toNat]?
  let (ident, names, diags0) := exportIdentity cat plan env ren
  let mut diags := diags0
  let mut ok := 0
  let mut effectOnly := 0
  for m in plan.modules do
    for gid in m.groups do
      let g := cat.get! gid
      if g.members.isEmpty then effectOnly := effectOnly + 1; continue
      let ns := names.getD gid #[]
      if ns.size != g.members.size then continue
      let memberSet : Std.HashMap Name Name := ns.foldl (fun s (n, mr) => s.insert n mr.local_) {}
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
        let some ci := env.find? n | continue
        let cls := match mr.cls with | "pub" => NameClass.pub | "pubAux" => .pubAux | _ => .scoped
        members := members.push { local_ := mr.local_, cls, info := canonLevelParams ci }
      members := members.qsort fun a b => a.local_.toString < b.local_.toString
      match encodeGroup baseId members (resolve 64) with
      | .error e => diags := diags.push ({
          severity := "reject", code := "export-encode"
          file := g.capsule.file, line := g.capsule.startLine, msg := e } : Diag)
      | .ok bytes =>
        let d := groupIdOf bytes
        if d == g.declId then ok := ok + 1
        else diags := diags.push ({
          severity := "reject", code := "export-mismatch"
          file := g.capsule.file, line := g.capsule.startLine
          msg := s!"stock-built group {d.take 12} ≠ stored {g.declId.take 12}" } : Diag)
  return (ok, effectOnly, diags)

def runBuild (out : FilePath) : IO (Bool × String × Nat) := do
  let t0 ← IO.monoMsNow
  let elan := (← IO.getEnv "HOME").getD "" ++ "/.elan/bin/lake"
  let r ← IO.Process.output { cmd := elan, args := #["build"], cwd := out }
  let t1 ← IO.monoMsNow
  return (r.exitCode == 0, r.stdout ++ r.stderr, t1 - t0)

end Paralean
