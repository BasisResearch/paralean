import Lean
import Paralean.Capture
import Paralean.Crdt

/-!
Capture driver: elaborate a workspace file against the pinned base plus a *transparent
prelude* made of every currently published group (source replay of their capsules), and
store every completed command group.
-/

namespace Paralean
open Lean Elab System

/-- Relocation namespaces a capsule must open: relocated groups among its dependencies. -/
def relocatedDepsOf (cat : Catalog) (g : GroupRec) (conservative : Bool) : Array Name :=
  let ds := g.deps ++ g.feDeps ++ (if conservative then g.feDepsConservative else #[])
  ds.foldl (init := #[]) fun acc d =>
    match cat.metas[d]? with
    | some m => if m.capsule.relocate && !acc.contains m.relocNs then acc.push m.relocNs else acc
    | none => acc

/-- Outcome of replaying one stored group from its capsule. -/
structure ReplayRes where
  gid : String
  ok : Bool
  diags : Array Diag
  /-- Replayed declaration ID (if a group was produced). -/
  replayedDeclId : Option String := none
  /-- Provided by a stock-built module (initializer groups), not re-elaborated in-process. -/
  materialized : Bool := false
  /-- The group this replay re-captured (its members carry re-derived statement hashes);
      `none` unless the replayed command produced a group. -/
  replayed : Option GroupRec := none
  deriving Inhabited

/-- Elaborate a source chunk into the session, routing the command at byte offset `mainAt`
through `analyze` (with the stored package ID) and everything else to scaffolding. -/
unsafe def replayCapsule (sess : Session) (fc : FileCtx) (g : GroupRec) (src : String) (mainAt : Nat) :
    IO (Session × ReplayRes) := do
  let inputCtx := Parser.mkInputContext src s!"<capsule {g.short}>"
  let sessRef ← IO.mkRef sess
  let resRef ← IO.mkRef ({ gid := g.gid, ok := false, diags := #[] } : ReplayRes)
  let fc := { fc with input := src, fileMap := inputCtx.fileMap, file := s!"<capsule {g.short}>" }
  let fcRef ← IO.mkRef fc
  let mainSeen ← IO.mkRef false
  let replayStep (r : CmdResult) : IO Unit := do
    let sess ← sessRef.get
    let errs := r.msgs.filter (·.severity == .error)
    if r.startPos ≥ mainAt && r.startPos < mainAt + g.capsule.text.utf8ByteSize &&
        (← resRef.get).replayedDeclId.isNone && !(← mainSeen.get) then
      mainSeen.set true
      let (sess', fc', out) ← analyze sess (← fcRef.get) r (pidOverride? := some g.gid)
      fcRef.set fc'
      sessRef.set sess'
      match out with
      | .group g' bytes' =>
        let ok := g'.declId == g.declId
        if !ok && (← IO.getEnv "PARALEAN_DEBUG").isSome then
          let nameOf (r : Ref) : Except String Name := pure (Name.mkSimple (toString r))
          if let .ok dg := decodeGroup bytes' (g'.unwire fun _ => none) nameOf then
            for (l, _, ci) in dg.members do
              let h := (g'.members.find? (·.local_ == l)).map (·.hash) |>.getD ""
              if !g.members.any (fun o => o.local_ == l && o.hash == h) then
                IO.eprintln s!"REPLAYED {l}\n  type: {ci.type}\n  value: {ci.value?.getD (mkConst `none)}"
        let d : Diag := {
          severity := "capsule", code := "replay-mismatch"
          msg := s!"replayed declaration {g'.declId.take 12} ≠ stored {g.declId.take 12}; \
            differing members: {(g'.members.filter fun m => !g.members.any fun o =>
              o.local_ == m.local_ && o.hash == m.hash).map (·.local_)}"
          file := g.capsule.file, line := g.capsule.startLine }
        resRef.set {
          gid := g.gid, ok := ok, replayedDeclId := some g'.declId, replayed := some g'
          diags := if ok then #[] else #[d] }
      | .failed ds =>
        let ds' := ds.map fun (d : Diag) => { d with
          severity := "capsule", code := s!"replay-{d.code}", file := g.capsule.file
          line := g.capsule.startLine }
        resRef.set { gid := g.gid, ok := false, diags := ds' }
      | .skipped why =>
        let ok := g.members.isEmpty
        let d : Diag := {
          severity := "capsule", code := "replay-empty"
          msg := s!"replayed command produced nothing ({why})"
          file := g.capsule.file, line := g.capsule.startLine }
        resRef.set { gid := g.gid, ok := ok, diags := if ok then #[] else #[d] }
    else
      for c in r.newConsts do
        sessRef.modify fun s => { s with scaffold := s.scaffold.insert c.name }
      unless errs.isEmpty do
        let mut ds := #[]
        for m in errs do
          let msg := (← m.toString).trimAscii.toString
          ds := ds.push ({
            severity := "capsule", code := "replay-scaffold-error", msg := msg
            file := g.capsule.file, line := g.capsule.startLine } : Diag)
        resRef.modify fun x => { x with diags := x.diags ++ ds }
  let st ← runCommands (← sessRef.get).cmdState inputCtx {} fun r => do
    replayStep r
    return none
  let sess ← sessRef.get
  let mut res ← resRef.get
  unless ← mainSeen.get do
    res := { res with ok := false, diags := res.diags.push {
      severity := "capsule", code := "replay-no-main", file := g.capsule.file
      line := g.capsule.startLine, msg := "the capsule's command was not found when re-elaborating" } }
  return ({ sess with cmdState := st }, { res with ok := res.ok && res.diags.all (·.severity != "capsule") })

/-- Groups provided as real (stock-built) modules instead of through the prelude. -/
structure MatResult where
  imports : Array Import
  arts : NameMap ImportArtifacts
  covered : Array String
  identOf : Environment → Std.HashMap Name (String × Name)
  /-- Wire information of the covered packages (see `Session.pkgs`). -/
  pkgs : Std.HashMap String (String × Array Name) := {}
  buildMs : Nat := 0
  diags : Array Diag

abbrev Materializer := Catalog → Array String → IO MatResult

/-- Groups with initializer effects (they must cross a module boundary). -/
def initClosure (cat : Catalog) (sel : Array String) : Array String := Id.run do
  let isInit (g : GroupRec) := g.touched.any fun (n, _) =>
    n == `Lean.regularInitAttr || n == `Lean.builtinInitAttr
  let roots := sel.filter fun g => isInit (cat.get! g)
  if roots.isEmpty then return #[]
  match cat.closure roots with
  | .ok c => return c.filter sel.contains
  | .error _ => return #[]

/-- Header line for an import. -/
def importSpec (i : Import) : String :=
  (if i.isExported then "public " else "") ++ (if i.isMeta then "meta " else "") ++ "import " ++
  (if i.importAll then "all " else "") ++ toString i.module

/-- Module flag and import specs of the most recently opened header. -/
initialize modulePrefs : IO.Ref (Bool × Array String) ← IO.mkRef (false, #[])

initialize baseEnvCache : IO.Ref (Std.HashMap String Environment) ← IO.mkRef {}

def hostOptions : Options :=
  Elab.async.set {} false

/-- Import the base header of `input`; returns the session start state. -/
unsafe def openSession (input : String) (fileName : String) (module : Name)
    (wsModules : Array Name := #[]) (wsBaseImports : Name → Array Name := fun _ => #[])
    (extraImports : Array Import := #[]) (arts : NameMap ImportArtifacts := {}) :
    IO (Session × Parser.InputContext × Parser.ModuleParserState × Array Name × Array Diag × Array Name) := do
  enableInitializersExecution
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let all := headerToImports header
  -- imports of other workspace files are satisfied by the transparent prelude
  let wsImports := (all.filter fun i => wsModules.contains i.module).map (·.module)
  let mut baseImports := all.filter fun i => !wsModules.contains i.module
  -- host-injected imports (`Paralean.Remote`, materialized modules) are not capsule imports
  let ownImports := baseImports
  baseImports := baseImports ++ extraImports
  -- a workspace import brings its own base imports with it
  for w in wsImports do
    for m in wsBaseImports w do
      unless baseImports.any (·.module == m) do baseImports := baseImports.push { module := m }
  let imports := (ownImports.filter (fun i => !i.isMeta)).map (·.module)
  let imports := imports.foldl (fun acc m => if acc.contains m then acc else acc.push m) #[]
  -- Imported environments are pure values but their regions are never freed; import each
  -- distinct base once per process.
  let key := toString (HeaderSyntax.isModule header) ++ ":" ++
    toString (baseImports.map fun i => s!"{i.module}/{i.isExported}/{i.isMeta}/{i.importAll}")
  let (env, messages) ← match (← baseEnvCache.get)[key]? with
    | some env => pure (env.setMainModule module, messages)
    | none => do
      let (env, messages') ← processHeaderCore (HeaderSyntax.startPos header) baseImports
        (HeaderSyntax.isModule header) hostOptions messages inputCtx (mainModule := module) (arts := arts)
      unless messages'.hasErrors do baseEnvCache.modify (·.insert key env)
      pure (env, messages')
  let mut diags := #[]
  for m in messages.toList do
    if m.severity == .error then
      diags := diags.push ({ severity := "reject", code := "header", msg := (← m.toString), file := fileName } : Diag)
  let cmdState := Command.mkState env messages hostOptions
  let cmdState := { cmdState with infoState := { cmdState.infoState with enabled := true } }
  modulePrefs.set (HeaderSyntax.isModule header, baseImports.map importSpec)
  return ({ cmdState, mainModule := module }, inputCtx, parserState, imports, diags, wsImports)

/-- Decide which published groups enter the prelude: exclude conflicting public names
and groups whose base imports are not available, together with their dependents. -/
def preludeSelection (cat : Catalog) (imports : Array Name) (env : Environment)
    (own : Std.HashSet String := {}) : Array String × Array String × Array Diag := Id.run do
  let mut owners : Std.HashMap Name (Array String) := {}
  for gid in cat.order do
    unless own.contains gid do
      for n in (cat.get! gid).publicNames do
        owners := owners.insert n ((owners.getD n #[]).push gid)
  let mut excluded : Std.HashSet String := {}
  let mut diags := #[]
  for (n, gs) in owners.toArray do
    if gs.size > 1 then
      for g in gs do excluded := excluded.insert g
      diags := diags.push ({
        severity := "reject", code := "version-conflict"
        msg := s!"public name {n} has {gs.size} concurrent heads: {gs.map (·.take 12)}" } : Diag)
  for gid in cat.order do
    let g := cat.get! gid
    for m in g.capsule.imports do
      unless imports.contains m || (env.getModuleIdx? m).isSome do
        excluded := excluded.insert gid
        diags := diags.push ({
          severity := "info", code := "base-mismatch"
          msg := s!"group {gid.take 12} needs base import {m}" } : Diag)
  -- propagate exclusion to dependents; groups that depend on this file's own previous
  -- groups are deferred until the file re-produces them
  let mut sel := #[]
  let mut deferred := #[]
  let mut ownish : Std.HashSet String := own
  for gid in cat.order do
    if own.contains gid then continue
    let g := cat.get! gid
    let ds := g.deps ++ g.feDeps
    if excluded.contains gid || ds.any excluded.contains then
      excluded := excluded.insert gid
    else if ds.any ownish.contains then
      ownish := ownish.insert gid
      deferred := deferred.push gid
    else sel := sel.push gid
  return (sel, deferred, diags)

/-- Capture one workspace file into the store. -/
unsafe def captureFile (store : Store) (ws : String) (relFile : String) (path : FilePath)
    (module : Name) (log : String → IO Unit := fun _ => pure ())
    (targets : Array TargetContract := #[]) (materialize? : Option Materializer := none)
    (remote : Bool := false) : IO FileRec := do
  store.init
  let input ← IO.FS.readFile path
  let allFiles ← store.currentFiles
  let wsModules := (allFiles.filter (·.workspace == ws)).map (·.module)
  let wsFiles := allFiles.filter (·.workspace == ws)
  let rec baseOf (fuel : Nat) (m : Name) : Array Name :=
    match fuel, wsFiles.find? (·.module == m) with
    | fuel + 1, some f => f.imports ++ f.wsImports.flatMap (baseOf fuel)
    | _, _ => #[]
  -- transparent workspaces: `remote%` declarations bring their own closure; no prelude
  let remoteImports : Array Import := if remote then #[{ module := `Paralean.Remote }] else #[]
  let (sess0, inputCtx, parserState, imports, hdrDiags, wsImports) ←
    openSession input relFile module wsModules (baseOf 32) (extraImports := remoteImports)
  let registry : Store := match ← IO.getEnv "PARALEAN_STORE" with
    | some r => { root := r }
    | none => store
  let sess0 ← if remote then do
      let recs ← registry.pubs
      let ren := renamesOf (← metasFor registry recs) recs
      pure { sess0 with remoteStore? := some registry, remoteRenames := ren }
    else pure sess0
  if !hdrDiags.isEmpty then
    return {
      workspace := ws, file := relFile, module, imports, groups := #[], skipped := #[]
      diags := hdrDiags, prelude := #[] }
  -- Transparent prelude: every published group of every workspace, except this file's
  -- previous capture (it is being re-captured).
  let own : Std.HashSet String := (allFiles.filter fun f => f.workspace == ws && f.file == relFile)
    |>.foldl (fun s f => f.groups.foldl (·.insert ·) s) {}
  let files := allFiles.filter fun f => !(f.workspace == ws && f.file == relFile)
  let cat ← Catalog.load store (allFiles)
  let (sel, deferred, selDiags) := if remote then (#[], #[], #[]) else
    preludeSelection cat imports sess0.cmdState.env own
  let _ := files
  -- initializer groups cross a real module boundary
  let mut sel := sel
  let mut sess0 := sess0
  let mut selDiags := selDiags
  let initGs := initClosure cat sel
  if let some mat := materialize? then
    if !initGs.isEmpty then
      let mr ← mat cat initGs
      selDiags := selDiags ++ mr.diags
      if !mr.covered.isEmpty then
        let (s1, _, _, _, d1, _) ← openSession input relFile module wsModules (baseOf 32)
          (extraImports := mr.imports) (arts := mr.arts)
        if d1.isEmpty then
          let inits := mr.covered.filter fun gid => (cat.get! gid).touched.any fun (n, _) =>
            n == `Lean.regularInitAttr || n == `Lean.builtinInitAttr
          sess0 := { s1 with index := mr.identOf s1.cmdState.env, pkgs := mr.pkgs, initGroups := inits }
          sel := sel.filter (!mr.covered.contains ·)
        else selDiags := selDiags ++ d1
  let baseEnv := sess0.cmdState.env
  let (isModule, specs) ← modulePrefs.get
  -- non-module files carry no explicit `public`; Init is implicit
  let specs := specs.filter fun sp => !(sp.endsWith " Init")
  let fc0 : FileCtx := {
    workspace := ws, file := relFile, module, imports, input
    fileMap := inputCtx.fileMap, baseEnv, isModule, importSpecs := specs }
  let mut sess := { sess0 with targets }
  let mut diags := selDiags
  let mut nOk := 0
  for gid in sel do
    let g := cat.get! gid
    let deps := relocatedDepsOf cat g false
    let src := renderCapsule g deps
    let (sess', res) ← replayCapsule sess fc0 g src (capsuleTextOffset g deps)
    sess := sess'
    if res.ok then nOk := nOk + 1
    diags := diags ++ res.diags
    if materialize?.isNone && g.touched.any (fun (n, _) => n == `Lean.regularInitAttr || n == `Lean.builtinInitAttr) then
      diags := diags.push {
        severity := "unsupported", code := "initialize-in-prelude", file := g.capsule.file
        line := g.capsule.startLine
        msg := "`initialize` effects run only when a module is imported; through the transparent \
          prelude they do not run, so consumers in this file cannot observe them" }
  -- Transparent workspaces: published declarations of other files are visible by name.
  -- Stand-in for a fork hook at name resolution: load (`remote%`) every published group
  -- whose public name occurs in this file's text, at the root, before the file.
  -- (superseded by the name-resolution hook when `PARALEAN_VISIBILITY` is set)
  if remote && (← IO.getEnv "PARALEAN_VISIBILITY").isNone then
    let recs ← registry.pubs
    let here := (recs.filter (·.file == relFile)).map (·.pid)
    -- identifier-like tokens of the file
    let mut words : Std.HashSet String := {}
    let mut cur := ""
    for c in input.toList do
      if c.isAlphanum || c == '_' || c == '.' || c == '\'' then cur := cur.push c
      else
        unless cur.isEmpty do words := words.insert cur
        cur := ""
    unless cur.isEmpty do words := words.insert cur
    let mut chunk := ""
    let mut nTrig := 0
    for r in recs do
      if here.contains r.pid then continue
      let g ← registry.getMeta r.pid
      let hit := g.publicNames.any fun n =>
        words.contains n.toString || words.contains (n.getString!)
      if hit then
        chunk := chunk ++ s!"remote% \"{r.pid}\"\n"
        nTrig := nTrig + 1
    if nTrig > 0 then
      let ictx := Parser.mkInputContext chunk "<visible published declarations>"
      let sref ← IO.mkRef sess
      let fref ← IO.mkRef { fc0 with input := chunk, fileMap := ictx.fileMap }
      let errs ← IO.mkRef (#[] : Array Diag)
      let st ← runCommands sess.cmdState ictx {} fun r => do
        let (s', f', out) ← analyze (← sref.get) (← fref.get) r
        sref.set s'; fref.set f'
        if let .failed ds := out then errs.modify (· ++ ds)
        return none
      sess := { (← sref.get) with cmdState := st }
      diags := diags ++ (← errs.get)
      log s!"visible: {nTrig} published groups loaded by name (remote%)"
  -- The file itself; deferred prelude groups are replayed as soon as their dependencies
  -- on this file have been re-produced with identical package IDs.
  let sessRef ← IO.mkRef sess
  let fcRef ← IO.mkRef fc0
  let groupsRef ← IO.mkRef (#[] : Array String)
  let rejectedRef ← IO.mkRef (#[] : Array String)
  let skippedRef ← IO.mkRef (#[] : Array (Name × Nat))
  let diagsRef ← IO.mkRef diags
  let okRef ← IO.mkRef nOk
  let pendingRef ← IO.mkRef deferred
  let writesRef ← IO.mkRef (#[] : Array (GroupRec × ByteArray))
  let availRef ← IO.mkRef (sel.foldl (·.insert ·) ({} : Std.HashSet String))
  -- test hook: cancel the capture after N commands (models a killed or cancelled worker)
  let cancelAfter := (← IO.getEnv "PARALEAN_CANCEL_AFTER").bind (·.toNat?)
  let nCmds ← IO.mkRef 0
  let _ ← runCommands sess.cmdState inputCtx parserState fun r => do
    nCmds.modify (· + 1)
    if let some k := cancelAfter then
      if (← nCmds.get) > k then
        throw <| IO.userError s!"capture cancelled after {k} commands"
    let (sess', fc', out) ← analyze (← sessRef.get) (← fcRef.get) r
    sessRef.set sess'
    fcRef.set fc'
    match out with
    | .group g bytes =>
      -- nothing is written until the file record: a cancelled or failed capture stages
      -- nothing in the publishable store
      writesRef.modify (·.push (g, bytes))
      if g.diags.any (·.severity == "reject") then
        rejectedRef.modify (·.push g.gid)
      else
        groupsRef.modify (·.push g.gid)
        availRef.modify (·.insert g.gid)
      diagsRef.modify (· ++ g.diags)
      log s!"  {g.kind} {g.short} {g.cmdKind.getString!} L{g.capsule.startLine} \
        members={g.members.size} pub={g.publicNames.size} realized={g.realized.size} \
        deps={g.deps.size} fe={g.feDeps.size} bytes={g.encSize}\
        {if g.diags.any (·.severity == "reject") then " REJECTED" else ""}"
    | .skipped why =>
      skippedRef.modify (·.push (r.stx.getKind, lineOf (← fcRef.get).fileMap r.startPos))
      if why != "scope" && why != "no-effect" then
        log s!"  skipped {r.stx.getKind} ({why})"
    | .failed ds =>
      diagsRef.modify (· ++ ds)
      for d in ds do log s!"  {d}"
    -- deferred prelude groups whose dependencies are now available
    let mut st? : Option Command.State := none
    let mut progress := true
    while progress do
      progress := false
      for gid in ← pendingRef.get do
        let g := cat.get! gid
        if (g.deps ++ g.feDeps).all (← availRef.get).contains then
          let deps := relocatedDepsOf cat g false
          let src := renderCapsule g deps
          let base := (← sessRef.get)
          -- capsules are rendered from the root scope; restore the file's scopes after
          let start := st?.getD r.stateAfter
          let start := { start with scopes := sess0.cmdState.scopes }
          let (sess'', res) ← replayCapsule { base with cmdState := start } (← fcRef.get) g src
            (capsuleTextOffset g deps)
          sessRef.set sess''
          st? := some { sess''.cmdState with scopes := r.stateAfter.scopes }
          pendingRef.modify (·.filter (· != gid))
          availRef.modify (·.insert gid)
          if res.ok then okRef.modify (· + 1)
          diagsRef.modify (· ++ res.diags)
          log s!"  prelude (deferred) {g.short} {if res.ok then "ok" else "MISMATCH"}"
          progress := true
    return st?
  for gid in ← pendingRef.get do
    let g := cat.get! gid
    diagsRef.modify (·.push {
      severity := "info", code := "deferred-unavailable", file := g.capsule.file
      line := g.capsule.startLine
      msg := s!"group {gid.take 12} depends on a previous revision of this file and is not visible" })
  let nPre := sel.size + deferred.size - (← pendingRef.get).size
  if nPre > 0 then
    log s!"prelude: {← okRef.get}/{nPre} groups replayed with identical declaration IDs"
  -- remote mode: earlier publications of this file are now `remote%` elements; keep them
  let prev := if remote then (allFiles.filter fun f => f.workspace == ws && f.file == relFile).flatMap (·.groups)
    else #[]
  let newGroups ← groupsRef.get
  let groups := (prev.filter (!newGroups.contains ·)) ++ newGroups
  let rec_ : FileRec := {
    workspace := ws, file := relFile, module, imports, groups := groups
    skipped := ← skippedRef.get, diags := ← diagsRef.get, prelude := sel ++ deferred
    rejected := ← rejectedRef.get, wsImports, preludeOk := ← okRef.get }
  -- Commit: accepted groups into the publishable namespace, rejected groups into the
  -- audit namespace (never published, exported or used as dependencies), then the file
  -- record, which is what publishes.
  for (g, bytes) in ← writesRef.get do
    let dst := if g.diags.any (·.severity == "reject") then store.audit else store
    dst.init
    let declId ← dst.putObject bytes
    unless declId == g.declId do throw <| IO.userError "store: declaration ID mismatch"
    dst.putMeta g
  let _ ← store.putFileRec rec_
  return rec_

end Paralean
