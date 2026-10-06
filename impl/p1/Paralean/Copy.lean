import Lean
import Paralean.Driver
import Paralean.Materialize
import Paralean.Validate
import Paralean.Rga

/-!
Working copies for transparent workspaces (P3).

A copy is `DIR/work` (a git repository with the agent's files), `DIR/cache` (its cache of
the store, `PARALEAN_STORE`) and `DIR/state.json` (agent, persistent Lamport clock, applied
records, hidden elements, applied renames). Records travel through the P2 store with
`plr` (`impl/p3-remote`); `impl/p3-remote/scripts/ws.sh` runs the steps below in order.

* `ws-capture`: capture a working file in remote mode; write each new group's capsule
  object (`{"rec", "deps"}`) and list the packages to stage and validate.
* `ws-plan`: after validation, compute each new record's placement (anchor, rootPath,
  lineage keys, Lamport time) and revisions. A validator response for a group whose remote
  dependency was superseded meanwhile is a stale response and is rejected.
* `ws-sync`: after `plr pull`: one git commit per newly known record, authored by its
  publisher, containing the projection (working form) only; then rewrite the working files
  as projection plus drafts; report renames (and rename the losing author's drafts) and
  invalidated elements.
* `ws-hash`, `ws-delete`, `ws-check`: projection hash, tombstone arguments, elaboration of a
  working file with every axiom its constants use.

An author edits a published declaration by deleting its element block and writing the new
text; the element stays hidden in that copy until the revision publishes.
-/

namespace Paralean.Copy
open Lean System P3

structure State where
  agent : String
  agentId : String
  lamport : Nat := 0
  applied : Array String := #[]
  hidden : Array (String × Array String) := #[]
  /-- (name, group) pairs whose rename this copy has already applied to its drafts. -/
  renamed : Array (String × String) := #[]
  deriving ToJson, FromJson, Inhabited

def State.load (dir : FilePath) : IO State := do
  match Json.parse (← IO.FS.readFile (dir / "state.json")) >>= fromJson? with
  | .ok s => return s
  | .error e => throw <| IO.userError s!"bad copy state: {e}"

/-- Written to a temporary file and renamed: the clock is durable before it is used. -/
def State.save (s : State) (dir : FilePath) : IO Unit := do
  IO.FS.writeFile (dir / "state.json.tmp") (toJson s).pretty
  IO.FS.rename (dir / "state.json.tmp") (dir / "state.json")

def State.hiddenIn (s : State) (f : String) : Array String :=
  (s.hidden.find? (·.1 == f)).map (·.2) |>.getD #[]

def git (work : FilePath) (args : Array String) : IO String := do
  let r ← IO.Process.output { cmd := "git", args := #["-C", work.toString] ++ args }
  if r.exitCode != 0 then throw <| IO.userError s!"git {args}: {r.stderr}"
  return r.stdout

def moduleOf (file : String) : Name :=
  let f := if file.endsWith ".lean" then (file.dropEnd 5).toString else file
  (f.splitOn "/").foldl Name.mkStr .anonymous

def init (dir : FilePath) (agent : String) : IO Unit := do
  let t ← trust
  let some (id, _) := t.agents.find? (·.2 == agent) | throw <| IO.userError s!"agent {agent} is not in the trust file"
  IO.FS.createDirAll (dir / "work")
  IO.FS.createDirAll (dir / "cache" / "p3" / "records")
  ({ root := dir / "cache" } : Store).init
  let _ ← git (dir / "work") #["init", "-q", "-b", "main"]
  let _ ← git (dir / "work") #["config", "user.name", agent]
  let _ ← git (dir / "work") #["config", "user.email", s!"{agent}@paralean.invalid"]
  let _ ← git (dir / "work") #["commit", "-q", "--allow-empty", "--date", "@0 +0000", "-m", "paralean: empty workspace"]
  ({ agent, agentId := id } : State).save dir

/-! ## Capture -/

unsafe def capture (dir : FilePath) (file : String) (log : String → IO Unit) : IO Json := do
  let st ← State.load dir
  let cache : Store := { root := dir / "cache" }
  let r ← captureFile cache st.agent file (dir / "work" / file) (moduleOf file) (log := log)
    (remote := true) (materialize? := some (materialize cache))
  let v ← Remote.view
  let published : Std.HashSet String := v.known.markers.foldl (·.insert ·.pid) {}
  let mut batch : Std.HashMap String (String × String) := {}
  let mut out := #[]
  for pid in r.groups do
    if published.contains pid then continue
    let g ← cache.getMeta pid
    -- the capsule object is the package's metadata JSON, as stored
    let bytes ← IO.FS.readBinFile (cache.metaPath pid)
    let cid := capsuleIdOf bytes
    IO.FS.createDirAll (cache.root / "p3" / "capsules")
    IO.FS.writeBinFile (cache.root / "p3" / "capsules" / s!"{cid}.json") bytes
    batch := batch.insert pid (g.declId, cid)
    -- capsules of the exact dependency closure, dependencies first (the job pins them)
    let mut order : Array String := #[]
    let mut stack : Array (String × Bool) := (g.deps ++ g.feDeps).reverse.map (·, false)
    let mut seen : Std.HashSet String := {}
    while !stack.isEmpty do
      let (d, post) := stack.back!
      stack := stack.pop
      if post then
        unless order.contains d do order := order.push d
        continue
      if seen.contains d then continue
      seen := seen.insert d
      stack := stack.push (d, true)
      let dm ← if batch.contains d then cache.getMeta d else Remote.getMetaIO d
      for e in (dm.deps ++ dm.feDeps).reverse do
        unless seen.contains e do stack := stack.push (e, false)
    let mut deps := #[]
    for d in order do
      match batch[d]? <|> (← Remote.pkgIndex.get)[d]? with
      | some (_, c) => deps := deps.push c
      | none => throw <| IO.userError s!"capture: dependency {(d.take 12).toString} of {g.short} is neither published nor in this batch"
    out := out.push (Json.mkObj [("pid", pid), ("group", g.declId), ("capsule", cid), ("deps", toJson deps),
      ("names", toJson (g.publicNames.map toString)), ("line", g.capsule.startLine)])
  let rejected := r.diags.filter (·.severity == "reject") |>.map toString
  return Json.mkObj [("packages", Json.arr out), ("rejected", toJson rejected), ("rejectedPids", toJson r.rejected)]

/-! ## Placement of new records -/

def anchorName (group : String) : Name := `Paralean.anchor ++ Name.mkSimple s!"g{(group.take 32).toString}"

/-- Elements in a working file: (line, group). -/
def elementLines (txt : String) : Array (Nat × String) := Id.run do
  let lines := txt.splitOn "\n"
  let mut out := #[]
  for i in [0:lines.length] do
    let l := lines[i]!
    if l.startsWith "-- paralean:published " then
      out := out.push (i + 1, (l.drop "-- paralean:published ".length).toString.trimAscii.toString)
  return out

def jsonPath (p : Array (String × Nat × String)) : Json :=
  Json.arr (p.map fun (g, l, a) => Json.arr #[g, l, a])

unsafe def plan (dir : FilePath) (file : String) (receiptsPath : FilePath) (planPath : FilePath)
    (log : String → IO Unit) : IO Json := do
  let mut st ← State.load dir
  let cache : Store := { root := dir / "cache" }
  let v ← Remote.view
  let rs ← match ← readJson receiptsPath with
    | .arr a => pure a
    | j => pure #[j]
  let txt ← IO.FS.readFile (dir / "work" / file)
  -- an earlier step of this publication (records already planned and published)
  let prior : Option Json ← do
    let p := dir / "pending.json"
    if ← p.pathExists then pure (some (← readJson p)) else pure none
  let priorEntries := (prior.bind fun j => (j.getObjValAs? (Array Json) "entries").toOption).getD #[]
  let txt := (prior.bind fun j => (j.getObjValAs? String "text").toOption).getD txt
  let elems := elementLines txt
  -- accepted packages, in file order
  let mut pkgs : Array (GroupRec × String × String × String) := #[]   -- (meta, capsule, receipt, job)
  let mut rejected : Array Json := #[]
  for r in rs do
    let capsule ← ofExcept receiptsPath (r.getObjValAs? String "capsule")
    let g ← match ← loadCapsule cache.root capsule with
      | .ok g => pure g
      | .error e => throw <| IO.userError e
    let ok := (r.getObjValAs? Bool "accepted").toOption.getD false
    if !ok then
      rejected := rejected.push (Json.mkObj [("pid", g.gid), ("reason", (r.getObjValAs? String "reason").toOption.getD "")])
      continue
    pkgs := pkgs.push (g, capsule, ← ofExcept receiptsPath (r.getObjValAs? String "receipt"),
      ← ofExcept receiptsPath (r.getObjValAs? String "job"))
  pkgs := pkgs.qsort (fun a b => a.1.capsule.startLine < b.1.capsule.startLine)
  -- stale responses: a remote dependency superseded since the request
  let byPid : Std.HashMap String Marker := v.known.markers.foldl (fun m mk => m.insert mk.pid mk) {}
  let batchPids : Std.HashSet String := pkgs.foldl (fun s p => s.insert p.1.gid) {}
  let mut stale : Std.HashSet String := {}
  for (g, _, _, _) in pkgs do
    for d in g.deps ++ g.feDeps do
      if batchPids.contains d then
        if stale.contains d then stale := stale.insert g.gid
        continue
      match byPid[d]? with
      | some m =>
        unless v.live.contains m.group do
          stale := stale.insert g.gid
          let names := ((v.metas[d]?).map (·.publicNames)).getD #[]
          rejected := rejected.push (Json.mkObj [("pid", g.gid), ("reason",
            s!"stale response: validated against {names} ({(m.group.take 12).toString}), which is no longer a live head here")])
      | none => pure ()
  -- the clock covers every known record, then advances once per new record; persisted first
  let maxKnown := v.known.markers.foldl (fun m r => max m r.lamport) (v.known.tombs.foldl (fun m t => max m t.lamport) 0)
  let mut lam := max st.lamport maxKnown
  let me := st.agentId
  let mut batch : Array (Nat × String × Array (String × Nat × String)) := #[]  -- (line, group, rootPath)
  for e in priorEntries do
    let ls := (e.getObjValAs? (Array Nat) "lines").toOption.getD #[0]
    let rp ← ofExcept receiptsPath (do
      let a ← e.getObjValAs? (Array Json) "rootPath"
      a.mapM fun x => do
        let (g, l, au) ← triple x
        let gs : String ← fromJson? g
        return (gs, l, au))
    batch := batch.push (ls[0]!, (e.getObjValAs? String "group").toOption.getD "", rp)
  let mut entries : Array Json := #[]
  for (g, capsule, rid, jid) in pkgs do
    if stale.contains g.gid then continue
    lam := lam + 1
    let names := Rga.declaredNames g
    -- revisions: the live head of this file that the author sees under the same name
    let mut revs : Array Json := #[]
    let mut lkeys : Array Json := #[]
    let mut revRoot : Option (Array (String × Nat × String)) := none
    for n in names do
      let head? := v.elements file |>.find? fun m =>
        m.group != g.declId && (v.metas[m.pid]?.any fun h => (Rga.declaredNames h).contains n) &&
          !((v.renames.getD m.pid {}).contains n)
      match head? with
      | some h =>
        let parents := h.revisions.filter fun rid => (v.known.revs[rid]?.any (·.name == n))
        revs := revs.push (Json.mkObj [("name", toJson n), ("parents", toJson parents)])
        let (l, a) := Rga.lineageKey h n
        lkeys := lkeys.push (Json.arr #[toJson n, l, a])
        if revRoot.isNone then revRoot := some h.rootPath
      | none =>
        revs := revs.push (Json.mkObj [("name", toJson n), ("parents", toJson (#[] : Array String))])
        lkeys := lkeys.push (Json.arr #[toJson n, lam, me])
    if names.isEmpty then
      revs := revs.push (Json.mkObj [("name", toJson (anchorName g.declId)), ("parents", toJson (#[] : Array String))])
    let line := g.capsule.startLine
    let (anchor, rootPath) : Option String × Array (String × Nat × String) := match revRoot with
      | some p => (none, p)
      | none =>
        -- nearest element or earlier record of this batch above it, by its lineage root
        let above := (elems.filter (·.1 < line)).map (fun (l, gr) => (l, gr, ((v.known.byGroup[gr]?).map (·.rootPath)).getD #[]))
          ++ (batch.filter (·.1 < line))
        match (above.qsort (·.1 < ·.1)).back? with
        | some (_, _, p) =>
          if p.isEmpty then (none, #[(g.declId, lam, me)])
          else (some p.back!.1, p.push (g.declId, lam, me))
        | none => (none, #[(g.declId, lam, me)])
    batch := batch.push (line, g.declId, rootPath)
    entries := entries.push (Json.mkObj [("group", g.declId), ("capsule", capsule), ("receipt", rid), ("job", jid),
      ("file", file), ("anchor", match anchor with | some a => Json.str a | none => Json.null),
      ("lamport", lam), ("author", me), ("rootPath", jsonPath rootPath), ("lineageKeys", Json.arr lkeys),
      ("revisions", Json.arr revs), ("pid", g.gid), ("lines", Json.arr #[g.capsule.startLine, g.capsule.endLine])])
    log s!"plan: {g.publicNames} at L{line}: lamport {lam}, {if revRoot.isSome then "revision" else "insert"}"
  st := { st with lamport := lam }
  st.save dir
  IO.FS.writeFile planPath (Json.arr entries).pretty
  -- the original text and the planned ranges, so sync can move published text out of the drafts
  IO.FS.writeFile (dir / "pending.json") (Json.mkObj [("file", file), ("text", txt), ("entries", Json.arr (priorEntries ++ entries))]).compress
  return Json.mkObj [("planned", entries.size), ("rejected", Json.arr rejected), ("lamport", lam)]

/-! ## Sync -/

/-- Split a working file into drafts after removing the text of `published` ranges
(start line ↦ (group, end line)): text that followed a just-published declaration now follows
its element. -/
def resplit (txt : String) (published : Std.HashMap Nat (String × Nat)) : Array (String × String) := Id.run do
  let lines := (txt.splitOn "\n").toArray
  let mut drafts : Array (String × String) := #[]
  let mut anchor := ""
  let mut cur := ""
  let mut i := 0
  let mut inElem := false
  let mut inAuto := false
  let flush (drafts : Array (String × String)) (anchor cur : String) :=
    if cur.trimAscii.toString != "" then drafts.push (anchor, cur.trimAscii.toString ++ "\n") else drafts
  while i < lines.size do
    let l := lines[i]!
    let ln := i + 1
    if inElem then
      if l.startsWith "-- paralean:end " then inElem := false
      i := i + 1
    else if inAuto then
      if l.startsWith "-- paralean:auto-end" then inAuto := false
      i := i + 1
    else if l.startsWith "-- paralean:auto-begin" then inAuto := true; i := i + 1
    else if l.startsWith "-- paralean:published " then
      drafts := flush drafts anchor cur
      cur := ""
      anchor := (l.drop "-- paralean:published ".length).toString.trimAscii.toString
      inElem := true
      i := i + 1
    else if let some (gid, b) := published[ln]? then
      drafts := flush drafts anchor cur
      cur := ""
      anchor := gid
      i := b
    else
      if !(l.startsWith "import " || l.startsWith "public import " || l == "module" ||
           l.startsWith "-- paralean: published projection") then
        cur := cur ++ l ++ "\n"
      i := i + 1
  return flush drafts anchor cur

/-- The projection in working form, without the elements this copy hides (being edited). -/
def workingProjection (v : Rga.View) (file : String) (hidden : Array String) : String :=
  let v' := { v with live := hidden.foldl (·.erase ·) v.live }
  v'.workingProjection file

structure RecordRef where
  id : String
  lamport : Nat
  author : String
  file : String
  isTomb : Bool
  group : String

unsafe def sync (dir : FilePath) (log : String → IO Unit) : IO Json := do
  let mut st ← State.load dir
  let t ← trust
  let work := dir / "work"
  let v ← Remote.view
  let k := v.known
  -- git: one commit per newly applied record, in (Lamport, author) order
  let recs : Array RecordRef := (k.markers.map fun m =>
      { id := m.id, lamport := m.lamport, author := m.author, file := m.file, isTomb := false, group := m.group }) ++
    (k.tombs.map fun x => { id := x.id, lamport := x.lamport, author := x.author, file := x.file, isTomb := true, group := x.target })
  let newRecs := (recs.filter fun r => !st.applied.contains r.id).qsort fun a b =>
    keyLt (a.lamport, a.author) (b.lamport, b.author) || ((a.lamport, a.author) == (b.lamport, b.author) && a.id < b.id)
  -- the working files as the agent left them (drafts), before commits rewrite the tree
  let mut texts : Std.HashMap String String := {}
  for f in (v.files ++ (← workFiles work)) do
    let p := work / f
    if ← p.pathExists then texts := texts.insert f (← IO.FS.readFile p)
  let mut applied : Std.HashSet String := st.applied.foldl (·.insert ·) {}
  for r in newRecs do
    applied := applied.insert r.id
    let sub : Known := { k with markers := k.markers.filter (applied.contains ·.id),
                                tombs := k.tombs.filter (applied.contains ·.id) }
    let sv := Rga.View.of sub v.metas
    let p := work / r.file
    if let some d := p.parent then IO.FS.createDirAll d
    -- the committed tree is the projection; the working tree keeps drafts on top of it
    IO.FS.writeFile p (sv.workingProjection r.file)
    let _ ← git work #["add", r.file]
    let names := ((k.byGroup[r.group]?).bind (v.metas[·.pid]?)).map (·.publicNames.map toString) |>.getD #[]
    let who := t.agentName r.author
    let _ ← git work #["commit", "-q", "--allow-empty", s!"--author={who} <{who}@paralean.invalid>",
      "--date", s!"@{r.lamport} +0000", "-m",
      s!"paralean: {if r.isTomb then "delete" else "insert"} {names} in {r.file}\n\nParalean-Group: {r.group}\nParalean-Lamport: {r.lamport}\nParalean-Record: {r.id}"]
  st := { st with applied := recs.map (·.id) }
  -- drafts (re-split around just-published text if a publication is pending)
  let pending? : Option Json ← do
    let p := dir / "pending.json"
    if ← p.pathExists then pure (some (← readJson p)) else pure none
  let mut pendingDone := false
  let mut files := v.files
  let mut out : Array Json := #[]
  for f in (← workFiles work) do unless files.contains f do files := files.push f
  -- renames this copy must apply to its own drafts (it lost a name)
  let mut myRenames : Std.HashMap Name Name := {}
  let mut diags : Array String := #[]
  for (x, loser, winner) in v.losers do
    let some lm := k.byGroup[loser]? | continue
    if lm.author != st.agentId then continue
    let new := Rga.fresh x loser
    if st.renamed.contains (x.toString, loser) then continue
    let wa := ((k.byGroup[winner]?).map (t.agentName ·.author)).getD "?"
    diags := diags.push s!"rename: your declaration `{x}` ({(loser.take 12).toString}) lost the name to {wa}'s \
      ({(winner.take 12).toString}, older lineage); it is now `{new}`. Your drafts were renamed; \
      tombstone it and republish under a new name to resolve the registry conflict."
    myRenames := myRenames.insert x new
    st := { st with renamed := st.renamed.push (x.toString, loser) }
  for f in files do
    let path := work / f
    let cur := texts.getD f ""
    let mut drafts := splitDrafts cur
    if let some pj := pending? then
      if (pj.getObjValAs? String "file").toOption == some f then
        let txt := (pj.getObjValAs? String "text").toOption.getD cur
        let mut ranges : Std.HashMap Nat (String × Nat) := {}
        for e in (pj.getObjValAs? (Array Json) "entries").toOption.getD #[] do
          let g := (e.getObjValAs? String "group").toOption.getD ""
          let ls := (e.getObjValAs? (Array Nat) "lines").toOption.getD #[]
          if k.byGroup.contains g && ls.size == 2 then ranges := ranges.insert ls[0]! (g, ls[1]!)
        drafts := resplit txt ranges
        pendingDone := true
    -- the Lean rename of the losing author's drafts
    unless myRenames.isEmpty do
      drafts := drafts.map fun (a, d) => (a, renameText .anonymous myRenames d)
    -- elements removed from the working file are being edited: keep them hidden while live
    let shown := (elementLines cur).map (·.2)
    let before := st.hiddenIn f
    let wasRendered := (v.elements f).map (·.group) |>.filter fun g => k.markers.any (·.group == g)
    let mut hidden := before.filter v.live.contains
    if !cur.isEmpty then
      for g in wasRendered do
        if !shown.contains g && st.applied.contains ((k.byGroup[g]?).map (·.id) |>.getD "") &&
            !newRecs.any (·.group == g) && !hidden.contains g then
          hidden := hidden.push g
    st := { st with hidden := (st.hidden.filter (·.1 != f)).push (f, hidden) }
    let proj := workingProjection v f hidden
    IO.FS.writeFile path (renderWorking proj drafts)
    out := out.push (Json.mkObj [("file", f), ("elements", (v.elements f).size), ("hidden", hidden.size),
      ("drafts", drafts.size)])
  if pendingDone then IO.FS.removeFile (dir / "pending.json")
  -- invalidation: live elements whose closure holds a group that is no longer live
  let byPid : Std.HashMap String Marker := k.markers.foldl (fun m mk => m.insert mk.pid mk) {}
  for m in k.markers do
    unless v.live.contains m.group do continue
    let some g := v.metas[m.pid]? | continue
    let mut todo := g.deps ++ g.feDeps
    let mut seen : Std.HashSet String := {}
    while !todo.isEmpty do
      let d := todo.back!
      todo := todo.pop
      if seen.contains d then continue
      seen := seen.insert d
      if let some dm := byPid[d]? then
        unless v.live.contains dm.group do
          let by_ := k.markers.find? fun e => (v.graph.anc.getD e.group {}).contains dm.group
          let dn := ((v.metas[d]?).map (·.publicNames)).getD #[]
          diags := diags.push s!"invalidated: {g.publicNames} in {m.file} ({(m.group.take 12).toString}) depends on \
            {dn} ({(dm.group.take 12).toString}), {match by_ with
              | some e => s!"superseded by {(e.group.take 12).toString} ({t.agentName e.author})"
              | none => "deleted"}"
      match (← Remote.metaCache.get)[d]? with
      | some dg => todo := todo ++ dg.deps ++ dg.feDeps
      | none => pure ()
  st.save dir
  for d in diags do log d
  let h := IO.FS.Handle.mk (dir / "diagnostics.log") .append
  for d in diags do (← h).putStrLn d
  return Json.mkObj [("applied", newRecs.size), ("files", Json.arr out), ("diagnostics", toJson diags)]
where
  workFiles (work : FilePath) : IO (Array String) := do
    let mut out := #[]
    for p in ← work.walkDir (fun p => return p.fileName != some ".git") do
      if p.extension == some "lean" then
        out := out.push ((p.toString.drop (work.toString.length + 1)).toString)
    return out

/-! ## Hash, delete, check -/

def hash (file : String) : IO (String × String) := do
  let v ← Remote.view
  let p := v.projection file
  return (Sha256.hashHex p.toUTF8, p)

def delete (dir : FilePath) (file : String) (name : Name) : IO Json := do
  let mut st ← State.load dir
  let v ← Remote.view
  let some m := v.elements file |>.find? fun m =>
      (v.metas[m.pid]?.any fun g => (g.publicNames.map (renameName (v.renames.getD m.pid {}))).contains name)
    | throw <| IO.userError s!"no live declaration {name} in {file}"
  let maxKnown := v.known.markers.foldl (fun m r => max m r.lamport) (v.known.tombs.foldl (fun m t => max m t.lamport) 0)
  let lam := max st.lamport maxKnown + 1
  st := { st with lamport := lam }
  st.save dir
  return Json.mkObj [("target", m.group), ("lamport", lam), ("file", file)]

/-- Elaborate a working file as the fork would (with `Paralean.Remote`); report errors and
every axiom used by a constant of the file, and any axiom the file itself declares. -/
unsafe def check (dir : FilePath) (file : String) : IO Json := do
  let input ← IO.FS.readFile (dir / "work" / file)
  let (sess, inputCtx, ps, _, hdr, _) ← openSession input file (moduleOf file)
    (extraImports := #[{ module := `Paralean.Remote }])
  let errs ← IO.mkRef (hdr.map toString)
  let st ← runCommands sess.cmdState inputCtx ps fun r => do
    for m in r.msgs do
      if m.severity == .error then
        let pos := m.pos
        errs.modify (·.push s!"{file}:{pos.line}: {(← m.data.toString).take 6000}")
    return none
  let env := st.env
  -- `#print axioms` of every constant of the file: Lean's `collectAxioms`, which follows
  -- module-system interfaces of imports by provenance
  let ctx : Core.Context := { fileName := "<check>", fileMap := default, maxHeartbeats := 0 }
  let axiomsOf (n : Name) : IO (Array Name) := do
    let (a, _) ← (Lean.collectAxioms (m := CoreM) n).toIO ctx { env }
    return a
  let mut axioms : Std.HashMap Name Nat := {}
  let mut localAxioms := #[]
  let mut nConsts : Nat := 0
  for aci in ← env.getLocalConstantInfos do
    let ci := aci.toConstantInfo
    nConsts := nConsts + 1
    if let .axiomInfo _ := ci then localAxioms := localAxioms.push ci.name
    for a in ← axiomsOf ci.name do axioms := axioms.insert a (axioms.getD a 0 + 1)
  let mut placeholders := #[]
  for (a, _) in axioms.toList do
    if !allowedAxioms.contains a then placeholders := placeholders.push a
  -- the constants `remote%` loaded (published elements and their closures)
  let mut elemAxioms : Array Name := #[]
  let mut nLoaded : Nat := 0
  for ((m, _), ns) in (← Remote.verifiedCache.get).toList do
    if m != env.mainModule then continue
    for (_, n) in ns do
      nLoaded := nLoaded + 1
      for a in ← axiomsOf n do unless elemAxioms.contains a do elemAxioms := elemAxioms.push a
  return Json.mkObj [("file", file), ("errors", toJson (← errs.get)), ("constants", nConsts),
    ("axioms", toJson ((axioms.toArray.map (fun (a, k) => (a.toString, k))).qsort (·.1 < ·.1))),
    ("disallowedAxioms", toJson placeholders), ("localAxioms", toJson localAxioms),
    ("loadedConstants", toJson nLoaded), ("loadedAxioms", toJson elemAxioms)]

/-! ## Export -/

/-- Export the copy's published state (every live element and its dependency closure) to a
clean Lake package, build it with the pinned Lean, and re-encode every group from the built
modules. `remote%` never appears in the export: elements are written from their capsules. -/
unsafe def export_ (dir : FilePath) (out : FilePath) (log : String → IO Unit) : IO Json := do
  let v ← Remote.view
  let cache : Store := { root := dir / "cache" }
  let roots := (v.known.markers.filter fun m => v.live.contains m.group).map (·.pid)
  let cat ← Catalog.ofStore cache roots
  for gid in cat.order do discard <| P3.payload cache.root (cat.get! gid).declId
  let mathlib? := (← IO.getEnv "PARALEAN_MATHLIB").map FilePath.mk
  let cat' := { cat with metas := cat.metas.fold (fun m k g => m.insert k (renamedGroup v.renames g)) {} }
  let (plan, bytes) ← writeExport cat' cat'.order out mathlib? v.renames
  log s!"export: {plan.modules.size} modules ({plan.modules.map (·.name)}), {cat.order.size} groups, {bytes} bytes"
  let rejects := plan.diags.filter (·.severity == "reject")
  if !rejects.isEmpty then
    return Json.mkObj [("ok", false), ("diags", toJson (rejects.map toString))]
  let (ok, buildLog, ms) ← runBuild out
  if !ok then
    return Json.mkObj [("ok", false), ("build", buildLog.take 2000 |>.toString)]
  let (nv, ne, ds) ← verifyExport cat' plan out v.renames
  return Json.mkObj [("ok", nv + ne == cat.order.size), ("modules", toJson (plan.modules.map (·.name.toString))),
    ("groups", cat.order.size), ("identical", nv), ("effectOnly", ne), ("buildMs", ms), ("bytes", bytes),
    ("diags", toJson (ds.map toString))]

end Paralean.Copy
