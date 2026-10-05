import Lean
import Paralean.Driver
import Paralean.Validate
import Paralean.Crdt

/-!
Working copies for transparent workspaces (prototype).

A copy is `DIR/work` (a git repository with the agent's files), `DIR/store` (the copy's
replica of the store: objects, metadata, receipts, publication records) and
`DIR/state.json`. `PARALEAN_STORE` must name `DIR/store` (the `remote%` elaborator
reads it).

* `publish F`: capture `F` in remote mode, validate (receipts), add a publication record
  per new group (anchor = nearest published element above it in this copy), remove the
  published text from the drafts, then sync.
* `sync`: apply records not yet applied, in (Lamport, author) order. Each record gives one
  git commit, authored by its publisher, containing only the projection (never
  drafts). Then rewrite the working files: projection plus this agent's drafts, which
  are re-attached after the element they followed.
* `pull OTHER`: anti-entropy (union of the two stores), then sync.
-/

namespace Paralean
open Lean System

structure CopyState where
  author : String
  lamport : Nat := 0
  applied : Array String := #[]
  deriving ToJson, FromJson, Inhabited

def CopyState.load (dir : FilePath) : IO CopyState := do
  match Json.parse (← IO.FS.readFile (dir / "state.json")) >>= fromJson? with
  | .ok s => return s
  | .error e => throw <| IO.userError s!"bad copy state: {e}"

def CopyState.save (s : CopyState) (dir : FilePath) : IO Unit :=
  IO.FS.writeFile (dir / "state.json") (toJson s).pretty

def git (work : FilePath) (args : Array String) : IO String := do
  let r ← IO.Process.output { cmd := "git", args := #["-C", work.toString] ++ args }
  if r.exitCode != 0 then throw <| IO.userError s!"git {args}: {r.stderr}"
  return r.stdout

def copyInit (dir : FilePath) (author : String) : IO Unit := do
  IO.FS.createDirAll (dir / "work")
  (Store.mk (dir / "store")).init
  let _ ← git (dir / "work") #["init", "-q", "-b", "main"]
  let _ ← git (dir / "work") #["config", "user.name", author]
  let _ ← git (dir / "work") #["config", "user.email", s!"{author}@paralean.invalid"]
  ({ author } : CopyState).save dir

def projectionHash (store : Store) (file : String) : IO String := do
  let recs ← store.pubs
  let metas ← metasFor store recs
  return Sha256.hashHex (renderProjection metas recs file).toUTF8

def recOrder (a b : PubRecord) : Bool :=
  a.lamport < b.lamport || (a.lamport == b.lamport && (a.author < b.author ||
    (a.author == b.author && a.pid < b.pid)))

def copySync (dir : FilePath) (log : String → IO Unit := fun _ => pure ())
    (draftsOverride : Std.HashMap String (Array (String × String)) := {}) : IO Nat := do
  let st ← CopyState.load dir
  let store : Store := { root := dir / "store" }
  let work := dir / "work"
  let recs ← store.pubs
  let metas ← metasFor store recs
  let newRecs := (recs.filter fun r => !st.applied.contains r.key).qsort recOrder
  let files := recs.foldl (fun acc r => if acc.contains r.file then acc else acc.push r.file) #[]
  -- keep this agent's drafts
  let mut drafts : Std.HashMap String (Array (String × String)) := {}
  for f in files do
    let p := work / f
    if let some d := draftsOverride[f]? then drafts := drafts.insert f d
    else if ← p.pathExists then drafts := drafts.insert f (splitDrafts (← IO.FS.readFile p))
  -- one commit per newly applied record, authored by its publisher, projection only
  let mut applied := recs.filter fun r => st.applied.contains r.key
  for r in newRecs do
    applied := applied.push r
    let p := work / r.file
    if let some d := p.parent then IO.FS.createDirAll d
    IO.FS.writeFile p (renderProjection metas applied r.file)
    let _ ← git work #["add", r.file]
    let names := (metas.get? r.pid).map (·.publicNames.map toString) |>.getD #[]
    let _ ← git work #["commit", "-q", "--allow-empty", s!"--author={r.author} <{r.author}@paralean.invalid>",
      "-m", s!"paralean: {r.author} publishes {names} in {r.file} ({(r.pid.take 12).toString}, t={r.lamport})"]
  -- working tree: projection + drafts (uncommitted)
  for f in files do
    let proj := renderProjection metas recs f
    IO.FS.writeFile (work / f) (renderWorking proj (drafts.getD f #[]))
  let lam := recs.foldl (fun m r => max m r.lamport) st.lamport
  { st with lamport := lam, applied := recs.map (fun (r : PubRecord) => r.key) }.save dir
  log s!"sync: applied {newRecs.size} new publication(s); {files.size} file(s)"
  return newRecs.size

/-- Draft-only file content: remove the published elements. -/
def onlyDrafts (txt : String) : Array (String × String) := splitDrafts txt

unsafe def copyPublish (dir : FilePath) (file : String) (log : String → IO Unit := fun _ => pure ()) :
    IO (Array String) := do
  let st ← CopyState.load dir
  let store : Store := { root := dir / "store" }
  let work := dir / "work"
  let path := work / file
  let module := (file.dropEnd 5).toString.splitOn "/" |>.foldl Name.mkStr .anonymous
  let r ← captureFile store st.author file path module (log := log) (remote := true)
    (materialize? := some (materialize store))
  if r.diags.any (·.severity == "reject") then
    log s!"publish: {r.rejected.size} rejected group(s) stay drafts"
  let key := (← IO.getEnv "PARALEAN_RECEIPT_KEY").getD ""
  let (nr, refused) ← validateStore store key (log := log)
  log s!"validator: {nr} receipt(s)"
  -- only groups that are not yet published (re-captures keep earlier ones as elements)
  let already := (← store.pubs).map (·.pid)
  let groups := r.groups.filter fun g => !refused.contains g && !already.contains g
  -- anchors: nearest published element (or earlier publication of this batch) above
  let txt ← IO.FS.readFile path
  let lines := txt.splitOn "\n"
  let mut elems : Array (Nat × String) := #[]
  for i in [0:lines.length] do
    let l := lines[i]!
    if l.startsWith "-- paralean:published " then
      elems := elems.push (i + 1, (l.drop "-- paralean:published ".length).toString.trimAscii.toString)
  let mut lamport := st.lamport
  let mut published := #[]
  let mut ranges : Array (Nat × Nat) := #[]
  for gid in groups do
    let g ← store.getMeta gid
    let above := (elems.filter (·.1 < g.capsule.startLine))
    let anchor := (above.qsort (·.1 < ·.1)).back?.map (·.2) |>.getD ""
    lamport := lamport + 1
    store.putPub { pid := gid, file, anchor, lamport, author := st.author }
    elems := elems.push (g.capsule.startLine, gid)
    published := published.push gid
    ranges := ranges.push (g.capsule.startLine, g.capsule.endLine)
  -- Re-split the drafts: published text leaves them (it comes back as an element), and
  -- draft text that followed a newly published declaration now follows its element.
  let starts : Std.HashMap Nat (String × Nat) := (published.zip ranges).foldl
    (fun m (gid, (a, b)) => m.insert a (gid, b)) {}
  let mut drafts : Array (String × String) := #[]
  let mut anchor := ""
  let mut cur := ""
  let mut i := 0
  let mut inElem := false
  let mut inAuto := false
  while i < lines.length do
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
      if cur.trimAscii.toString != "" then drafts := drafts.push (anchor, cur.trimAscii.toString ++ "\n")
      cur := ""
      anchor := (l.drop "-- paralean:published ".length).toString.trimAscii.toString
      inElem := true
      i := i + 1
    else if let some (gid, b) := starts[ln]? then
      if cur.trimAscii.toString != "" then drafts := drafts.push (anchor, cur.trimAscii.toString ++ "\n")
      cur := ""
      anchor := gid
      i := b
    else
      if !(l.startsWith "import " || l.startsWith "public import " || l == "module" ||
           l.startsWith "-- paralean: published projection") then
        cur := cur ++ l ++ "\n"
      i := i + 1
  if cur.trimAscii.toString != "" then drafts := drafts.push (anchor, cur.trimAscii.toString ++ "\n")
  { st with lamport } |>.save dir
  let _ ← copySync dir log (draftsOverride := ({} : Std.HashMap String _).insert file drafts)
  return published

def copyPull (dir other : FilePath) (log : String → IO Unit := fun _ => pure ()) : IO Nat := do
  let a : Store := { root := dir / "store" }
  let b : Store := { root := other / "store" }
  for e in ← (b.root / "objects").readDir do
    let _ ← a.putObject (← IO.FS.readBinFile e.path)
  for sub in ["meta", "receipts", "pubs"] do
    if ← (b.root / sub).pathExists then
      IO.FS.createDirAll (a.root / sub)
      for e in ← (b.root / sub).readDir do
        unless ← (a.root / sub / e.fileName).pathExists do
          IO.FS.writeFile (a.root / sub / e.fileName) (← IO.FS.readFile e.path)
  -- file records too (capsule catalogues), so validation and export see the groups
  let mine := (← a.fileRecs).map (·.2)
  for (_, r) in ← b.fileRecs do
    unless mine.any (fun m => m.workspace == r.workspace && m.file == r.file && m.groups == r.groups) do
      let _ ← a.putFileRec r
  copySync dir log

end Paralean
