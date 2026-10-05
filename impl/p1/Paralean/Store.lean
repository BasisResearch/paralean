module

public import Lean
public import Paralean.Model

@[expose] public section

/-!
Local content-addressed store.

```
<root>/objects/<gid>.grp   binary group encoding; file name = SHA-256 of the bytes
<root>/meta/<gid>.json     GroupRec (capsule, deps, diagnostics)
<root>/files/<seq>.json    FileRec, one per capture run, in capture order
<root>/audit/objects, <root>/audit/meta
                           groups that capture rejected: kept for audit (the validator's
                           kernel re-check of N3), never in the publishable namespace
```

Objects are immutable: a write of an existing ID is checked byte-for-byte, and every read
re-hashes the bytes.
-/

namespace Paralean
open Lean System

structure Store where
  root : FilePath
  /-- Also read the audit namespace (rejected groups); only the audit replay sets it. -/
  auditRead : Bool := false

namespace Store

def objPath (s : Store) (gid : String) : FilePath := s.root / "objects" / s!"{gid}.grp"
def metaPath (s : Store) (gid : String) : FilePath := s.root / "meta" / s!"{gid}.json"

/-- Audit namespace for rejected groups: same layout, never published or exported. -/
def audit (s : Store) : Store := { root := s.root / "audit" }

/-- Where to read an object or metadata file: the publishable namespace, else (audit
reads only) the audit namespace. -/
def readPath (s : Store) (p : Store → FilePath) : IO FilePath := do
  let main := p s
  if s.auditRead && !(← main.pathExists) then return p s.audit
  return main

def init (s : Store) : IO Unit := do
  IO.FS.createDirAll (s.root / "objects")
  IO.FS.createDirAll (s.root / "meta")
  IO.FS.createDirAll (s.root / "files")

def putObject (s : Store) (bytes : ByteArray) : IO String := do
  let gid := groupIdOf bytes
  let p := s.objPath gid
  if ← p.pathExists then
    let old ← IO.FS.readBinFile p
    unless old == bytes do
      throw <| IO.userError s!"store: object {gid} exists with different bytes"
  else
    let tmp := p.withExtension "tmp"
    IO.FS.writeBinFile tmp bytes
    IO.FS.rename tmp p
  return gid

def getObject (s : Store) (gid : String) : IO ByteArray := do
  let bytes ← IO.FS.readBinFile (← s.readPath (·.objPath gid))
  let h := groupIdOf bytes
  unless h == gid do
    throw <| IO.userError s!"store: object {gid} fails hash verification (got {h})"
  return bytes

def hasObject (s : Store) (gid : String) : IO Bool := (s.objPath gid).pathExists

def putMeta (s : Store) (g : GroupRec) : IO Unit :=
  IO.FS.writeFile (s.metaPath g.gid) (toJson g).pretty

def getMeta (s : Store) (gid : String) : IO GroupRec := do
  let txt ← IO.FS.readFile (← s.readPath (·.metaPath gid))
  match Json.parse txt >>= fromJson? with
  | .ok g => return g
  | .error e => throw <| IO.userError s!"store: bad meta {gid}: {e}"

def fileRecs (s : Store) : IO (Array (Nat × FileRec)) := do
  let dir := s.root / "files"
  unless ← dir.pathExists do return #[]
  let mut out := #[]
  for e in ← dir.readDir do
    if let some seq := (e.fileName.dropEnd 5).toString.toNat? then
      let txt ← IO.FS.readFile e.path
      match Json.parse txt >>= fromJson? with
      | .ok (r : FileRec) => out := out.push (seq, r)
      | .error err => throw <| IO.userError s!"store: bad file record {e.path}: {err}"
  return out.qsort (·.1 < ·.1)

def putFileRec (s : Store) (r : FileRec) : IO Nat := do
  let recs ← s.fileRecs
  let seq := recs.foldl (fun m (k, _) => max m (k + 1)) 0
  IO.FS.writeFile (s.root / "files" / s!"{seq}.json") (toJson r).pretty
  return seq

/-- The latest capture of each `(workspace, file)`; older captures are superseded revisions. -/
def currentFiles (s : Store) : IO (Array FileRec) := do
  let recs ← s.fileRecs
  let mut latest : Std.HashMap (String × String) (Nat × FileRec) := {}
  for (seq, r) in recs do
    latest := latest.insert (r.workspace, r.file) (seq, r)
  return (latest.toArray.map (·.2)).qsort (·.1 < ·.1) |>.map (·.2)

end Store

/-- Loaded view of the published groups. -/
structure Catalog where
  metas : Std.HashMap String GroupRec := {}
  /-- Order in which groups were captured (a valid topological order). -/
  order : Array String := #[]

def Catalog.load (s : Store) (files : Array FileRec) : IO Catalog := do
  -- metas in file/capture order, then a dependency-respecting order (DFS post-order)
  let mut metas : Std.HashMap String GroupRec := {}
  let mut seq : Array String := #[]
  for f in files do
    for gid in f.groups do
      unless metas.contains gid do
        metas := metas.insert gid (← s.getMeta gid)
        seq := seq.push gid
  let mut order := #[]
  let mut done : Std.HashSet String := {}
  for root in seq do
    if done.contains root then continue
    let mut stack : Array (String × Bool) := #[(root, false)]
    while !stack.isEmpty do
      let (g, post) := stack.back!
      stack := stack.pop
      if post then
        unless done.contains g do done := done.insert g; order := order.push g
      else if !done.contains g then
        stack := stack.push (g, true)
        if let some m := metas[g]? then
          for d in (m.deps ++ m.feDeps).reverse do
            if metas.contains d && !done.contains d then stack := stack.push (d, false)
  return { metas, order }

def Catalog.get! (c : Catalog) (gid : String) : GroupRec := c.metas.getD gid default

/-- Wire form of references to members of stored groups (OPEN-22/23): a dependency member
`(package ID, local)` is `(group ID, canonical index)`. -/
def wireDepOf (lookup : String → Option GroupRec) : String → Name → Option (String × Nat) :=
  fun pid l => do
    let g ← lookup pid
    let i ← g.members.findIdx? (·.local_ == l)
    pure (g.declId, i)

/-- Inverse wire context of a stored group `g`: its members by canonical index, and a
dependency's group ID resolved through `g`'s own (kernel and frontend) dependency pins. -/
def GroupRec.unwire (g : GroupRec) (lookup : String → Option GroupRec) : UnwireCtx where
  selfLocal i := g.members[i]?.map (·.local_)
  dep id i := (g.deps ++ g.feDeps).findSome? fun d => do
    let m ← lookup d
    if m.declId == id then pure (d, ← m.members[i]?.map (·.local_)) else none

def Catalog.wireDep (c : Catalog) : String → Name → Option (String × Nat) := wireDepOf (c.metas[·]?)
def Catalog.unwire (c : Catalog) (g : GroupRec) : UnwireCtx := g.unwire (c.metas[·]?)

/-- Dependency closure (kernel + frontend), in catalogue order. -/
partial def Catalog.closure (c : Catalog) (roots : Array String) (conservative := false) :
    Except String (Array String) := do
  let mut seen : Std.HashSet String := {}
  let mut stack := roots
  while !stack.isEmpty do
    let g := stack.back!
    stack := stack.pop
    if seen.contains g then continue
    seen := seen.insert g
    let some r := c.metas[g]? | throw s!"closure: missing group {g}"
    stack := stack ++ r.deps ++ r.feDeps
    if conservative then stack := stack ++ r.feDepsConservative
  return c.order.filter seen.contains

/-- Two different groups in one closure define the same public name: a transitive
version conflict. -/
def Catalog.conflicts (c : Catalog) (gids : Array String) : Array (Name × String × String) :=
  Id.run do
    let mut owner : Std.HashMap Name String := {}
    let mut out := #[]
    for g in gids do
      for n in (c.get! g).publicNames do
        match owner[n]? with
        | some h => if h != g then out := out.push (n, h, g)
        | none => owner := owner.insert n g
    return out

end Paralean
