module

public import Lean
public import Paralean.Store
public import Paralean.Render
public import Paralean.Sha256

@[expose] public section

/-!
Declaration-level placement CRDT and canonical rendering (transparent workspaces).

Each shared file is a replicated growable list (RGA) whose elements are published package
IDs. A publication record carries the file, an anchor (the nearest *published* element
above it in the author's copy, or the file start), a Lamport time and the author.
Concurrent inserts after one anchor are ordered by descending (Lamport time, author), as
in RGA, so a later insert after the same anchor lands closer to it. The record set is
grow-only; replicas merge by set union.

The published projection of a file is a pure function of the record set and the stored
capsules: canonical imports, then one fixed-text block per element. Drafts live only in
their author's working file, between elements, and are never part of the projection.
-/

namespace Paralean
open Lean System

structure PubRecord where
  pid : String
  file : String
  /-- Package ID of the element above, or `""` for the file start. -/
  anchor : String
  lamport : Nat
  author : String
  deriving ToJson, FromJson, Inhabited, Repr, BEq

def PubRecord.key (r : PubRecord) : String := Sha256.hashHex (toJson r).compress.toUTF8

def Store.putPub (s : Store) (r : PubRecord) : IO Unit := do
  IO.FS.createDirAll (s.root / "pubs")
  IO.FS.writeFile (s.root / "pubs" / s!"{r.key}.json") (toJson r).compress

def Store.pubs (s : Store) : IO (Array PubRecord) := do
  let d := s.root / "pubs"
  unless ← d.pathExists do return #[]
  let mut out := #[]
  for e in ← d.readDir do
    match Json.parse (← IO.FS.readFile e.path) >>= fromJson? with
    | .ok r => out := out.push r
    | .error err => throw <| IO.userError s!"bad publication record {e.path}: {err}"
  return out

/-- RGA order of one file's elements. -/
partial def linearize (recs : Array PubRecord) : Array PubRecord := Id.run do
  let later (a b : PubRecord) : Bool :=   -- a before b among siblings
    a.lamport > b.lamport || (a.lamport == b.lamport && a.author > b.author) ||
    (a.lamport == b.lamport && a.author == b.author && a.pid > b.pid)
  let mut children : Std.HashMap String (Array PubRecord) := {}
  let known : Std.HashSet String := recs.foldl (·.insert ·.pid) {}
  for r in recs do
    -- an anchor that is not (yet) known here attaches to the file start
    let a := if r.anchor == "" || known.contains r.anchor then r.anchor else ""
    children := children.insert a ((children.getD a #[]).push r)
  let rec go (a : String) (fuel : Nat) (acc : Array PubRecord) : Array PubRecord :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      let cs := (children.getD a #[]).qsort later
      cs.foldl (fun acc c => go c.pid fuel (acc.push c)) acc
  go "" (recs.size + 1) #[]

def metasFor (store : Store) (recs : Array PubRecord) : IO (Std.HashMap String GroupRec) := do
  let mut m := {}
  for r in recs do
    unless m.contains r.pid do m := m.insert r.pid (← store.getMeta r.pid)
  return m

/-! ## Name collisions (rule 4)

Unrelated published declarations with the same public name: the lowest
(Lamport time, author, package) keeps the name; every other one is renamed to
`<name>_<author>_<lamport>`, a deterministic function of the replicated set. Its
auxiliaries follow (prefix rename), and published uses of it (groups that depend on the
renamed package) are rewritten in their rendered and loaded text. Declaration identity
is unaffected: dependencies pin packages, and encodings use package identities.
-/

/-- Package ↦ (published Lean name ↦ rendered name). -/
def renamesOf (metas : Std.HashMap String GroupRec) (recs : Array PubRecord) :
    Std.HashMap String (Std.HashMap Name Name) := Id.run do
  let mut owners : Std.HashMap Name (Array PubRecord) := {}
  for r in recs do
    if let some g := metas[r.pid]? then
      for n in g.publicNames do
        let os := owners.getD n #[]
        unless os.any (·.pid == r.pid) do owners := owners.insert n (os.push r)
  let mut out : Std.HashMap String (Std.HashMap Name Name) := {}
  for (n, os) in owners.toList do
    if os.size < 2 then continue
    let sorted := os.qsort fun a b => a.lamport < b.lamport ||
      (a.lamport == b.lamport && (a.author < b.author || (a.author == b.author && a.pid < b.pid)))
    for r in sorted.extract 1 sorted.size do
      let new := match n with
        | .str p s => Name.mkStr p s!"{s}_{r.author}_{r.lamport}"
        | n => n
      out := out.insert r.pid ((out.getD r.pid {}).insert n new)
  return out

/-- Apply a rename map to a Lean name (longest renamed prefix). -/
def renameName (m : Std.HashMap Name Name) (n : Name) : Name := Id.run do
  if m.isEmpty then return n
  let mut p := n
  while !p.isAnonymous do
    if let some q := m[p]? then return n.replacePrefix p q
    p := p.getPrefix
  return n

/-- Rename map in force for `g`'s text: its own renames and those of its dependencies. -/
def textRenames (ren : Std.HashMap String (Std.HashMap Name Name)) (g : GroupRec) :
    Std.HashMap Name Name := Id.run do
  let mut m := ren.getD g.gid {}
  for d in g.deps ++ g.feDeps do
    for (a, b) in (ren.getD d {}).toList do m := m.insert a b
  return m

def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' || c == '.' ||
  Lean.isLetterLike c || Lean.isSubScriptAlnum c

/-- Rewrite identifier tokens that denote a renamed name (written fully qualified or
relative to the namespace `ns`). -/
def renameText (ns : Name) (m : Std.HashMap Name Name) (txt : String) : String := Id.run do
  if m.isEmpty then return txt
  let mut forms : Array (String × String) := #[]
  for (a, b) in m.toList do
    forms := forms.push (a.toString, b.toString)
    if ns.isPrefixOf a && ns != a then
      forms := forms.push ((a.replacePrefix ns .anonymous).toString, (b.replacePrefix ns .anonymous).toString)
  let rewrite (tok : String) : String := Id.run do
    for (f, r) in forms do
      if tok == f then return r
      if tok.startsWith (f ++ ".") then return r ++ (tok.drop f.length).toString
    return tok
  let mut out := ""
  let mut cur := ""
  for c in txt.toList do
    if isIdentChar c then cur := cur.push c
    else
      out := out ++ rewrite cur
      cur := ""
      out := out.push c
  return out ++ rewrite cur

/-- `g` with its rendered names: capsule text rewritten under the renames in force. -/
def renamedGroup (ren : Std.HashMap String (Std.HashMap Name Name)) (g : GroupRec) : GroupRec :=
  let m := textRenames ren g
  if m.isEmpty then g else
  let c := g.capsule
  let text := renameText c.currNamespace m c.text
  -- the value offset moves by the length change of the header part
  let vs := c.valueStart.map fun v =>
    let hdr := String.fromUTF8! (c.text.toUTF8.extract 0 v)
    (renameText c.currNamespace m hdr).utf8ByteSize
  let own := ren.getD g.gid {}
  { g with capsule := { c with text, valueStart := vs },
           publicNames := g.publicNames.map (renameName own) }

/-- Can the element be written as `<published header> := remote% "<pid>"` in place? -/
def headerForm (g : GroupRec) : Bool :=
  g.capsule.valueStart.isSome && g.capsule.localEffects.isEmpty && !g.capsule.relocate &&
  g.kind == "decl"

def elementBegin (pid : String) : String := s!"-- paralean:published {pid}"
def elementEnd (pid : String) : String := s!"-- paralean:end {(pid.take 12).toString}"

/-- Fixed text of one element (a pure function of the stored capsule). -/
def renderElement (g : GroupRec) (r : PubRecord) : String :=
  let c := g.capsule
  let body := match c.valueStart with
    | some v =>
      if headerForm g then
        (String.fromUTF8! (c.text.toUTF8.extract 0 v)).trimAsciiEnd.toString ++ s!" := remote% \"{g.gid}\""
      else s!"remote% \"{g.gid}\""
    | none => s!"remote% \"{g.gid}\""
  if headerForm g then
    -- the capsule's scope with the value replaced; the first line is the group comment
    let inner := renderCapsule { g with capsule := { c with text := body, localEffects := #[] } } #[]
    let inner := "\n".intercalate (inner.splitOn "\n" |>.drop 1)
    s!"{elementBegin g.gid}\n-- {r.author} @{r.lamport}: {g.publicNames.map (·.toString)}\n{inner}{elementEnd g.gid}\n"
  else
    s!"{elementBegin g.gid}\n-- {r.author} @{r.lamport}: {g.publicNames.map (·.toString)}\n{body}\n{elementEnd g.gid}\n"

/-- Canonical published projection of `file`. -/
def renderProjection (metas : Std.HashMap String GroupRec) (recs : Array PubRecord) (file : String) :
    String := Id.run do
  let elems := linearize (recs.filter (·.file == file))
  let isModule := elems.any fun r => (metas[r.pid]?.map (·.capsule.isModule)).getD false
  let mut imports : Array String := #[]
  for r in elems do
    if let some g := metas[r.pid]? then
      let ls := if isModule then g.capsule.importSpecs else g.capsule.imports.map (s!"import {·}")
      for l in ls do
        unless imports.contains l do imports := imports.push l
  imports := imports.qsort (· < ·)
  let mut out := (if isModule then "module\n" else "") ++ String.join (imports.toList.map (· ++ "\n"))
  out := out ++ s!"-- paralean: published projection of {file}\n"
  let ren := renamesOf metas recs
  for r in elems do
    if let some g := metas[r.pid]? then
      out := out ++ "\n" ++ renderElement (renamedGroup ren g) r
  return out

/-- Split a working file into draft segments keyed by the element they follow (`""` =
before the first element). Element blocks and machine-generated scope blocks
(`-- paralean:auto-begin` … `-- paralean:auto-end`) are not drafts. -/
def splitDrafts (txt : String) : Array (String × String) := Id.run do
  let lines := txt.splitOn "\n"
  let mut out : Array (String × String) := #[]
  let mut cur := ""
  let mut after := ""
  let mut inElem := false
  let mut inAuto := false
  for l in lines do
    if inElem then
      if l.startsWith "-- paralean:end " then inElem := false
    else if inAuto then
      if l.startsWith "-- paralean:auto-end" then inAuto := false
    else if l.startsWith "-- paralean:auto-begin" then inAuto := true
    else if l.startsWith "-- paralean:published " then
      if cur.trimAscii.toString != "" then out := out.push (after, cur.trimAscii.toString ++ "\n")
      cur := ""
      inElem := true
      after := (l.drop "-- paralean:published ".length).toString.trimAscii.toString
    else if l.startsWith "import " || l.startsWith "public import " || l.startsWith "meta import " ||
        l == "module" || l.startsWith "-- paralean: published projection" then
      pure ()
    else
      cur := cur ++ l ++ "\n"
  if cur.trimAscii.toString != "" then out := out.push (after, cur.trimAscii.toString ++ "\n")
  return out

/-- Top-level command chunks of draft text: a chunk starts at a line in column 0. -/
def chunks (txt : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut cur := ""
  for l in txt.splitOn "\n" do
    let top := !l.isEmpty && !(l.front == ' ' || l.front == '\t')
    if top && cur.trimAscii.toString != "" then
      out := out.push cur
      cur := ""
    cur := cur ++ l ++ "\n"
  if cur.trimAscii.toString != "" then out := out.push cur
  return out

structure ScopeFrame where
  opener : String
  closer : String
  cmds : Array String := #[]

def scopeCmdPrefixes : List String :=
  ["open ", "variable", "universe ", "set_option ", "include ", "omit ", "attribute [local", "local "]

/-- Effect of one draft chunk on the scope stack. -/
def stepScopes (stack : Array ScopeFrame) (chunk : String) : Array ScopeFrame :=
  let first := ((chunk.splitOn "\n").headD "").trimAscii.toString
  let words := (first.splitOn " ").filter (· != "")
  if first.startsWith "--" || first.startsWith "/-" then stack
  else if words.headD "" == "namespace" then
    stack.push { opener := first, closer := s!"end {words.getD 1 ""}" }
  else if words.contains "section" && (words.getLast? == some "section" ||
      (words.idxOf? "section").any (· + 2 == words.length)) &&
      !first.endsWith " in" then
    let name := if words.getLast? == some "section" then "" else words.getLast!
    stack.push { opener := first, closer := if name == "" then "end" else s!"end {name}" }
  else if words.headD "" == "end" then stack.pop
  else if scopeCmdPrefixes.any (fun (p : String) => first.startsWith p) && !first.endsWith " in" && !stack.isEmpty then
    stack.modify (stack.size - 1) fun f => { f with cmds := f.cmds.push chunk.trimAsciiEnd.toString }
  else stack

def scopeOf (stack : Array ScopeFrame) (draft : String) : Array ScopeFrame :=
  (chunks draft).foldl stepScopes stack

/-- Working file = projection with the author's drafts re-attached after their element.
Elements are always elaborated at the root: scopes the drafts left open are closed before
an element and reopened (with their scope commands) after it, in machine-generated blocks. -/
def renderWorking (projection : String) (drafts : Array (String × String)) : String := Id.run do
  let lines := projection.splitOn "\n"
  -- header (imports, projection comment) and element blocks
  let mut header := ""
  let mut elems : Array (String × String) := #[]
  let mut cur : Option (String × String) := none
  for l in lines do
    match cur with
    | some (pid, txt) =>
      let txt := txt ++ l ++ "\n"
      if l.startsWith "-- paralean:end " then
        elems := elems.push (pid, txt); cur := none
      else cur := some (pid, txt)
    | none =>
      if l.startsWith "-- paralean:published " then
        cur := some ((l.drop "-- paralean:published ".length).toString.trimAscii.toString, l ++ "\n")
      else if elems.isEmpty then header := header ++ l ++ "\n"
  let mut pending : Std.HashMap String String :=
    drafts.foldl (fun m (k, v) => m.insert k ((m.getD k "") ++ v)) {}
  let mut out := header.trimAsciiEnd.toString ++ "\n"
  let mut stack : Array ScopeFrame := #[]
  if let some d := pending[""]? then
    out := out ++ "\n" ++ d
    stack := scopeOf stack d
    pending := pending.erase ""
  for (pid, txt) in elems do
    if !stack.isEmpty then
      out := out ++ "\n-- paralean:auto-begin (close draft scopes around a published element)\n"
      for f in stack.reverse do out := out ++ f.closer ++ "\n"
      out := out ++ "-- paralean:auto-end\n"
    out := out ++ "\n" ++ txt
    if !stack.isEmpty then
      out := out ++ "-- paralean:auto-begin (reopen draft scopes)\n"
      for f in stack do
        out := out ++ f.opener ++ "\n"
        for c in f.cmds do out := out ++ c ++ "\n"
      out := out ++ "-- paralean:auto-end\n"
    if let some d := pending[pid]? then
      out := out ++ "\n" ++ d
      stack := scopeOf stack d
      pending := pending.erase pid
  -- drafts whose element is unknown here stay at the end
  for (_, v) in pending.toList do out := out ++ "\n" ++ v
  return (out.dropEndWhile (· == '\n')).toString ++ "\n"

end Paralean
