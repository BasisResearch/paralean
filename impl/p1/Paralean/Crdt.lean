module

public import Lean
public import Paralean.Store
public import Paralean.Render
public import Paralean.Sha256
public import Paralean.Encode

@[expose] public section

/-!
Working-file helpers for transparent workspaces: rename maps applied to names and capsule
text, and the split of a working file into published elements and the author's drafts.
The RGA, naming and canonical projection are in `Paralean.Rga`.

A working file is the copy's projection in working form (each element between
`-- paralean:published <group>` and `-- paralean:end` lines) with the author's drafts
re-attached after the element they followed. Drafts are never part of the projection.
-/

namespace Paralean
open Lean System

/-! ## Renames

The rename maps themselves come from `Rga.View` (lineage naming, §11.5). A renamed
package's auxiliaries follow (prefix rename), and published uses of it (groups that depend
on the renamed package) are rewritten in their rendered and loaded text (OPEN-17).
Declaration identity is unaffected: dependencies pin packages.
-/

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

/-- Source spelling of a name: components that are not identifiers (the reserved fresh
names, which contain `✝`) are written `«…»`. Lean's `Name.toString` leaves `✝` unescaped. -/
def nameSrc (n : Name) : String :=
  ".".intercalate (n.components.map fun c => match c with
    | .str _ s => if (s.splitOn "✝").length > 1 then s!"«{s}»" else c.toString
    | _ => c.toString)

def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' || c == '.' ||
  Lean.isLetterLike c || Lean.isSubScriptAlnum c

/-- Rewrite identifier tokens that denote a renamed name (written fully qualified or
relative to the namespace `ns`). -/
def renameText (ns : Name) (m : Std.HashMap Name Name) (txt : String) : String := Id.run do
  if m.isEmpty then return txt
  let mut forms : Array (String × String) := #[]
  for (a, b) in m.toList do
    forms := forms.push (a.toString, nameSrc b)
    if ns.isPrefixOf a && ns != a then
      forms := forms.push ((a.replacePrefix ns .anonymous).toString, nameSrc (b.replacePrefix ns .anonymous))
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
