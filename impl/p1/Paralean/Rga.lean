module

public import Lean
public import Paralean.Model
public import Paralean.P3
public import Paralean.Crdt

@[expose] public section

/-!
Per-file declaration RGA, lineage naming and canonical rendering (p0-interfaces §11.3–11.5),
following `verification/tla/Workspace.tla` and `verification/veil/WORKSPACES.md`.

The input is what a copy knows: publication records (markers), tombstones and the
revisions they name (`P3.Known`), plus each package's metadata. Rendering and naming read
only fields the records carry (`rootPath`, `lineageKeys`, own keys, revision parents),
never anchors or ancestors that are not known, so the result is a function of the known
set (`render_carried`, `view_carried`).

* **Liveness.** A known group is live unless a known tombstone by its author deletes it or
  a known group revises it (for any name, transitively through known revisions).
* **Order.** Live groups sort by their lineage root's carried anchor path (`PathBefore`: a
  proper prefix first, otherwise the newer key at the first difference first), then by own
  key, oldest first. A revision carries its root's path, so it takes its root's place.
* **Names.** For a public name `x`, the candidates are the live groups declaring it. The
  least (lineage key for `x`, own key) keeps `x`; every other candidate is renamed to the
  reserved fresh name `fresh x g` (OPEN-25 spelling: the last component gets the suffix
  `✝pl<first 8 hex of the group ID>`). Validators reject groups declaring a name with a
  `✝` component, so a fresh name never clashes with a declared one. Renaming is
  hierarchical (derived names follow their prefix).
-/

namespace Paralean.Rga
open Lean P3

/-- Reserved-namespace marker (OPEN-25). -/
def reservedMark : String := "✝pl"

def isReserved (n : Name) : Bool :=
  n.components.any fun c => match c with
    | .str _ s => (s.splitOn "✝").length > 1
    | _ => false

def fresh (x : Name) (group : String) : Name :=
  match x with
  | .str p s => .str p s!"{s}{reservedMark}{(group.take 8).toString}"
  | n => .str n s!"{reservedMark}{(group.take 8).toString}"

/-- Revision ancestry. -/
structure Graph where
  /-- group ↦ groups it revises (transitively), for any name. -/
  anc : Std.HashMap String (Std.HashSet String) := {}
  /-- (group, name) ↦ groups it revises for that name (transitively). -/
  ancFor : Std.HashMap (String × Name) (Std.HashSet String) := {}

partial def revAncestors (k : Known) (rid : String) (acc : Std.HashSet String) (seen : Std.HashSet String) :
    Std.HashSet String × Std.HashSet String :=
  if seen.contains rid then (acc, seen) else
  let seen := seen.insert rid
  match k.revs[rid]? with
  | none => (acc, seen)
  | some r => r.parents.foldl (fun (acc, seen) p =>
      let acc := match k.revs[p]? with
        | some pr => acc.insert pr.group
        | none => acc
      revAncestors k p acc seen) (acc, seen)

def Graph.of (k : Known) : Graph := Id.run do
  let mut g : Graph := {}
  for m in k.markers do
    let mut all : Std.HashSet String := {}
    for rid in m.revisions do
      let (a, _) := revAncestors k rid {} {}
      all := a.fold (·.insert ·) all
      if let some r := k.revs[rid]? then
        g := { g with ancFor := g.ancFor.insert (m.group, r.name) a }
    g := { g with anc := g.anc.insert m.group (all.erase m.group) }
  return g

/-- The groups a copy can render, with their metadata. -/
structure View where
  known : Known
  graph : Graph
  metas : Std.HashMap String GroupRec
  live : Std.HashSet String
  /-- pid ↦ (published name ↦ rendered name). -/
  renames : Std.HashMap String (Std.HashMap Name Name)
  /-- (name, losing group, winning group) for every renamed candidate. -/
  losers : Array (Name × String × String)

def tombstoned (k : Known) (m : Marker) : Bool :=
  k.tombs.any fun t => t.target == m.group && t.author == m.author && t.file == m.file

def computeLive (k : Known) (g : Graph) : Std.HashSet String := Id.run do
  let mut superseded : Std.HashSet String := {}
  for m in k.markers do
    for a in g.anc.getD m.group {} do superseded := superseded.insert a
  let mut live := {}
  for m in k.markers do
    if !superseded.contains m.group && !tombstoned k m then live := live.insert m.group
  return live

def keyLe (a b : Nat × String) : Bool := !keyLt b a

/-- `PathBefore` of Workspace.tla on carried paths. -/
def pathBefore (p q : Array (String × Nat × String)) : Bool := Id.run do
  let n := min p.size q.size
  for i in [0:n] do
    let a := (p[i]!.2.1, p[i]!.2.2)
    let b := (q[i]!.2.1, q[i]!.2.2)
    if a != b then return keyLt b a
  return p.size < q.size

def posLt (a b : Marker) : Bool :=
  if a.rootPath.map (fun x => (x.2.1, x.2.2)) == b.rootPath.map (fun x => (x.2.1, x.2.2)) then keyLt a.key b.key
  else pathBefore a.rootPath b.rootPath

def declaredNames (g : GroupRec) : Array Name :=
  (g.members.filter (·.cls == "pub")).map (·.name)

def lineageKey (m : Marker) (x : Name) : Nat × String :=
  match m.lineageKeys.find? (·.1 == x) with
  | some (_, l, a) => (l, a)
  | none => m.key

def View.of (k : Known) (metas : Std.HashMap String GroupRec) : View := Id.run do
  let graph := Graph.of k
  let live := computeLive k graph
  -- candidates per public name
  let mut cands : Std.HashMap Name (Array Marker) := {}
  for m in k.markers do
    unless live.contains m.group do continue
    let some g := metas[m.pid]? | continue
    for x in declaredNames g do
      cands := cands.insert x ((cands.getD x #[]).push m)
  let mut renames : Std.HashMap String (Std.HashMap Name Name) := {}
  let mut losers := #[]
  for (x, ms) in cands.toList do
    if ms.size < 2 then continue
    let lt (a b : Marker) : Bool :=
      let ka := lineageKey a x
      let kb := lineageKey b x
      keyLt ka kb || (ka == kb && keyLt a.key b.key)
    let sorted := ms.qsort lt
    let w := sorted[0]!
    for m in sorted.extract 1 sorted.size do
      renames := renames.insert m.pid ((renames.getD m.pid {}).insert x (fresh x m.group))
      losers := losers.push (x, m.group, w.group)
  return { known := k, graph, metas, live, renames, losers := losers.qsort (fun a b => a.2.1 < b.2.1) }

/-- Live elements of `file`, in rendered order. -/
def View.elements (v : View) (file : String) : Array Marker :=
  (v.known.markers.filter fun m => m.file == file && v.live.contains m.group).qsort posLt

def View.files (v : View) : Array String :=
  (v.known.markers.foldl (fun acc m => if acc.contains m.file then acc else acc.push m.file) #[]).qsort (· < ·)

/-- Rendered public name ↦ group, over the live heads of every file except `exclude`. -/
def View.index (v : View) (exclude : Option String := none) : Std.HashMap Name String := Id.run do
  let mut idx := {}
  for m in v.known.markers do
    if !v.live.contains m.group || some m.file == exclude then continue
    let some g := v.metas[m.pid]? | continue
    let own := v.renames.getD m.pid {}
    for n in g.publicNames do idx := idx.insert (renameName own n) m.group
  return idx

/-! ## Canonical rendering (§11.3) -/

/-- Can the element be written as `<header> :=\n  remote% "<group>"`? -/
def headerForm (g : GroupRec) : Bool := Paralean.headerForm g

def stripEnd (s : String) : String :=
  "\n".intercalate ((s.splitOn "\n").map fun l => l.trimAsciiEnd.toString) |>.trimAsciiEnd.toString

def elementText (g : GroupRec) (group : String) : String :=
  match g.capsule.valueStart with
  | some v =>
    if headerForm g then
      stripEnd (String.fromUTF8! (g.capsule.text.toUTF8.extract 0 v)) ++ s!" :=\n  remote% \"{group}\""
    else s!"remote_decl% \"{group}\""
  | none => s!"remote_decl% \"{group}\""

/-- Scope lines opened before and closed after an element in header form. -/
def scopeLines (c : Capsule) : Array String × Array String := Id.run do
  let mut opens := #[]
  let mut closes := #[]
  let needSection := c.sectionHeader != "" || c.noncomputable_ || !c.opens.isEmpty || !c.scopeCmds.isEmpty
  if needSection then
    opens := opens.push (if c.sectionHeader != "" then c.sectionHeader
      else if c.noncomputable_ then "noncomputable section" else "section")
    closes := closes.push "end"
  for o in c.opens do opens := opens.push o
  unless c.currNamespace.isAnonymous do
    opens := opens.push s!"namespace {c.currNamespace}"
    closes := closes.push s!"end {c.currNamespace}"
  for s in c.scopeCmds do opens := opens.push (stripEnd s)
  return (opens, closes.reverse)

def scopeKey (g : GroupRec) : String :=
  if headerForm g then
    let (o, _) := scopeLines g.capsule
    "\n".intercalate o.toList
  else "\x00standalone"

def View.group (v : View) (m : Marker) : Option GroupRec :=
  (v.metas[m.pid]?).map (renamedGroup v.renames)

def View.header (v : View) (elems : Array Marker) (file : String) : String := Id.run do
  let gs := elems.filterMap v.group
  let isModule := !gs.isEmpty && gs.all (·.capsule.isModule)
  let self := moduleOfFile file
  let mut imps : Array String := #[]
  for g in gs do
    -- `Init` is implicit in a non-module file
    let ls := if isModule then g.capsule.importSpecs
      else g.capsule.imports.filter (fun m => m != self && m != `Init) |>.map (s!"import {·}")
    for l in ls do unless imps.contains l do imps := imps.push l
  imps := imps.qsort (· < ·)
  return (if isModule then "module\n" else "") ++ String.join (imps.toList.map (· ++ "\n"))
where
  moduleOfFile (f : String) : Name :=
    let f := if f.endsWith ".lean" then (f.dropEnd 5).toString else f
    (f.splitOn "/").foldl Name.mkStr .anonymous

/-- The published projection of `file`: canonical bytes (§11.3), a pure function of the
known records and the packages they name. -/
def View.projection (v : View) (file : String) : String := Id.run do
  let elems := v.elements file
  if elems.isEmpty then return ""
  let mut blocks : Array String := #[]
  let mut i := 0
  while i < elems.size do
    let some g := v.group elems[i]! | i := i + 1; continue
    let key := scopeKey g
    let mut run := #[elementText g elems[i]!.group]
    let mut j := i + 1
    while j < elems.size do
      match v.group elems[j]! with
      | some h => if scopeKey h == key && headerForm g then run := run.push (elementText h elems[j]!.group); j := j + 1
                  else break
      | none => j := j + 1
    if headerForm g then
      let (o, c) := scopeLines g.capsule
      let pre := if o.isEmpty then "" else "\n".intercalate o.toList ++ "\n\n"
      let post := if c.isEmpty then "" else "\n\n" ++ "\n".intercalate c.toList
      blocks := blocks.push (pre ++ "\n\n".intercalate run.toList ++ post)
    else blocks := blocks.push ("\n\n".intercalate run.toList)
    i := j
  let hdr := v.header elems file
  let body := "\n\n".intercalate blocks.toList
  return (if hdr.isEmpty then "" else hdr ++ "\n") ++ body ++ "\n"

/-- The projection in working-copy form: each element wrapped in its own scope between
`-- paralean:published <group>` / `-- paralean:end` lines, so drafts can sit between
elements (`Crdt.renderWorking`). -/
def View.workingProjection (v : View) (file : String) : String := Id.run do
  let elems := v.elements file
  let mut out := v.header elems file ++ s!"-- paralean: published projection of {file}\n"
  for m in elems do
    let some g := v.group m | continue
    let body := if headerForm g then
        let (o, c) := scopeLines g.capsule
        "\n".intercalate (o.toList ++ [elementText g m.group] ++ c.toList)
      else elementText g m.group
    out := out ++ "\n" ++ s!"{elementBegin m.group}\n{body}\n{elementEnd m.group}\n"
  return out

/-! ## Staging: placement fields of a new record -/

/-- `rootPath` and `lineageKeys` of a new record (§11.1), computed by its author from the
groups it knows or has staged (`staged`: this batch, in order). `anchorOf` is the nearest
element above, or none (file start). `revises` are the groups it revises, per name. -/
structure Staged where
  group : String
  file : String
  anchor : Option String
  lamport : Nat
  author : String
  rootPath : Array (String × Nat × String)
  lineageKeys : Array (Name × Nat × String)

def lineageRootPath (m : Marker) : Array (String × Nat × String) := m.rootPath

end Paralean.Rga
