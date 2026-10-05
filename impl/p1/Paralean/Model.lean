module

public import Lean
public import Paralean.Encode

@[expose] public section

/-! Metadata records stored next to the binary group encodings. -/

namespace Paralean
open Lean

/-- Names (including hygienic ones, which Lean's `Name` JSON cannot round-trip) are
stored as component arrays. -/
instance (priority := high) nameToJsonComponents : ToJson Name where
  toJson n := Json.arr (n.components.toArray.map fun c => match c with
    | .str _ s => Json.str s
    | .num _ k => Json.num k
    | .anonymous => Json.null)

instance (priority := high) nameFromJsonComponents : FromJson Name where
  fromJson? j := do
    let arr ← j.getArr?
    arr.foldlM (init := Name.anonymous) fun n c => match c with
      | .str s => pure (Name.mkStr n s)
      | .num k => match k.mantissa.toNat? with
        | some v => if k.exponent == 0 then pure (Name.mkNum n v) else throw "bad name component"
        | none => throw "bad name component"
      | _ => throw "bad name component"

/-- Diagnostic classes. `reject` = policy rejection; `unsupported` = frontend effect we do
not reproduce; `capsule` = a case that needs a larger source capsule; `info` = note. -/
structure Diag where
  severity : String
  code : String
  msg : String
  file : String := ""
  line : Nat := 0
  deriving ToJson, FromJson, Inhabited, Repr

instance : ToString Diag := ⟨fun d =>
  s!"[{d.severity}:{d.code}] {d.file}:{d.line}: {d.msg}"⟩

structure MemberRec where
  /-- Lean name in the capture environment. -/
  name : Name
  /-- Normalized identity inside the group (module- and relocation-independent). -/
  local_ : Name
  cls : String
  kind : String
  /-- Hash of this member's encoding alone (diagnostics only). -/
  hash : String := ""
  /-- Hash of the statement alone (type + level params), with exact dependency pins.
      Target contracts compare this. -/
  typeHash : String := ""
  deriving ToJson, FromJson, Inhabited, Repr

/-- Source capsule: everything needed to re-elaborate the command. -/
structure Capsule where
  workspace : String
  file : String
  /-- Module name the file was elaborated as. -/
  module : Name
  startLine : Nat
  endLine : Nat
  /-- Header imports of the file (all from the pinned base). -/
  imports : Array Name
  /-- `noncomputable section`. -/
  noncomputable_ : Bool
  /-- Section header of the enclosing scope, e.g. `@[expose] public section` (module system). -/
  sectionHeader : String := ""
  /-- The file is a `module` (module system). -/
  isModule : Bool := false
  /-- Header import lines as written (`public import X`, `import all Y`, ...). -/
  importSpecs : Array String := #[]
  currNamespace : Name
  /-- `open` commands rendered at the root, in original order. -/
  opens : Array String
  /-- `universe`, `variable`, `include`, `omit`, `set_option` rendered inside the namespace. -/
  scopeCmds : Array String
  /-- Text of section-local effect commands still in scope (conservative capsule part). -/
  localEffects : Array String
  /-- The command text. For relocated groups the `private` keyword is blanked and an
      anonymous instance receives its generated name explicitly. -/
  text : String
  /-- Relocate into `currNamespace._pl_<gid8>` on render. -/
  relocate : Bool
  /-- Byte offset in `text` where the declaration value (`:= …`, equations, `where …`)
      starts; `none` for commands without a single value (structures, mutual blocks, …).
      `text.take valueStart` is the published header (name, binders, statement). -/
  valueStart : Option Nat := none
  deriving ToJson, FromJson, Inhabited, Repr

structure GroupRec where
  /-- Package ID: declaration content + capsule + frontend dependencies. Dependencies pin these. -/
  gid : String
  /-- Declaration ID: SHA-256 of the canonical kernel encoding (the stored object). -/
  declId : String
  /-- `decl` (has kernel members) or `effect` (frontend-only command). -/
  kind : String
  cmdKind : Name
  members : Array MemberRec
  /-- Reserved names the command realized; never members, re-realized by consumers. -/
  realized : Array Name
  /-- Exact kernel dependencies (group IDs). -/
  deps : Array String
  /-- Frontend dependencies found precisely (info trees, attribute targets). -/
  feDeps : Array String
  /-- Conservative frontend dependencies: every earlier global effect group of the file. -/
  feDepsConservative : Array String
  publicNames : Array Name
  /-- Canonical anchor for groups with no public name (`<ns>._pl_<gid8>`). -/
  anchor : Option Name
  /-- Persistent extensions whose exported entries this command changed. -/
  touched : Array (Name × Nat)
  /-- Transitive axioms of the group (base + deps + own). -/
  axioms : Array Name
  capsule : Capsule
  diags : Array Diag
  /-- Bytes of the binary encoding. -/
  encSize : Nat
  deriving ToJson, FromJson, Inhabited, Repr

def GroupRec.short (g : GroupRec) : String := (g.gid.take 8).toString

def GroupRec.relocNs (g : GroupRec) : Name :=
  g.capsule.currNamespace ++ Name.mkSimple s!"_pl_{g.short}"

/-- A pinned target: the statement hash a published proof of `name` must have. -/
structure TargetContract where
  name : Name
  typeHash : String
  deriving ToJson, FromJson, Inhabited, Repr

/-- A captured workspace file. -/
structure FileRec where
  workspace : String
  file : String
  module : Name
  imports : Array Name
  /-- Groups of this file in command order (decl and effect). -/
  groups : Array String
  /-- Commands that produced no group (`#check`, `example`, scope commands, ...). -/
  skipped : Array (Name × Nat)
  diags : Array Diag
  /-- Groups visible through the transparent prelude when this file was captured. -/
  prelude : Array String
  /-- Groups captured but rejected by policy (stored for audit, never published). -/
  rejected : Array String := #[]
  /-- Imports of other workspace files, satisfied by the transparent prelude. -/
  wsImports : Array Name := #[]
  /-- Source-replay result of the prelude: groups whose declaration ID was reproduced. -/
  preludeOk : Nat := 0
  deriving ToJson, FromJson, Inhabited, Repr

/-- Name-classification helpers. -/
def plComponent? (s : String) : Option String :=
  if s.startsWith "_pl_" then some (s.drop 4).toString else none

/-- Mangled module spelling used in `_aux_<M>___` names. -/
def mangleModule (m : Name) : String :=
  "_".intercalate (m.components.map fun c => c.toString (escape := false))

def moduleToSuffix : Name → String
  | .anonymous => ""
  | .num n _ => moduleToSuffix n
  | .str n s => moduleToSuffix n ++ "_" ++ s.decapitalize

/-- Suffix that `mkBaseNameWithSuffix` appends for the project of `mainModule`. -/
def projectSuffix (mainModule : Name) : String := moduleToSuffix mainModule.getRoot

/--
Normalize a Lean name to its module-independent identity:
drop the `_private.<M>.0` prefix, `_pl_<gid>` relocation components and macro-scope tails,
and replace the module spelling inside `_aux_<M>___` names.
-/
partial def normName (mainModule : Name) (n : Name) : Name :=
  let n := privateToUserName n
  let mm := mangleModule mainModule
  let comps := n.components
  -- macro scopes: keep the user part, drop module/hash/scope numbers
  let comps := match comps.findIdx? (· == Name.mkSimple "_@") with
    | some i => comps.take i ++ [`_hyg]
    | none => comps
  let comps := comps.filter fun c => match c with
    | .str .anonymous s => (plComponent? s).isNone
    | _ => true
  let comps := comps.map fun c => match c with
    | .str .anonymous s =>
      if s.startsWith "_aux_" then
        Name.mkSimple (s.replace s!"_aux_{mm}___" "_aux_$M___")
      else c
    | _ => c
  comps.foldl (fun acc c => match c with
    | .str _ s => .str acc s
    | .num _ k => .num acc k
    | .anonymous => acc) .anonymous

end Paralean
