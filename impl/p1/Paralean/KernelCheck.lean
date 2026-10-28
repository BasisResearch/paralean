import Lean
import Paralean.Validate
import Paralean.Capture

/-!
# Split validator (W2-13): the verdict comes from a process that runs no package code

`check-group` source-replays a closure's capsules (gated, but elaborated by base
elaborators on capsule input) and kernel-replays their stored terms in one process, and the
validator signs what that process prints. A defect reachable from capsule input in that
process could therefore print any verdict.

The validator now runs two processes on the same verified input store:

* `source-check` (sandboxed, single-use) is the old `check-group` pipeline. It contributes
  only *evidence*: whether each group's capsule re-elaborates to its declaration ID, and the
  reserved constants (equation lemmas and the like) it re-realized, encoded with the payload
  encoding. Nothing else it says is used.
* `kernel-check` (a fresh sandbox) elaborates no capsule. It opens the pinned imports,
  decodes every group's content-addressed stored terms under names it chooses itself, adds
  them and the evidence's reserved constants with the stock kernel, audits axioms from its
  own kernel environment, and re-derives each target's statement hash from the stored bytes.
  Its `CHECK` line is the verdict: kernel validity, axioms and targets are its own findings;
  the evidence can only reject (a group the frontend reports as not reproducing its ID).

The decoder and the kernel treat every evidence byte as untrusted input.
-/

namespace Paralean
open Lean

/-! ## JSON forms of names and references (component-wise, so they round-trip exactly) -/

def nameToJsonV (n : Name) : Json :=
  Json.arr <| n.components.toArray.map fun c => match c with
    | .str _ s => Json.mkObj [("s", s)]
    | .num _ k => Json.mkObj [("n", k)]
    | .anonymous => Json.null

def nameOfJsonV (j : Json) : Except String Name := do
  let parts ← j.getArr?
  if parts.size > 256 then throw "name has too many components"
  parts.foldlM (init := Name.anonymous) fun n p => do
    match p.getObjValAs? String "s" with
    | .ok s => pure (Name.mkStr n s)
    | .error _ => pure (Name.mkNum n (← p.getObjValAs? Nat "n"))

partial def refToJsonV : Ref → Json
  | .base n => Json.mkObj [("base", nameToJsonV n)]
  | .self l => Json.mkObj [("self", nameToJsonV l)]
  | .dep g l => Json.mkObj [("dep", g), ("local", nameToJsonV l)]
  | .res r s => Json.mkObj [("res", refToJsonV r), ("suffix", nameToJsonV s)]

def refOfJsonV : Nat → Json → Except String Ref
  | 0, _ => throw "reference nests too deeply"
  | fuel + 1, j => do
    if let .ok b := j.getObjVal? "base" then return .base (← nameOfJsonV b)
    if let .ok l := j.getObjVal? "self" then return .self (← nameOfJsonV l)
    if let .ok g := j.getObjValAs? String "dep" then return .dep g (← nameOfJsonV (← j.getObjVal? "local"))
    let r ← refOfJsonV fuel (← j.getObjVal? "res")
    return .res r (← nameOfJsonV (← j.getObjVal? "suffix"))

def hexOfBytes (b : ByteArray) : String :=
  b.foldl (init := "") fun s x =>
    let d (v : UInt8) : Char := if v < 10 then Char.ofNat (48 + v.toNat) else Char.ofNat (87 + v.toNat)
    s.push (d (x >>> 4)) |>.push (d (x &&& 15))

def bytesOfHex (s : String) : Except String ByteArray := do
  if s.length % 2 != 0 then throw "odd hex length"
  let digit (c : Char) : Except String UInt8 :=
    if '0' ≤ c && c ≤ '9' then pure (c.toNat - '0'.toNat).toUInt8
    else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10).toUInt8
    else throw "bad hex digit"
  let cs := s.toList.toArray
  let mut out := ByteArray.emptyWithCapacity (cs.size / 2)
  for i in [0:cs.size / 2] do
    out := out.push ((← digit cs[2*i]!) * 16 + (← digit cs[2*i+1]!))
  return out

/-! ## Evidence: what the frontend hands the kernel checker -/

/-- One re-realized reserved constant: its reference and a one-member pseudo-group
(member local `r`, everything else as references) in the payload encoding. -/
structure RealizedConst where
  ref : Ref
  bytes : ByteArray

structure GroupEvidence where
  gid : String
  sourceOk : Bool
  diags : Array String := #[]
  realized : Array RealizedConst := #[]

/-- Evidence for a check: per group, and the frontend's own diagnostics (which can only
explain a rejection). -/
structure Evidence where
  groups : Array GroupEvidence := #[]
  diags : Array String := #[]

def evidenceToJson (ev : Evidence) : Json :=
  Json.mkObj [("diags", toJson ev.diags), ("groups", Json.arr <| ev.groups.map fun g => Json.mkObj [
    ("gid", g.gid), ("sourceOk", g.sourceOk), ("diags", toJson g.diags),
    ("realized", Json.arr <| g.realized.map fun r =>
      Json.mkObj [("ref", refToJsonV r.ref), ("bytes", hexOfBytes r.bytes)])])]

def evidenceOfJson (j : Json) : Except String Evidence := do
  let gs ← (← j.getObjVal? "groups").getArr?
  let diags := (j.getObjValAs? (Array String) "diags").toOption.getD #[]
  let groups ← gs.mapM fun g => do
    let realized ← (← g.getObjVal? "realized").getArr?
    return {
      gid := ← g.getObjValAs? String "gid", sourceOk := ← g.getObjValAs? Bool "sourceOk"
      diags := ← g.getObjValAs? (Array String) "diags"
      realized := ← realized.mapM fun r => do
        return { ref := ← refOfJsonV 32 (← r.getObjVal? "ref"), bytes := ← bytesOfHex (← r.getObjValAs? String "bytes") } }
  return { groups, diags }

/-- Local identity of a realized constant inside its pseudo-group. -/
def realizedLocal : Name := `r

/-! ## Frontend: `source-check` -/

/-- `e` without metadata nodes. The kernel looks through `mdata`, and realized equation
lemmas can carry syntax-valued metadata, which the payload encoding cannot carry. -/
partial def stripMData (e : Expr) : Expr :=
  e.replace fun
    | .mdata _ b => some (stripMData b)
    | _ => none

def ConstantInfo.stripMData : ConstantInfo → ConstantInfo
  | .defnInfo v => .defnInfo { v with type := Paralean.stripMData v.type, value := Paralean.stripMData v.value }
  | .thmInfo v => .thmInfo { v with type := Paralean.stripMData v.type, value := Paralean.stripMData v.value }
  | .opaqueInfo v => .opaqueInfo { v with type := Paralean.stripMData v.type, value := Paralean.stripMData v.value }
  | .axiomInfo v => .axiomInfo { v with type := Paralean.stripMData v.type }
  | ci => ci

/-- Encode the reserved constants a frontend realized for a group. Every constant they name
is a reference: a capsule member of the closure (`dep`), a base constant, or another
reserved name (`res`). -/
def encodeRealized (sr : SourceReplay) (cat : Catalog) (ci : ConstantInfo) :
    Except String RealizedConst := do
  let env := sr.sess.cmdState.env
  let inv : Std.HashMap Name (String × Name) := sr.names.fold (init := {}) fun m key n => m.insert n key
  let rec resolveA (fuel : Nat) (n : Name) : Except String Ref := do
    match fuel with
    | 0 => throw s!"reference {n} nests too deeply"
    | fuel + 1 =>
      if let some (pid, l) := inv[n]? then return .dep pid l
      if sr.baseEnv.contains n then return .base n
      match reservedBase env n with
      | some (b, s) => return .res (← resolveA fuel b) s
      | none => throw s!"realized constant refers to {n}, which is neither a capsule member, base nor reserved"
  let ref ← resolveA 64 ci.name
  unless ref matches .res .. do throw s!"{ci.name} is not a reserved name"
  let m : EncMember := { local_ := realizedLocal, cls := .scoped, info := ConstantInfo.stripMData ci }
  let resolve (n : Name) : Except String Ref :=
    if n == ci.name then pure (.self realizedLocal) else resolveA 64 n
  let bytes ← encodeGroup "realized" #[m] resolve (WireCtx.ofMembers #[m] cat.wireDep)
  return { ref, bytes }

/-- The old `check-group` pipeline, plus the evidence `kernel-check` needs. -/
unsafe def sourceCheck (store : Store) (gids : Array String) (declId : String)
    (targets : Array TargetContract := #[]) : IO (CheckResult × Evidence) := do
  let (r, replay?) ← checkGroupFull store gids declId targets
  let some rp := replay? | return (r, { diags := r.diags })
  let ev := rp.closure.map fun gid =>
    let res := rp.source.results.find? (·.gid == gid)
    let realized := ((rp.kernel.find? (·.gid == gid)).map (·.extra)).getD #[]
    { gid, sourceOk := (res.map (·.ok)).getD false
      diags := (res.map (·.diags.map toString)).getD #["not replayed"]
      realized := realized.filterMap fun ci => (encodeRealized rp.source rp.cat ci).toOption : GroupEvidence }
  return (r, { groups := ev, diags := if r.ok then #[] else r.diags })

/-! ## Trusted: `kernel-check` -/

/-- The name `kernel-check` gives member `l` of the group with catalogue key `pid`. -/
def kernelName (pid : String) (l : Name) : Name :=
  (Name.mkStr `_paralean_kernel pid).append l

/-- The name of a reference in the kernel checker's environment (`self` within `gid`). -/
def kernelRefName (gid : String) : Ref → Name
  | .base n => n
  | .self l => kernelName gid l
  | .dep pid l => kernelName pid l
  | .res r s => (kernelRefName gid r).append s

/-- Inverse wire context for a realized pseudo-group: its one member, and any closure
member by (group ID, index) through the catalogue. -/
def realizedUnwire (cat : Catalog) : UnwireCtx where
  selfLocal i := if i == 0 then some realizedLocal else none
  dep id i := cat.order.findSome? fun pid => do
    let g := cat.get! pid
    if g.declId == id then pure (pid, ← g.members[i]?.map (·.local_)) else none

/-- Statement hashes of the root group's members, re-derived from its stored bytes exactly
as capture computed them: each member re-encoded as an axiom under its own references. -/
def storedStatements (cat : Catalog) (bytes : ByteArray) (g : GroupRec) (gid : String) :
    Except String (Array (Name × String)) := do
  let dg ← decodeGroup bytes (cat.unwire g) (fun r => pure (kernelRefName gid r))
  let mut inv : Std.HashMap Name Ref := {}
  for r in dg.refs do
    let n := kernelRefName gid r
    if let some r' := inv[n]? then
      unless r' == r do throw s!"two references share the name {n}"
    inv := inv.insert n r
  let members : Array EncMember := dg.members.map fun (l, cls, ci) => { local_ := l, cls, info := ci }
  for m in members do inv := inv.insert m.info.name (.self m.local_)
  let wire := WireCtx.ofMembers members cat.wireDep
  let resolve (n : Name) : Except String Ref := match inv[n]? with
    | some r => pure r
    | none => throw s!"statement refers to {n}, which is not a reference of the group"
  members.mapM fun m => do
    let stmt : EncMember := { m with info := .axiomInfo {
      name := m.info.name, levelParams := m.info.levelParams, type := m.info.type, isUnsafe := false } }
    return (m.local_, groupIdOf (← encodeGroup dg.baseId #[stmt] resolve wire))

unsafe def kernelCheck (store : Store) (gids : Array String) (declId : String)
    (targets : Array TargetContract) (ev : Evidence) : IO CheckResult := do
  let evidence := ev.groups
  let fail (msg : String) : CheckResult := { declId, ok := false, diags := #[msg] ++ ev.diags }
  let file : FileRec := { (default : FileRec) with workspace := "validator", file := "<job>", groups := gids }
  let cat ← try Catalog.load store #[file] catch e => return fail s!"load: {e}"
  let some root := cat.order.find? (fun g => (cat.get! g).declId == declId)
    | return fail "no group of the job has this declaration ID"
  let clo ← match cat.closure #[root] with
    | .ok c => pure c
    | .error e => return fail e
  for gid in clo do
    let c := (cat.get! gid).capsule
    if let .error e := Safety.checkCapsuleShape c.file c.module then
      return fail s!"capsule of {((cat.get! gid).declId.take 12).toString}: {e}"
    if hasInitEffect (cat.get! gid) then
      return fail s!"group {((cat.get! gid).declId.take 12).toString} has initializer effects, which a published capsule may not have"
  -- Base environment: the pinned imports only; no capsule is elaborated in this process.
  let imports := clo.foldl (fun acc g => (cat.get! g).capsule.imports.foldl
    (fun acc m => if acc.contains m then acc else acc.push m) acc) #[]
  let isModule := clo.any fun g => (cat.get! g).capsule.isModule
  let specs := clo.foldl (fun acc g => (cat.get! g).capsule.importSpecs.foldl
    (fun acc sp => if acc.contains sp then acc else acc.push sp) acc) #[]
  let hdr := if isModule then "module\n" ++ String.join (specs.toList.map (· ++ "\n")) else headerFor imports
  let (sess, _, _, _, hdrDiags, _) ← try openSession hdr "<kernel-check>" `ParaleanKernelCheck
    catch e => return fail s!"base imports: {e}"
  unless hdrDiags.isEmpty do return fail s!"base imports: {hdrDiags.map toString}"
  let baseEnv := sess.cmdState.env
  let mut kenv := baseEnv.toKernelEnv
  let maxHB : USize := (Core.getMaxHeartbeats {}).toUSize
  let maxRec : USize := (maxRecDepth.get {}).toUSize
  let mut axCache : Std.HashMap Name (Array Name) := {}
  let mut rejected : Std.HashSet String := {}
  let mut diags : Array String := #[]
  let mut rootAxioms : Array Name := #[]
  for gid in clo do
    let g := cat.get! gid
    let short := (g.declId.take 12).toString
    let mut why : Array String := #[]
    -- The frontend can only make things worse: a group it says does not reproduce.
    match evidence.find? (·.gid == gid) with
    | some ev => unless ev.sourceOk do why := why.push s!"source replay of {short} failed: {ev.diags}"
    | none => why := why.push s!"no source-replay evidence for {short}" |>.append ev.diags
    for d in g.deps ++ g.feDeps do
      if rejected.contains d then why := why.push s!"{short} depends on rejected {(d.take 12).toString}"
    let bytes ← try store.getObject g.declId catch e => return fail s!"object {short}: {e}"
    match decodeGroup bytes (cat.unwire g) (fun r => pure (kernelRefName gid r)) with
    | .error e => why := why.push s!"decode {short}: {e}"
    | .ok dg =>
      let memberNames : NameSet := dg.members.foldl (fun s (_, _, ci) => s.insert ci.name) {}
      -- Reserved constants from the evidence, each decoded under the name of its reference
      -- in this group and checked by the kernel like any other declaration.
      let mut extra : Array ConstantInfo := #[]
      for rc in ((evidence.find? (·.gid == gid)).map (·.realized)).getD #[] do
        unless rc.ref matches .res .. do why := why.push s!"evidence for {short} names a non-reserved constant"; continue
        let name := kernelRefName gid rc.ref
        if (kenv.find? name).isSome || memberNames.contains name || extra.any (·.name == name) then continue
        match decodeGroup rc.bytes (realizedUnwire cat) (fun r =>
            if r == .self realizedLocal then pure name else pure (kernelRefName gid r)) with
        | .ok { members := #[(_, _, ci)], .. } => extra := extra.push ci
        | .ok _ => why := why.push s!"realized constant {name} is not one declaration"
        | .error e => why := why.push s!"realized constant {name}: {e}"
      match declsOf (dg.members ++ extra.map fun ci => (ci.name, NameClass.scoped, ci)) with
      | .error e => why := why.push s!"decls of {short}: {e}"
      | .ok ds =>
        for d in ds do
          match Kernel.Environment.addDeclCore kenv maxHB maxRec d none with
          | .ok k => kenv := k
          | .error e => why := why.push s!"kernel replay of {short} failed: {d.getNames}: {← kernelExMsg e}"
        for (_, _, ci) in dg.members do
          if let .recInfo _ := ci then
            match kenv.find? ci.name with
            | some ci' =>
              unless ci'.type == ci.type && ci'.levelParams == ci.levelParams do
                why := why.push s!"regenerated recursor {ci.name} differs"
            | none => why := why.push s!"recursor {ci.name} not generated"
        -- Axiom audit from this process's own kernel environment.
        let mut groupAxs : Array Name := #[]
        for (_, _, ci) in dg.members do
          let (axs, cache') ← kernelAxioms baseEnv kenv axCache ci.name
          axCache := cache'
          for a in axs do
            unless groupAxs.contains a do groupAxs := groupAxs.push a
            unless allowedAxioms.contains a do why := why.push s!"{ci.name} depends on disallowed axiom {a}"
          if let .axiomInfo _ := ci then why := why.push s!"{ci.name} is an axiom"
        if gid == root then rootAxioms := groupAxs
    unless why.isEmpty do
      rejected := rejected.insert gid
      diags := diags ++ why
  -- §11.5: no group declares a name in the reserved fresh namespace (from the catalogue).
  for m in (cat.get! root).members do
    if m.cls != "scoped" && Rga.isReserved m.name then
      diags := diags.push s!"the group declares {m.name}, a name in the reserved fresh namespace"
  -- Targets: statement hashes re-derived from the stored bytes, never from the frontend.
  let rootBytes ← try store.getObject (cat.get! root).declId catch e => return fail s!"object: {e}"
  let statements ← match storedStatements cat rootBytes (cat.get! root) root with
    | .ok s => pure s
    | .error e => diags := diags.push s!"statements: {e}"; pure #[]
  let declares (t : TargetContract) : Bool :=
    statements.any fun (l, h) => l == t.name && (t.typeHash.isEmpty || h == t.typeHash)
  let targetOk := if targets.isEmpty then none else some (targets.all declares)
  for t in targets do
    unless declares t do diags := diags.push s!"the group does not declare target {t.name} with the pinned statement"
  return { declId, gid := root, ok := diags.isEmpty, closure := clo.map (cat.get! · |>.declId)
           axioms := rootAxioms, publicNames := (cat.get! root).publicNames
           statements, targetOk, diags }

end Paralean
