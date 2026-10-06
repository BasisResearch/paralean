module

public import Lean
public meta import Lean
public meta import Paralean.Encode
public meta import Paralean.Model
public meta import Paralean.Store
public meta import Paralean.Render
public meta import Paralean.Crdt
public meta import Paralean.P3
public meta import Paralean.Rga

public meta section

/-!
`remote%`: published declarations inside a working copy (transparent workspaces, P3 v1).

A teammate's published declaration appears in every other copy of its file as

```
<published header> :=
  remote% "<group ID>"            -- theorem, def, instance, ...
remote_decl% "<group ID>"         -- structures, notation, mutual blocks, ... (OPEN-16)
```

Elaborating it (p0-interfaces §11.2):

1. **Name.** The group is published: its publication record is known, or is fetched from
   the store (`plr fetch-pkg`, which requires a valid certificate). The written
   declaration's name, resolved in the current scope, must be the (rendered) name of a
   member of that group.
2. **Statement.** The written binders and type, elaborated in the current scope, must be
   the published statement.
3. **Dependency versions.** The group's dependency closure is loaded by group ID from the
   store, independent of the file's imports. A local constant with the same name but other
   content is a version conflict, reported and never rebound.
4. **Receipt.** Every group of the closure has a receipt that a trusted validator signed
   (Ed25519), answering a job envelope the controller signed for exactly that group and
   capsule, with pinned policy and checker (`P3.checkReceipt`, P3 control's staging rule).
   The job also pins the capsules of the group's exact dependency closure.

Loading fetches the group's payload (`P3.payload`: from the cache, else `plr fetch-group`;
re-hashed) and decodes its kernel terms.

* A group whose declared value is a theorem is elaborated from its capsule's statement with
  the body `remote_value% "<package>"`: that term elaborator returns the **published
  proof term**, after adding the group's auxiliary members the proof uses (each
  kernel-checked by `addDecl`). The theorem itself is then kernel-checked with that proof.
  Attributes run as written, so `@[simp]` and generated declarations (`@[to_additive]`)
  come from the fetched proof.
* Other groups (definitions, instances, structures, inductives, notation) are elaborated
  from their capsule, since compilation, equation lemmas, structure info and instance
  search need the elaborator's side effects.

Afterwards every member in the environment is compared with the decoded payload: types
always, values of definitions always, and theorem proofs whenever they were fetched. Any
difference is an error. No placeholder axiom exists anywhere; `remote%` never accepts a
body it cannot fetch.

Configuration: `PARALEAN_STORE` (the copy's cache), `PARALEAN_TRUST`, `PARALEAN_PLR`.
`PARALEAN_REMOTE_LOG` receives one line per load for measurements.
-/

namespace Paralean.Remote
open Lean Elab Command Term Meta P3

syntax (name := remoteTerm) "remote% " str : term
syntax (name := remoteCmd) "remote_decl% " str : command
/-- Internal: the published proof of the package's theorem (fetched, never a placeholder). -/
syntax (name := remoteValue) "remote_value% " str : term

def storeRoot : IO System.FilePath := do
  let some r ← IO.getEnv "PARALEAN_STORE" | throw <| IO.userError "PARALEAN_STORE is not set"
  return r

def logEvent (s : String) : IO Unit := do
  if let some p ← IO.getEnv "PARALEAN_REMOTE_LOG" then
    let h ← IO.FS.Handle.mk p .append
    h.putStrLn s

/-- Depth of `remote%` loads in progress (the visibility predicate is suspended inside). -/
initialize loadingDepth : IO.Ref Nat ← IO.mkRef 0
/-- Packages loaded on demand by name resolution during the current command (for capture). -/
initialize loadLog : IO.Ref (Array String) ← IO.mkRef #[]
/-- pid ↦ (group, capsule): from known records and from loaded capsules' dependency lists. -/
initialize pkgIndex : IO.Ref (Std.HashMap String (String × String)) ← IO.mkRef {}
initialize metaCache : IO.Ref (Std.HashMap String GroupRec) ← IO.mkRef {}
/-- (module, package) ↦ member names verified in that module's environment. -/
initialize verifiedCache : IO.Ref (Std.HashMap (Name × String) (Array (Name × Name))) ← IO.mkRef {}
/-- The copy's view (records count, view), recomputed when records arrive. -/
initialize viewCache : IO.Ref (Nat × Option Rga.View) ← IO.mkRef (0, none)
/-- (module, package) ↦ the member names `remote_value%` gave the members it added. -/
initialize fetchedNames : IO.Ref (Std.HashMap (Name × String) (Std.HashMap Name Name)) ← IO.mkRef {}
/-- Constants `remote_value%` added from a payload (and the theorems it completed): their
proofs are the fetched ones. -/
initialize fetchedAdded : IO.Ref NameSet ← IO.mkRef {}
/-- Decoded payloads per package (immutable). -/
initialize payloadCache : IO.Ref (Std.HashMap String ByteArray) ← IO.mkRef {}

def countRecords (root : System.FilePath) : IO Nat := do
  let mut n := 0
  for sub in ["records", "fetched"] do
    let d := root / "p3" / sub
    if ← d.pathExists then n := n + (← d.readDir).size
  return n

/-- A known package's metadata from its stored capsule (hash-checked). -/
def metaOfCapsule (root : System.FilePath) (capsule : String) : IO GroupRec := do
  match ← loadCapsule root capsule with
  | .error e => throw <| IO.userError s!"remote%: {e}"
  | .ok g =>
    pkgIndex.modify (·.insert g.gid (g.declId, capsule))
    metaCache.modify (·.insert g.gid g)
    return g

def metaOfCapsuleOpt (root : System.FilePath) (capsule : String) : IO (Option GroupRec) := do
  if ← (root / "p3" / "capsules" / s!"{capsule}.json").pathExists then
    return some (← metaOfCapsule root capsule)
  return none

def view : IO Rga.View := do
  let root ← storeRoot
  let n ← countRecords root
  if let (k, some v) ← viewCache.get then
    if k == n then return v
  let known ← Known.load root
  let all ← Known.load root ["records", "fetched"]
  pkgIndex.modify fun m => all.markers.foldl (fun m mk => m.insert mk.pid (mk.group, mk.capsule)) m
  let mut metas : Std.HashMap String GroupRec := {}
  for mk in known.markers do
    metas := metas.insert mk.pid (← metaOfCapsule root mk.capsule)
  let v := Rga.View.of known metas
  viewCache.set (n, some v)
  return v

def renames : IO (Std.HashMap String (Std.HashMap Name Name)) := return (← view).renames

/-- The publication record of a group: known, or fetched from the store (certified). -/
def markerOf (group : String) : IO Marker := do
  let root ← storeRoot
  let find : IO (Option Marker) := do
    let k ← Known.load root ["records", "fetched"]
    return k.byGroup[group]?
  if let some m ← find then return m
  discard <| plr #["fetch-pkg", "--cache", root.toString, group]
  match ← find with
  | some m =>
    pkgIndex.modify (·.insert m.pid (m.group, m.capsule))
    return m
  | none => throw <| IO.userError s!"remote%: no published declaration with ID {group}"

def getMetaIO (pid : String) : IO GroupRec := do
  if let some g := (← metaCache.get)[pid]? then return g
  discard <| view
  let some (group, capsule) := (← pkgIndex.get)[pid]?
    | throw <| IO.userError s!"remote%: package {(pid.take 12).toString} is unknown to this copy"
  let root ← storeRoot
  unless ← (root / "p3" / "capsules" / s!"{capsule}.json").pathExists do
    discard <| markerOf group
  metaOfCapsule root capsule

def getMeta (pid : String) : CommandElabM GroupRec := getMetaIO pid

/-- The package a `remote%` literal (a group ID) denotes. -/
def pidOfGroup (group : String) : IO String := do
  let g := if group.startsWith "group:" then (group.drop 6).toString else group
  return (← markerOf g).pid

/-- Receipt of a package's group (§6), checked in this process. -/
def checkReceipt (g : GroupRec) : IO Unit := do
  let m ← markerOf g.declId
  unless m.pid == g.gid do
    throw <| IO.userError s!"remote%: the record of {g.short} names another package"
  let root ← storeRoot
  match ← P3.checkReceipt root m with
  | .ok job =>
    -- the job pins the capsules of the exact dependency closure: index their packages
    for c in job.deps do
      if (← metaOfCapsuleOpt root c).isNone then
        throw <| IO.userError s!"remote%: dependency capsule {(c.take 12).toString} of {g.short} is not in the cache"
  | .error e => throw <| IO.userError s!"remote%: receipt of {g.short} ({g.publicNames}): {e}"

/-- Lean names in the current environment of a group's members: match normalized local
identities (and the relocation tag) against this file's constants. -/
def memberNames (g : GroupRec) : CommandElabM (Std.HashMap Name Name) := do
  let env ← getEnv
  let mm := env.mainModule
  -- members `remote_value%` added itself: exactly the names it chose
  if let some m := (← fetchedNames.get)[(mm, g.gid)]? then
    let m := m.fold (fun acc l n => if env.contains n then acc.insert l n else acc) {}
    if !m.isEmpty then return m
  let own := (← renames).getD g.gid {}
  if !g.capsule.relocate then
    let mut fast : Std.HashMap Name Name := {}
    for m in g.members do
      let nm := renameName own m.name
      let cands := [nm, mkPrivateNameCore mm (privateToUserName nm)]
      if let some n := cands.find? env.contains then
        if normName mm n == renameName own m.local_ then fast := fast.insert m.local_ n
    if fast.size == g.members.size then return fast
  let tag := if g.capsule.relocate then some g.short else none
  let wanted : Std.HashMap Name Name := g.members.foldl (fun m mr => m.insert (renameName own mr.local_) mr.local_) {}
  let hygBases : Std.HashMap Name Nat := g.members.foldl (init := {}) fun m mr =>
    match mr.local_ with
    | .num p _ => if p.components.getLast? == some `_hyg then m.insert p (m.getD p 0 + 1) else m
    | _ => m
  let mut out : Std.HashMap Name Name := {}
  let mut hygSeen : Std.HashMap Name (Array Name) := {}
  for c in ← env.getLocalConstantInfos do
    let n := c.name
    let t := n.components.findSome? fun c => match c with
      | .str .anonymous s => plComponent? s
      | _ => none
    let l := normName mm n
    if t == tag then
      if let some orig := wanted[l]? then out := out.insert orig n
    if t == tag && hygBases.contains l then hygSeen := hygSeen.insert l ((hygSeen.getD l #[]).push n)
  for (b, k) in hygBases.toList do
    let ns := hygSeen.getD b #[]
    let recent := ns.extract (ns.size - k) ns.size
    for i in [0:recent.size] do out := out.insert (Name.mkNum b i) recent[i]!
  for m in g.members do
    let nm := renameName own m.name
    if !out.contains m.local_ && env.contains nm then out := out.insert m.local_ nm
  return out

/-- Dependency closure of `g` (dependencies first). -/
partial def closureOf (g : GroupRec) : CommandElabM (Array GroupRec) := do
  let rec go (gid : String) (seen : Std.HashSet String) (out : Array GroupRec) :
      CommandElabM (Std.HashSet String × Array GroupRec) := do
    if seen.contains gid then return (seen, out)
    let seen := seen.insert gid
    let r ← getMeta gid
    let mut st := (seen, out)
    for d in r.deps ++ r.feDeps do st ← go d st.1 st.2
    return (st.1, st.2.push r)
  return (← go g.gid {} #[]).2

/-- Elaborate Lean source (several commands) at the root scope of the current file. -/
def elabSourceAtRoot (src : String) (fileName : String) : CommandElabM Unit := do
  let saved ← get
  let root := saved.scopes.getLast!
  modify fun s => { s with scopes := [root] }
  let inputCtx := Parser.mkInputContext src fileName
  let mut pstate : Parser.ModuleParserState := {}
  try
    for _ in [0:100000] do
      let scope ← getScope
      let pmctx : Parser.ParserModuleContext :=
        { env := ← getEnv, options := scope.opts, currNamespace := scope.currNamespace,
          openDecls := scope.openDecls }
      let (cmd, ps, msgs) := Parser.parseCommand inputCtx pmctx pstate (← get).messages
      modify fun s => { s with messages := msgs }
      pstate := ps
      if Parser.isTerminalCommand cmd then break
      withReader (fun ctx => { ctx with fileName, fileMap := inputCtx.fileMap }) do
        elabCommand cmd
  finally
    modify fun s => { s with scopes := saved.scopes }

/-- Is the group's declared value a theorem (so its proof is taken from the payload)? -/
def proofFetched (g : GroupRec) : Bool :=
  let pubs := g.members.filter (·.cls == "pub")
  g.capsule.valueStart.isSome && !pubs.isEmpty && pubs.all (·.kind == "theorem")

/-- The capsule text to elaborate: a theorem's body is the fetched proof. -/
def capsuleSource (ren : Std.HashMap String (Std.HashMap Name Name)) (g : GroupRec) (fetch : Bool)
    (closure : Array GroupRec) : String :=
  let g := renamedGroup ren g
  let g := if fetch then
      match g.capsule.valueStart with
      | some v =>
        let hdr := String.fromUTF8! (g.capsule.text.toUTF8.extract 0 v)
        -- no implicit lambdas: the stored value is exactly the fetched proof, not an
        -- eta-expansion of it
        { g with capsule := { g.capsule with text := hdr.trimAsciiEnd.toString ++ s!" := no_implicit_lambda% (remote_value% \"{g.gid}\")" } }
      | none => g
    else g
  let ds := g.deps ++ g.feDeps
  renderCapsule g ((closure.filter fun d => d.capsule.relocate && ds.contains d.gid).map (·.relocNs))

/-! ## Decoding the fetched payload against the current environment -/

/-- Lean name of a dependency member in this module (verified earlier). -/
def depName (mm : Name) (pid : String) (l : Name) : IO (Option Name) := do
  match (← verifiedCache.get)[(mm, pid)]? with
  | some ps => return (ps.find? (·.1 == l)).map (·.2)
  | none => return none

def fetchPayload (g : GroupRec) : IO ByteArray := do
  if let some b := (← payloadCache.get)[g.gid]? then return b
  let t0 ← IO.monoMsNow
  let had ← (({ root := ← storeRoot } : Store).hasObject g.declId)
  let b ← P3.payload (← storeRoot) g.declId
  unless had do logEvent s!"fetch {g.declId} {b.size} {(← IO.monoMsNow) - t0}ms"
  payloadCache.modify (·.insert g.gid b)
  return b

/-- Decode `g`'s payload. `self` maps member identities to names in this environment; a
member without a name maps to `_paralean_missing.<identity>`. -/
def decodeHere (g : GroupRec) (closure : Array GroupRec) (self : Std.HashMap Name Name) :
    CoreM DecodedGroup := do
  let bytes ← fetchPayload g
  let mm := (← getEnv).mainModule
  let lookup : String → Option GroupRec := fun pid => closure.find? (·.gid == pid)
  -- dependency names, read before decoding (the decoder is pure)
  let mut deps : Std.HashMap (String × Name) Name := {}
  for d in closure do
    if d.gid == g.gid then continue
    for m in d.members do
      if let some n ← depName mm d.gid m.local_ then deps := deps.insert (d.gid, m.local_) n
  let deps' := deps
  let rec nameOf : Ref → Except String Name
    | .base n => .ok n
    | .self l => .ok (self.getD l (Name.appendCore `_paralean_missing l))
    | .dep pid l => match deps'[(pid, l)]? with
      | some n => .ok n
      | none => .error s!"dependency member {l} of {(pid.take 8).toString} is not loaded"
    | .res r s => do return Name.appendCore (← nameOf r) s
  match decodeGroup bytes (g.unwire lookup) nameOf with
  | .ok dg =>
    -- reserved names the terms use are re-realized here, never taken from the store
    for r in dg.refs do
      if let .res .. := r then
        if let .ok n := nameOf r then
          unless (← getEnv).contains n do
            try discard <| executeReservedNameAction n catch _ => pure ()
    return dg
  | .error e => throwError "remote%: payload of {g.short} does not decode here: {e}"

/-- Structural walk collecting the level assignment that makes `pub` equal `here`. -/
partial def matchLevels (pub here : Expr) (acc : Std.HashMap Name Level) : Std.HashMap Name Level :=
  let lv (a b : Level) (acc : Std.HashMap Name Level) : Std.HashMap Name Level :=
    match a with
    | .param p => if acc.contains p then acc else acc.insert p b
    | _ => acc
  match pub, here with
  | .sort a, .sort b => lv a b acc
  | .const _ ls, .const _ ls' => (ls.zip ls').foldl (fun acc (a, b) => lv a b acc) acc
  | .app f a, .app f' a' => matchLevels a a' (matchLevels f f' acc)
  | .lam _ t b _, .lam _ t' b' _ => matchLevels b b' (matchLevels t t' acc)
  | .forallE _ t b _, .forallE _ t' b' _ => matchLevels b b' (matchLevels t t' acc)
  | .letE _ t v b _, .letE _ t' v' b' _ => matchLevels b b' (matchLevels v v' (matchLevels t t' acc))
  | .mdata _ e, e' => matchLevels e e' acc
  | e, .mdata _ e' => matchLevels e e' acc
  | .proj _ _ e, .proj _ _ e' => matchLevels e e' acc
  | _, _ => acc

/-- Local variables a statement needs: those occurring in it, closed under occurrence in
their types; with `instImplicit`, also instance-implicit variables whose types mention
only needed ones (Lean's section-variable inclusion rule). In local-context order. -/
def neededVars (cands : Array Expr) (e : Expr) (instImplicit : Bool) (seed : Array Expr := #[]) :
    MetaM (Array Expr) := do
  let mut need : Std.HashSet FVarId := seed.foldl (·.insert ·.fvarId!) {}
  let mut changed := true
  let occurs (x : Expr) (t : Expr) : Bool := t.containsFVar x.fvarId!
  while changed do
    changed := false
    for x in cands do
      if need.contains x.fvarId! then continue
      let inE := occurs x e
      let mut inTy := false
      for y in cands do
        if need.contains y.fvarId! && occurs x (← instantiateMVars (← inferType y)) then inTy := true
      let isInst := instImplicit && (← x.fvarId!.getBinderInfo).isInstImplicit &&
        (← instantiateMVars (← inferType x)).hasAnyFVar (fun f => cands.any (·.fvarId! == f)) &&
        !(← instantiateMVars (← inferType x)).hasAnyFVar (fun f => cands.any (·.fvarId! == f) && !need.contains f)
      if inE || inTy || isInst then
        need := need.insert x.fvarId!
        changed := true
  return cands.filter fun x => need.contains x.fvarId!

/-- Constants of the group other than `main` that `e` uses, transitively, in an order
where each comes after the members it uses. -/
partial def auxOrder (infos : Std.HashMap Name ConstantInfo) (main : Name) (e : Expr) : Array Name := Id.run do
  let mut out : Array Name := #[]
  let mut seen : NameSet := {}
  let mut stack : Array (Name × Bool) := e.getUsedConstants.reverse.map (·, false)
  while !stack.isEmpty do
    let (n, post) := stack.back!
    stack := stack.pop
    if n == main || !infos.contains n then continue
    if post then
      unless out.contains n do out := out.push n
      continue
    if seen.contains n then continue
    seen := seen.insert n
    stack := stack.push (n, true)
    if let some ci := infos[n]? then
      for c in ci.getUsedConstantsAsSet.toList do
        unless seen.contains c do stack := stack.push (c, false)
  return out

/-- Name, in this module, for a member of `g` that `remote_value%` adds itself. -/
def auxName (mm : Name) (own : Std.HashMap Name Name) (m : MemberRec) : Name :=
  let n := renameName own m.name
  if isPrivateName n then mkPrivateNameCore mm (privateToUserName n) else n

/-- The published proof of the package's theorem, instantiated for the declaration being
elaborated. Adds the group's auxiliary members the proof uses (kernel-checked). -/
@[term_elab remoteValue]
def elabRemoteValue : TermElab := fun stx expected? => do
  let some pid := stx[1].isStrLit? | throwUnsupportedSyntax
  let some ty := expected? | throwError "remote_value%: expected type unknown"
  let ty ← instantiateMVars ty
  let some declName ← Term.getDeclName? | throwError "remote_value%: not inside a declaration"
  let g ← getMetaIO pid
  let env ← getEnv
  let mm := env.mainModule
  let own := (← renames).getD g.gid {}
  -- identities: the declaration being elaborated, other members by their published spelling
  let some main := g.members.find? (fun m => m.cls == "pub" &&
      (renameName own m.name == declName || auxName mm own m == declName ||
       privateToUserName (renameName own m.name) == privateToUserName declName))
    | throwError "remote_value%: {declName} is not a member of {g.short}"
  let mut self : Std.HashMap Name Name := {}
  for m in g.members do
    self := self.insert m.local_ (if m.local_ == main.local_ then declName else auxName mm own m)
  fetchedNames.modify (·.insert (mm, g.gid) self)
  let closure ← liftCommandElabM (closureOf g)
  let dg ← decodeHere g closure self
  let infos : Std.HashMap Name ConstantInfo := dg.members.foldl (fun m (_, _, ci) => m.insert ci.name ci) {}
  let some pubCi := infos[declName]? | throwError "remote_value%: {declName} missing from the payload"
  let some pubVal := pubCi.value? (allowOpaque := true) | throwError "remote_value%: {declName} has no published value"
  -- auxiliary members the proof uses (proof_n, match_n, private helpers), added first
  for n in auxOrder infos declName pubVal do
    if (← getEnv).contains n then continue
    let some ci := infos[n]? | continue
    let d : Declaration ← match ci with
      | .thmInfo v => pure (.thmDecl v)
      | .defnInfo v => pure (if v.safety == .safe then .defnDecl v else .mutualDefnDecl [v])
      | .opaqueInfo v => pure (.opaqueDecl v)
      | .axiomInfo _ => throwError "remote_value%: {g.short} contains an axiom {n}"
      | _ => throwError "remote_value%: auxiliary {n} of {g.short} is not a theorem or definition"
    addDecl d
    fetchedAdded.modify (·.insert n)
  fetchedAdded.modify (·.insert declName)
  -- universe levels and the leading binders of the published statement
  let lvl := matchLevels pubCi.type ty {}
  let inst (e : Expr) : Expr :=
    e.instantiateLevelParams pubCi.levelParams (pubCi.levelParams.map fun p => lvl.getD p (.param p))
  let lctx ← getLCtx
  let cands := lctx.getFVars.filter fun x =>
    match lctx.find? x.fvarId! with
    | some d => !d.isAuxDecl && !d.isImplementationDetail
    | none => false
  let pubTy := inst pubCi.type
  -- the declaration's binders: what the statement needs (Lean's variable rules), or every
  -- local in scope (`include`d section variables)
  for xs in [← neededVars cands ty false, ← neededVars cands ty true, cands] do
    let t ← instantiateMVars (← mkForallFVars xs ty)
    -- syntactic equality, or unification at reducible transparency when the header still
    -- has metavariables (auto-bound universes): it assigns them the published levels
    if t == pubTy || (← withReducible (isDefEq t pubTy)) then
      return (← instantiateMVars (inst pubVal)).beta xs
  let xs ← neededVars cands ty false
  throwError "remote_value%: the statement elaborated here is not the published statement of {declName}:{indentExpr (← mkForallFVars xs ty)}\nvs published{indentExpr pubTy}"

/-! ## Content check -/

/-- Compare `g`'s members in this environment with the decoded payload. Returns problems
(empty = identical) or `none` when no member is present. `proofs`: compare theorem bodies. -/
def payloadCheck (g : GroupRec) (closure : Array GroupRec) (proofs : Bool) : CommandElabM (Option (Array String)) := do
  let names ← memberNames g
  if names.isEmpty then return none
  let dg ← liftCoreM (decodeHere g closure names)
  let env ← getEnv
  let mut problems := #[]
  for ((l, _, pub), m) in dg.members.zip g.members do
    match env.find? pub.name with
    | none =>
      -- proof-internal auxiliaries of a regenerated theorem may carry other spellings
      if m.cls == "pub" then problems := problems.push s!"missing {l}"
    | some here =>
      let pub := canonLevelParams pub
      let here := canonLevelParams here
      unless pub.levelParams.length == here.levelParams.length && pub.type == here.type do
        problems := problems.push s!"statement of {pub.name} differs"
        continue
      match pub, here with
      | .defnInfo a, .defnInfo b =>
        -- interface equality (§5): bodies of Prop-typed auxiliaries (a recursive theorem's
        -- `_f`) are proofs and may differ, e.g. by a matcher reused at capture
        let isPropTy ← liftTermElabM (Meta.isProp a.type)
        unless isPropTy || a.value == b.value do
          problems := problems.push s!"body of {pub.name} differs: published {(toString a.value).take 2000} vs here {(toString b.value).take 2000}"
      | .thmInfo a, .thmInfo b =>
        -- proofs `remote_value%` took from the payload must be the payload's; members that
        -- Lean had already realized here (reserved names such as `induct_unfolding`, §3.3)
        -- only need the published statement
        if proofs && (← fetchedAdded.get).contains pub.name then unless a.value == b.value do
          let dbg := if (← IO.getEnv "PARALEAN_DEBUG_PROOFS").isSome then
            s!": fetched {(toString a.value).take 3000} vs here {(toString b.value).take 3000}" else ""
          problems := problems.push s!"proof of {pub.name} differs from the fetched one{dbg}"
      | .opaqueInfo _, .opaqueInfo _ | .inductInfo _, .inductInfo _ | .ctorInfo _, .ctorInfo _
      | .recInfo _, .recInfo _ | .axiomInfo _, .axiomInfo _ | .quotInfo _, .quotInfo _ => pure ()
      | .thmInfo _, .defnInfo _ | .defnInfo _, .thmInfo _ =>
        problems := problems.push s!"kind of {pub.name} differs"
      | _, _ => problems := problems.push s!"kind of {pub.name} differs"
  return some problems

/-- Invalidation: a version this copy knows to be superseded is never loaded, so no name in
this file can bind to it. Dependents of a deleted (tombstoned) group keep loading it. -/
def checkInvalidated (g : GroupRec) (closure : Array GroupRec) : CommandElabM Unit := do
  let v ← view
  for d in closure do
    if let some mk := v.known.byGroup[d.declId]? then
      if !v.live.contains d.declId && !Rga.tombstoned v.known mk then
        let by_ := v.known.markers.find? fun e => (v.graph.anc.getD e.group {}).contains d.declId
        let what := if d.gid == g.gid then s!"{g.publicNames} ({g.short}) is" else
          s!"{g.publicNames} ({g.short}) depends on {d.publicNames} ({d.short}), which is"
        throwError "remote%: invalidated: {what} superseded by \
          {(by_.map (·.group.take 12 |>.toString)).getD "?"}; revise it against the current version"

/-- Load `g` (dependencies first) unless already present. On failure the environment is
restored: a group that does not load leaves no constant behind (in particular none that
Lean's error recovery completed with `sorryAx`). -/
partial def ensureLoaded (g : GroupRec) : CommandElabM Unit := do
  loadingDepth.modify (· + 1)
  let env0 ← getEnv
  try ensureLoadedCore g
  catch e => setEnv env0; throw e
  finally loadingDepth.modify (· - 1)
where ensureLoadedCore (g : GroupRec) : CommandElabM Unit := do
  let closure ← closureOf g
  let mm := (← getEnv).mainModule
  checkInvalidated g closure
  for d in closure do
    if let some ns := (← verifiedCache.get)[(mm, d.gid)]? then
      let env ← getEnv
      if ns.all (fun p => env.contains p.2) then continue
    checkReceipt d
    -- a capsule that disables or weakens checking is never elaborated here, whatever its receipt
    for o in [`debug.skipKernelTC, `debug.byAsSorry, `debug.terminalTacticsAsSorry, `debug.proofAsSorry] do
      if (d.capsule.text ++ String.join d.capsule.scopeCmds.toList).contains o.toString then
        throwError "remote%: {d.short} ({d.publicNames}) sets {o}; it is never loaded"
    if d.members.isEmpty then
      let t0 ← IO.monoMsNow
      elabSourceAtRoot (capsuleSource (← renames) d false closure) s!"<remote {d.short}>"
      verifiedCache.modify (·.insert (mm, d.gid) #[])
      logEvent s!"load {d.declId} effect {(← IO.monoMsNow) - t0}ms"
      continue
    match ← payloadCheck d closure (proofs := false) with
    | some #[] =>
      verifiedCache.modify (·.insert (mm, d.gid) (← memberNames d).toArray)
    | some problems =>
      throwError "remote%: version conflict for {d.short} ({d.publicNames}): {problems}"
    | none =>
      let t0 ← IO.monoMsNow
      let fetch := proofFetched d
      let errsBefore := (← get).messages.toList.length
      elabSourceAtRoot (capsuleSource (← renames) d fetch closure) s!"<remote {d.short}>"
      let t1 ← IO.monoMsNow
      let errs ← ((← get).messages.toList.drop errsBefore).filterMapM fun m => do
        if m.severity == .error then return some (← m.toString) else return none
      unless errs.isEmpty do
        throwError "remote%: {d.short} ({d.publicNames}) does not load: {errs.take 3}"
      match ← payloadCheck d closure (proofs := fetch) with
      | some #[] =>
        verifiedCache.modify (·.insert (mm, d.gid) (← memberNames d).toArray)
      | some problems => throwError "remote%: {d.short} does not reproduce its published content: {problems}"
      | none => throwError "remote%: {d.short} produced none of its members"
      logEvent s!"load {d.declId} {if fetch then "fetched-proof" else "elaborated"} {t1 - t0}ms check {(← IO.monoMsNow) - t1}ms"

partial def findKind? (stx : Syntax) (k : SyntaxNodeKind) : Option Syntax :=
  if stx.getKind == k then some stx
  else match stx with
    | .node _ _ args => args.findSome? (findKind? · k)
    | _ => none

/-- The written value is exactly `remote% "<group>"`? -/
def remoteValue? (stx : Syntax) : Option (String × Syntax) := do
  let v ← findKind? stx ``Lean.Parser.Command.declValSimple
  let t := v[1]
  if t.getKind == ``remoteTerm then
    let lit ← t[1].isStrLit?
    some (lit, v)
  else none

/-- The written header must *mean* the published declaration where it is written: its
declared name, resolved in the current scope, is a just-loaded member, and its binders and
type, elaborated in the current scope, equal the published statement. -/
def checkWrittenHeader (g : GroupRec) (stx : Syntax) (env0 : Environment) : CommandElabM Unit := do
  let some declId := findKind? stx ``Lean.Parser.Command.declId
    | throwError "remote%: no declaration name"
  let id := declId[0].getId
  let ns ← getCurrNamespace
  let full := if (`_root_).isPrefixOf id then id.replacePrefix `_root_ .anonymous else ns ++ id
  let isPriv := (findKind? stx ``Lean.Parser.Command.private).isSome
  let env ← getEnv
  let full := if isPriv then mkPrivateNameCore env.mainModule full else full
  let loaded := (← memberNames g).toArray.map (·.2)
  unless loaded.contains full && env.contains full do
    throwError "remote%: the written declaration `{full}` is not the published declaration {g.short} (publishes {g.publicNames})"
  let some ci := env.find? full | throwError "remote%: {full} missing"
  let sig? := findKind? stx ``Lean.Parser.Command.declSig <|> findKind? stx ``Lean.Parser.Command.optDeclSig
  let some sig := sig? | return
  let binders := sig[0].getArgs
  let tyStx? : Option Syntax :=
    if sig.getKind == ``Lean.Parser.Command.declSig then some sig[1][1]
    else if sig[1].isNone then none else some sig[1][0][1]
  let some tyStx := tyStx? | return
  let sc ← getScope
  let env1 ← getEnv
  let ok ← runTermElabM fun vars => do
    setEnv env0
    let r ← Term.elabBinders binders fun xs => do
      let body ← Term.elabType tyStx
      Term.synthesizeSyntheticMVarsNoPostponing
      let tw ← instantiateMVars (← mkForallFVars xs body)
      setEnv env1
      let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
      let pub := ci.type.instantiateLevelParams ci.levelParams us
      let same (a b : Expr) : TermElabM Bool :=
        withNewMCtxDepth (allowLevelAssignments := true) <| withReducible <| isDefEq a b
      let included := (Array.range (min vars.size sc.varUIds.size)).filterMap fun i =>
        if sc.includedVars.contains sc.varUIds[i]! && !sc.omittedVars.contains sc.varUIds[i]!
        then some vars[i]! else none
      let used ← neededVars vars tw (instImplicit := true) (seed := included)
      if ← same (← instantiateMVars (← mkForallFVars used tw)) pub then return (true, tw, pub)
      let mut p := pub
      for v in vars do
        match p with
        | .forallE _ d b _ =>
          if ← same d (← inferType v) then p := b.instantiate1 v
        | _ => pure ()
      if ← same tw p then return (true, tw, pub)
      return (false, tw, pub)
    setEnv env1
    let (ok, tw, pub) := r
    unless ok do
      throwError "remote%: the written statement of `{full}` does not elaborate here to the published statement of {g.short}:{indentExpr tw}\nvs published{indentExpr pub}"
    return ok
  unless ok do
    throwError "remote%: the written statement of `{full}` does not elaborate here to the published statement of {g.short}"

@[command_elab Lean.Parser.Command.declaration]
def elabRemoteDecl : CommandElab := fun stx => do
  let some (lit, _) := remoteValue? stx | throwUnsupportedSyntax
  let g ← getMeta (← pidOfGroup lit)
  checkReceipt g
  let gr := renamedGroup (← renames) g
  if gr.capsule.valueStart.isNone then
    throwError "remote%: {g.short} has no value; write `remote_decl% \"{g.declId}\"`"
  let closure ← closureOf g
  checkInvalidated g closure
  for d in closure do
    if d.gid != g.gid then ensureLoaded d
  let env0 ← getEnv
  ensureLoaded g
  loadingDepth.modify (· + 1)
  try checkWrittenHeader g stx env0
  finally loadingDepth.modify (· - 1)

@[command_elab remoteCmd]
def elabRemoteCmd : CommandElab := fun stx => do
  let some lit := stx[1].isStrLit? | throwUnsupportedSyntax
  let g ← getMeta (← pidOfGroup lit)
  checkReceipt g
  ensureLoaded g

@[term_elab remoteTerm]
def elabRemoteTerm : TermElab := fun _ _ =>
  throwError "remote% may only be the entire value of a published declaration"

/-- Load a published package from `CoreM` (used by the name-resolution hook). -/
def loadInCore (pid : String) : CoreM Unit := do
  let env ← getEnv
  let cmdCtx : Command.Context := {
    fileName := "<registry>", fileMap := default, snap? := none, cancelTk? := none }
  let st := Command.mkState env {} (← getOptions)
  let act : CommandElabM Unit := do ensureLoaded (← getMeta pid)
  match ← (act.run cmdCtx |>.run st).toBaseIO with
  | .ok ((), st') =>
    setEnv st'.env
    for m in st'.messages.toList do
      if m.severity == .error then throwError "remote%: loading {(pid.take 8).toString}: {← m.toString}"
    loadLog.modify (·.push pid)
  | .error e => throw e

end Paralean.Remote
