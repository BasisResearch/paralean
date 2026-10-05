module

public import Lean
public meta import Lean
public meta import Paralean.Encode
public meta import Paralean.Model
public meta import Paralean.Store
public meta import Paralean.Render
public meta import Paralean.Receipt
public meta import Paralean.Crdt

public meta section

/-!
`remote%`: published declarations inside a working copy (transparent workspaces, Track B).

A teammate's published declaration appears in every other copy of its file as

```
<header exactly as published> := remote% "<package id>"     -- theorem, def, instance, ...
remote% "<package id>"                                       -- structures, notation, mutual, ...
```

Elaborating it:

1. looks up the package in the store and requires a valid validator receipt over the
   exact package and declaration ID (a forged or unknown ID is an error, never a `sorry`);
2. requires the written header to be the published header byte for byte (same name and
   statement text) and the current namespace to match;
3. loads the declaration's dependency closure from the store, independent of the file's
   imports (B→A→B never needs a module import);
4. elaborates the published capsule at the root scope. A theorem's proof is **not**
   fetched: the published statement is elaborated, its hash (with exact dependency pins)
   must equal the published one, and the proof is a receipt-backed placeholder. Defs,
   instances and structures re-elaborate their real capsule, because unfolding, `simp`
   and instance search need the bodies. Each member's encoding must equal the published
   member's.

The store and key come from `PARALEAN_STORE` and `PARALEAN_RECEIPT_KEY` (the fork would
configure them). The validator and the exporter always use real proofs.
-/

namespace Paralean.Remote
open Lean Elab Command Term Meta

syntax (name := remoteTerm) "remote% " str : term
syntax (name := remoteCmd) "remote% " str : command
/-- Internal: the receipt-backed proof placeholder of a remote theorem. -/
syntax (name := remoteProof) "remote_proof% " str : term

/-- Suffix of the placeholder axiom standing for a remote theorem's proof. -/
def placeholderSuffix : String := "_remote_proof"

def store : IO Store := do
  let some r ← IO.getEnv "PARALEAN_STORE" | throw <| IO.userError "PARALEAN_STORE is not set"
  return { root := r }

def receiptKey : IO String := do
  return (← IO.getEnv "PARALEAN_RECEIPT_KEY").getD ""

/-- Counters for measurements, appended to `$PARALEAN_REMOTE_LOG` if set. -/
def logEvent (s : String) : IO Unit := do
  if let some p ← IO.getEnv "PARALEAN_REMOTE_LOG" then
    let h ← IO.FS.Handle.mk p .append
    h.putStrLn s

/-- Depth of `remote%` loads in progress (the visibility predicate is suspended inside). -/
initialize loadingDepth : IO.Ref Nat ← IO.mkRef 0
/-- Packages loaded on demand by name resolution during the current command (for capture). -/
initialize loadLog : IO.Ref (Array String) ← IO.mkRef #[]

/-- Package metadata is immutable: cache it per process. -/
initialize metaCache : IO.Ref (Std.HashMap String GroupRec) ← IO.mkRef {}
/-- (module, package) ↦ member names already verified in that module's environment. -/
initialize verifiedCache : IO.Ref (Std.HashMap (Name × String) (Array (Name × Name))) ← IO.mkRef {}

/-- Rename maps (rule 4), recomputed when the set of publication records changes. -/
initialize renCache : IO.Ref (Nat × Std.HashMap String (Std.HashMap Name Name)) ← IO.mkRef (0, {})

def renames : IO (Std.HashMap String (Std.HashMap Name Name)) := do
  let s ← store
  let d := s.root / "pubs"
  let n ← if ← d.pathExists then pure (← d.readDir).size else pure 0
  let (k, m) ← renCache.get
  if k == n && n > 0 then return m
  let recs ← s.pubs
  let m := renamesOf (← metasFor s recs) recs
  renCache.set (n, m)
  return m

def getMeta (pid : String) : CommandElabM GroupRec := do
  if let some g := (← metaCache.get)[pid]? then return g
  let s ← store
  unless ← (s.metaPath pid).pathExists do
    throwError "remote%: no published declaration with ID {pid}"
  let g ← s.getMeta pid
  metaCache.modify (·.insert pid g)
  return g

def checkReceipt (g : GroupRec) : CommandElabM Unit := do
  let s ← store
  match ← s.getReceipt? g.gid with
  | none => throwError "remote%: {g.short} has no validator receipt; it is not published"
  | some r =>
    unless r.valid (← receiptKey) g.gid g.declId do
      throwError "remote%: the receipt for {g.short} does not verify"

/-- Lean names in the current environment of a group's members: match normalized local
identities (and the relocation tag) against this file's constants. -/
def memberNames (g : GroupRec) : CommandElabM (Std.HashMap Name Name) := do
  let env ← getEnv
  let mm := env.mainModule
  -- fast path: the published spelling, or its private form in this module
  if !g.capsule.relocate then
    let own := (← renames).getD g.gid {}
    let mut fast : Std.HashMap Name Name := {}
    for m in g.members do
      let nm := renameName own m.name
      let cands := [nm, mkPrivateNameCore mm (privateToUserName nm)]
      if let some n := cands.find? env.contains then
        if normName mm n == renameName own m.local_ then fast := fast.insert m.local_ n
    if fast.size == g.members.size then return fast
  let tag := if g.capsule.relocate then some g.short else none
  let own := (← renames).getD g.gid {}
  -- rendered local identity ↦ published local identity
  let wanted : Std.HashMap Name Name := g.members.foldl (fun m mr => m.insert (renameName own mr.local_) mr.local_) {}
  -- hygienic members (`base._hyg.<k>`): the group's k-th of the most recent constants with
  -- that base (a group is verified right after it is loaded; later checks use the cache)
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
  -- members imported from the base (materialized or prelude modules) keep their names
  for m in g.members do
    let nm := renameName own m.name
    if !out.contains m.local_ && env.contains nm then out := out.insert m.local_ nm
  return out

/-- Dependency closure of `g` (dependencies first). -/
partial def closureOf (g : GroupRec) : CommandElabM (Array GroupRec) := do
  let mut seen : Std.HashSet String := {}
  let mut out := #[]
  let rec go (gid : String) (seen : Std.HashSet String) (out : Array GroupRec) :
      CommandElabM (Std.HashSet String × Array GroupRec) := do
    if seen.contains gid then return (seen, out)
    let seen := seen.insert gid
    let r ← getMeta gid
    let mut st := (seen, out)
    for d in r.deps ++ r.feDeps do st ← go d st.1 st.2
    return (st.1, st.2.push r)
  (seen, out) ← go g.gid seen out
  let _ := seen
  return out

/-- Resolver from current Lean names to references, for the given loaded groups. -/
def resolverFor (groups : Array GroupRec) (self : GroupRec) : CommandElabM (Name → Except String Ref) := do
  let env ← getEnv
  let mut idx : Std.HashMap Name (String × Name) := {}
  let mm := env.mainModule
  for g in groups do
    let pairs ← match (← verifiedCache.get)[(mm, g.gid)]? with
      | some ps => pure ps
      | none => pure (← memberNames g).toArray
    for (l, n) in pairs do idx := idx.insert n (g.gid, l)
  let idx' := idx
  return fun c =>
    match idx'[c]? with
    | some (gid, l) => if gid == self.gid then .ok (.self l) else .ok (.dep gid l)
    | none =>
      if (env.getModuleIdxFor? c).isSome then .ok (.base c)
      else if isReservedName env c then
        match c with
        | .str p s =>
          match idx'[p]? with
          | some (gid, l) => .ok (.res (if gid == self.gid then .self l else .dep gid l) (Name.mkSimple s))
          | none => .ok (.res (.base p) (Name.mkSimple s))
        | _ => .error s!"unresolvable reserved name {c}"
      else .error s!"remote%: {c} is not a published constant"

def classOf (s : String) : NameClass :=
  match s with | "pub" => .pub | "pubAux" => .pubAux | _ => .scoped

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

/-- The capsule text to elaborate: a theorem's proof is replaced by the placeholder. -/
def capsuleSource (ren : Std.HashMap String (Std.HashMap Name Name)) (g : GroupRec) (placeholder : Bool)
    (closure : Array GroupRec) : String :=
  let g := renamedGroup ren g
  -- statement-only only when the theorem is the group's single public member: attributes
  -- that generate further declarations (`@[to_additive]`, `@[to_dual]`, …) read the proof
  let pubs := g.members.filter (·.cls == "pub")
  let theoremRoot := pubs.size == 1 && pubs.all (·.kind == "theorem")
  let g := if placeholder && theoremRoot then
      match g.capsule.valueStart with
      | some v =>
        let hdr := String.fromUTF8! (g.capsule.text.toUTF8.extract 0 v)
        { g with capsule := { g.capsule with text := hdr.trimAsciiEnd.toString ++ s!" := remote_proof% \"{g.gid}\"" } }
      | none => g
    else g
  let ds := g.deps ++ g.feDeps
  renderCapsule g ((closure.filter fun d => d.capsule.relocate && ds.contains d.gid).map (·.relocNs))

/-- Do `g`'s members exist here with the published content? `none` = not loaded. -/
def groupState (g : GroupRec) (closure : Array GroupRec) : CommandElabM (Option (Array String)) := do
  let pubs := g.members.filter (·.cls == "pub")
  let stmtOnly := pubs.size == 1 && pubs.all (·.kind == "theorem")
  let names ← memberNames g
  if names.isEmpty then return none
  let resolve ← resolverFor closure g
  let env ← getEnv
  let wire : WireCtx := {
    selfIdx := fun l => g.members.findIdx? (·.local_ == l)
    dep := wireDepOf fun pid => closure.find? (·.gid == pid) }
  let mut problems := #[]
  for m in g.members do
    match names[m.local_]? with
    | none =>
      -- internal auxiliaries of a theorem's proof are absent when the proof is a placeholder
      unless m.cls != "pub" do problems := problems.push s!"missing {m.local_}"
    | some n =>
      -- proof-internal auxiliaries (`_simp_n`, `_proof_n`, a recursive theorem's `_f`, …)
      -- are never needed by consumers and are not reproduced when the proof is a placeholder
      if m.kind == "theorem" && m.cls != "pub" then continue
      if stmtOnly && m.cls != "pub" then continue
      let some ci := env.find? n | problems := problems.push s!"missing {n}"; continue
      let isPlaceholder := match ci.value? with
        | some (.const c _) => c.getString!.endsWith placeholderSuffix
        | _ => false
      let ci := canonLevelParams ci
      let em : EncMember := { local_ := m.local_, cls := classOf m.cls, info := ci }
      if isPlaceholder || m.kind == "theorem" then
        let stmt : EncMember := { em with info := .axiomInfo {
          name := ci.name, levelParams := ci.levelParams, type := ci.type, isUnsafe := false } }
        match encodeGroup baseId #[stmt] resolve wire with
        | .ok b => unless groupIdOf b == m.typeHash do problems := problems.push s!"statement of {n} differs"
        | .error e => problems := problems.push e
      else
        match encodeGroup baseId #[em] resolve wire with
        | .ok b => unless (groupIdOf b).take 12 == m.hash do problems := problems.push s!"body of {n} differs"
        | .error e => problems := problems.push e
  return some problems
where
  baseId := s!"lean:{Lean.githash}"

/-- Load `g` (dependencies first) unless already present. -/
partial def ensureLoaded (g : GroupRec) (placeholder : Bool) : CommandElabM Unit := do
  loadingDepth.modify (· + 1)
  try ensureLoadedCore g placeholder
  finally loadingDepth.modify (· - 1)
where ensureLoadedCore (g : GroupRec) (placeholder : Bool) : CommandElabM Unit := do
  let closure ← closureOf g
  let mm := (← getEnv).mainModule
  for d in closure do
    -- verified earlier in this module and still present: nothing to do
    if let some ns := (← verifiedCache.get)[(mm, d.gid)]? then
      let env ← getEnv
      if ns.all (fun p => env.contains p.2) then continue
    checkReceipt d
    if d.members.isEmpty then
      -- effect-only group (attribute, docs, …): run once per module
      let t0 ← IO.monoMsNow
      elabSourceAtRoot (capsuleSource (← renames) d placeholder closure) s!"<remote {d.short}>"
      verifiedCache.modify (·.insert (mm, d.gid) #[])
      logEvent s!"load {d.gid} effect {(← IO.monoMsNow) - t0}ms"
      continue
    match ← groupState d closure with
    | some #[] =>   -- present with the published content (local or loaded before)
      let ns := (← memberNames d).toArray
      verifiedCache.modify (·.insert (mm, d.gid) ns)
    | some problems =>
      throwError "remote%: version conflict for {d.short} ({d.publicNames}): {problems}"
    | none =>
      let t0 ← IO.monoMsNow
      elabSourceAtRoot (capsuleSource (← renames) d placeholder closure) s!"<remote {d.short}>"
      match ← groupState d closure with
      | some #[] =>
        let ns := (← memberNames d).toArray
        verifiedCache.modify (·.insert (mm, d.gid) ns)
      | some problems => throwError "remote%: {d.short} does not reproduce its published content: {problems}"
      | none =>
        let errs ← (← get).messages.toList.filterMapM fun m => do
          if m.severity == .error then return some (← m.toString) else return none
        throwError "remote%: {d.short} produced none of its members: {errs.take 3}"
      let pubs := d.members.filter (·.cls == "pub")
      let isThm := pubs.size == 1 && pubs.all (·.kind == "theorem")
      logEvent s!"load {d.gid} {if isThm && placeholder then "statement" else "full"} {(← IO.monoMsNow) - t0}ms"

partial def findKind? (stx : Syntax) (k : SyntaxNodeKind) : Option Syntax :=
  if stx.getKind == k then some stx
  else match stx with
    | .node _ _ args => args.findSome? (findKind? · k)
    | _ => none

/-- The written value is exactly `remote% "<pid>"`? -/
def remoteValue? (stx : Syntax) : Option (String × Syntax) := do
  let v ← findKind? stx ``Lean.Parser.Command.declValSimple
  let t := v[1]
  if t.getKind == ``remoteTerm then
    let pid ← t[1].isStrLit?
    some (pid, v)
  else none

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

/-- The written header must *mean* the published declaration where it is written:
1. its declared name, resolved in the current scope (namespace, `_root_`, `private`), is
   the Lean name of a published member that was just loaded;
2. its binders and type, elaborated in the current scope (opens, variables, notation of
   this file), are definitionally equal at reducible transparency to the loaded
   published statement. Shadowing through `open`, a local definition or misplacement in
   another namespace therefore fails. -/
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
  -- the written statement, in this scope
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
      -- 1. Lean's statement rule: needed + `include`d + instance-implicit section variables
      let included := (Array.range (min vars.size sc.varUIds.size)).filterMap fun i =>
        if sc.includedVars.contains sc.varUIds[i]! && !sc.omittedVars.contains sc.varUIds[i]!
        then some vars[i]! else none
      let used ← neededVars vars tw (instImplicit := true) (seed := included)
      if ← same (← instantiateMVars (← mkForallFVars used tw)) pub then return (true, tw, pub)
      -- 2. definitions may include section variables their body uses: peel the published
      --    leading binders against the section variables, in order
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
  let some (pid, valStx) := remoteValue? stx | throwUnsupportedSyntax
  let g ← getMeta pid
  checkReceipt g
  -- the written header must be the published (rendered) header
  let gr := renamedGroup (← renames) g
  let some v := gr.capsule.valueStart
    | throwError "remote%: {g.short} has no value; write `remote% \"{pid}\"` as a command"
  let published := (String.fromUTF8! (gr.capsule.text.toUTF8.extract 0 v)).trimAscii.toString
  let src := (← getFileMap).source
  let some a := stx.getPos? | throwError "remote%: no source position"
  let some b := valStx.getPos? | throwError "remote%: no source position"
  let written := (String.fromUTF8! (src.toUTF8.extract a.byteIdx b.byteIdx)).trimAscii.toString
  unless written == published do
    throwError "remote%: the header does not match the published declaration {g.short}:\n  published: {published}\n  written:   {written}"
  -- dependencies first; the written header is elaborated in the environment *before* the
  -- declaration itself exists (its own names must not capture identifiers in its header)
  let closure ← closureOf g
  for d in closure do
    if d.gid != g.gid then ensureLoaded d (placeholder := true)
  let env0 ← getEnv
  ensureLoaded g (placeholder := true)
  -- judged in the context it was published in: names published elsewhere (visible to
  -- drafts through the name-resolution hook) must not capture its identifiers
  loadingDepth.modify (· + 1)
  try checkWrittenHeader g stx env0
  finally loadingDepth.modify (· - 1)

@[command_elab remoteCmd]
def elabRemoteCmd : CommandElab := fun stx => do
  let some pid := stx[1].isStrLit? | throwUnsupportedSyntax
  let g ← getMeta pid
  checkReceipt g
  ensureLoaded g (placeholder := true)

@[term_elab remoteTerm]
def elabRemoteTerm : TermElab := fun _ _ =>
  throwError "remote% may only be the entire value of a published declaration"

/-- Proof placeholder: checks the elaborated statement against the published statement
hash (with exact dependency pins) before standing in for the proof. -/
@[term_elab remoteProof]
def elabRemoteProof : TermElab := fun stx expected? => do
  let some pid := stx[1].isStrLit? | throwUnsupportedSyntax
  let some ty := expected? | throwError "remote_proof%: expected type unknown"
  let ty ← instantiateMVars ty
  -- abstract the theorem's binders (and section variables) in scope
  let lctx ← getLCtx
  let cands := lctx.getFVars.filter fun x =>
    match lctx.find? x.fvarId! with
    | some d => !d.isAuxDecl && !d.isImplementationDetail
    | none => false
  -- only what the statement needs: abstracting unused section variables would make Lean
  -- include them in the declaration
  let xs ← neededVars cands ty (instImplicit := false)
  let axTy ← instantiateMVars (← mkForallFVars xs ty)
  if axTy.hasMVar || axTy.hasFVar then
    throwError "remote_proof%: the published statement did not elaborate to a closed type"
  let some declName ← Term.getDeclName? | throwError "remote_proof%: not inside a declaration"
  let lps := (collectLevelParams {} axTy).params.toList
  let ax := declName ++ Name.mkSimple placeholderSuffix
  addDecl (.axiomDecl { name := ax, levelParams := lps, type := axTy, isUnsafe := false })
  logEvent s!"placeholder {pid}"
  return mkAppN (mkConst ax (lps.map Level.param)) xs

/-- Load a published package from `CoreM` (used by the name-resolution hook). -/
def loadInCore (pid : String) : CoreM Unit := do
  let env ← getEnv
  let cmdCtx : Command.Context := {
    fileName := "<registry>", fileMap := default, snap? := none, cancelTk? := none }
  let st := Command.mkState env {} (← getOptions)
  let act : CommandElabM Unit := do ensureLoaded (← getMeta pid) (placeholder := true)
  match ← (act.run cmdCtx |>.run st).toBaseIO with
  | .ok ((), st') =>
    setEnv st'.env
    for m in st'.messages.toList do
      if m.severity == .error then throwError "remote%: loading {(pid.take 8).toString}: {← m.toString}"
    loadLog.modify (·.push pid)
  | .error e => throw e

end Paralean.Remote
