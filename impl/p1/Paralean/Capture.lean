import Lean
import Paralean.Encode
import Paralean.Model
import Paralean.Store
import Paralean.Render
import Paralean.Hooks
import Paralean.InstName
import Paralean.Remote
import Paralean.Crdt
import Paralean.Fork

/-!
Command-granularity capture.

A `Session` drives the stock Lean frontend one command at a time (`Elab.async := false`).
For each command it diffs the local constants, the exported entries of every persistent
environment extension, the messages and the info trees, then builds one group holding
every `addDecl` the command performed (including nested realizations), minus reserved
names, which are recorded but never published.
-/

namespace Paralean
open Lean Elab Frontend

/-! ## Session state -/

structure Session where
  cmdState : Command.State
  mainModule : Name
  /-- Lean name in this session's environment ↦ (package id, local identity). -/
  index : Std.HashMap Name (String × Name) := {}
  /-- Package ID ↦ (group ID, member local identities in canonical order): the wire form
  of dependency references (OPEN-22/23). -/
  pkgs : Std.HashMap String (String × Array Name) := {}
  /-- Constants introduced only as capsule scaffolding (local effects re-run in a capsule). -/
  scaffold : NameSet := {}
  /-- Constant ↦ effect groups whose command targeted it (`attribute [...] c`). -/
  effectTargets : Std.HashMap Name (Array String) := {}
  /-- Memoized transitive axioms. -/
  axCache : Std.HashMap Name (Array Name) := {}
  /-- Store for resolving `remote%` references (transparent workspaces). -/
  remoteStore? : Option Store := none
  /-- Cache of package metadata read for `remote%` commands (immutable). -/
  remoteMetas : Std.HashMap String GroupRec := {}
  /-- Rename maps (rule 4) of the registry, for matching loaded constants. -/
  remoteRenames : Std.HashMap String (Std.HashMap Name Name) := {}
  /-- Groups whose command registered initializers (options, trace classes, refs). -/
  initGroups : Array String := #[]
  /-- Placeholder axioms of remote theorems (receipt-backed; allowed by the audit). -/
  remoteAxioms : NameSet := {}
  /-- Pinned target contracts. -/
  targets : Array TargetContract := #[]
  /-- Groups rejected by policy; dependents are rejected too. -/
  rejected : Std.HashSet String := {}
  /-- Options injected by the host; excluded from rendered capsules. -/
  hostOpts : Array Name := #[`Elab.async]

/-- Result of elaborating one command. -/
structure CmdResult where
  stx : Syntax
  /-- Byte range of the command in its input (excluding surrounding trivia). -/
  startPos : Nat
  endPos : Nat
  scopeBefore : Elab.Command.Scope
  scopesAfter : List Elab.Command.Scope
  envBefore : Environment
  envAfter : Environment
  newConsts : Array ConstantInfo
  /-- Fork collector only: constants created by `realizeConst` (provenance). -/
  realizedNames : NameSet := {}
  /-- Fork collector only: constants the kernel rejected (re-added as axioms by stock Lean). -/
  unchecked : Array Name := #[]
  msgs : Array Message
  touched : Array (Name × Nat)
  trees : Array InfoTree
  /-- Command state after the command (info trees cleared). -/
  stateAfter : Command.State

/-- Extensions whose entries change for bookkeeping reasons only. -/
def noiseExtNames : List String :=
  ["Lean.declRangeExt", "_private.Lean.ExtraModUses.0.Lean.extraModUses", "Lean.indirectModUseExt",
   "_private.Lean.Namespace.0.Lean.namespacesExt"]

def isNoiseExt (n : Name) : Bool := noiseExtNames.contains n.toString

unsafe def touchedExts (pExts : Array (PersistentEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState))
    (before after : Environment) : Array (Name × Nat) :=
  pExts.filterMap fun e =>
    let s0 := e.getState before
    let s1 := e.getState after
    if ptrAddrUnsafe s0 == ptrAddrUnsafe s1 then none
    else
      let n0 := (e.exportEntriesFn before s0).private.size
      let n1 := (e.exportEntriesFn after s1).private.size
      if n0 == n1 then none else some (e.name, n1 - n0)

/-- Elaborate every command of `inputCtx` from `parserState`, calling `k` after each. -/
unsafe def runCommands (cmdState : Command.State) (inputCtx : Parser.InputContext)
    (parserState : Parser.ModuleParserState) (k : CmdResult → IO (Option Command.State)) :
    IO Command.State := do
  let pExts ← persistentEnvExtensionsRef.get
  -- fork hook 2: the per-command collector replaces the O(n) diff of local constants
  let collector := (← Fork.use).collector
  let rec loop (fuel : Nat) : FrontendM Unit := do
    match fuel with
    | 0 => throw <| IO.userError "runCommands: command limit exceeded"
    | fuel + 1 =>
      let st0 ← getCommandState
      let before := st0.env
      let nMsgs := st0.messages.toArray.size
      let mark := Fork.declMark before
      let localBefore ← if collector then pure #[] else before.getLocalConstantInfos
      let done ← processCommand
      let st1 ← getCommandState
      let after := st1.env
      let stx := (← get).commands.back!
      let (newConsts, realizedNames, unchecked) ← if collector then do
          -- complete only after the command's kernel tasks (`addedSince` waits for them)
          let added ← Fork.addedSince after mark
          pure (added.map (·.info),
            added.foldl (fun s a => if a.realized then s.insert a.info.name else s) ({} : NameSet),
            (added.filter (!·.checked)).map (·.info.name))
        else do
          let localAfter ← after.getLocalConstantInfos
          let bset : NameSet := localBefore.foldl (fun s c => s.insert c.name) {}
          pure ((localAfter.filter fun c => !bset.contains c.name).map (·.toConstantInfo), {}, #[])
      let msgs := st1.messages.toArray.extract nMsgs st1.messages.toArray.size
      let touched := touchedExts pExts before after
      let trees := st1.infoState.trees.toArray
      let st1' := { st1 with infoState := { st1.infoState with trees := {} } }
      setCommandState st1'
      let startPos := (stx.getPos? (canonicalOnly := true)).getD (← get).cmdPos |>.byteIdx
      let endPos := (stx.getTailPos? (canonicalOnly := true)).getD (← getParserState).pos |>.byteIdx
      k { stx, startPos, endPos, scopeBefore := st0.scopes.head!, scopesAfter := st1.scopes,
          envBefore := before, envAfter := after, newConsts, realizedNames, unchecked, msgs, touched, trees
          stateAfter := st1' } >>= fun
        | some st => setCommandState st
        | none => pure ()
      unless done do loop fuel
  let (_, s) ← (loop 1000000 { inputCtx }).run
    { commandState := cmdState, parserState, cmdPos := parserState.pos }
  return s.commandState

/-! ## Syntax helpers -/

partial def syntaxKinds (stx : Syntax) (acc : NameSet := {}) : NameSet :=
  match stx with
  | .node _ k args => args.foldl (fun a s => syntaxKinds s a) (acc.insert k)
  | _ => acc

partial def findNodes (stx : Syntax) (p : Syntax → Bool) (acc : Array Syntax := #[]) : Array Syntax :=
  let acc := if p stx then acc.push stx else acc
  match stx with
  | .node _ _ args => args.foldl (fun a s => findNodes s p a) acc
  | _ => acc

def hasLocalAttrKind (stx : Syntax) : Bool :=
  (findNodes stx fun s => s.getKind == ``Lean.Parser.Term.local).size > 0

/-- Marker in front of an instance name that capture made explicit: still a generated name. -/
def genMarker : String := "/-pl:gen-/"

/-- Names declared by `declId`s of the command, resolved against the current namespace. -/
def declaredRoots (stx : Syntax) (ns : Name) : Array Name :=
  -- declIds of instances whose name capture made explicit (the marker is trivia of the
  -- preceding token, so test the whole instance node)
  let generated := (findNodes stx (·.getKind == ``Lean.Parser.Command.instance)).filterMap fun i =>
    if ((i.reprint.getD "").splitOn genMarker).length > 1 then some i[3][0] else none
  (findNodes stx fun s => s.getKind == ``Lean.Parser.Command.declId).filterMap fun d =>
    if generated.any (·.getPos? == d.getPos?) then none else
    let id := d[0].getId
    if id.isAnonymous then none
    else match id with
      | .str .anonymous "_root_" => none
      | _ =>
        if (`_root_).isPrefixOf id then some (id.replacePrefix `_root_ .anonymous)
        else some (ns ++ id)

def isDeclarationCmd (stx : Syntax) : Bool :=
  let k := stx.getKind
  k == ``Lean.Parser.Command.declaration || k == ``Lean.Parser.Command.mutual ||
  (k == ``Lean.Parser.Command.in && stx[2].getKind == ``Lean.Parser.Command.declaration)

def scopeKinds : List Name :=
  [``Lean.Parser.Command.namespace, ``Lean.Parser.Command.section, ``Lean.Parser.Command.end,
   ``Lean.Parser.Command.open, ``Lean.Parser.Command.variable, ``Lean.Parser.Command.universe,
   ``Lean.Parser.Command.set_option, ``Lean.Parser.Command.include, ``Lean.Parser.Command.omit,
   ``Lean.Parser.Command.eoi]

/-- Options that disable or weaken checking. -/
def bypassOptions : List Name :=
  [`debug.skipKernelTC, `debug.byAsSorry, `debug.terminalTacticsAsSorry, `debug.proofAsSorry]

def setOptionNames (stx : Syntax) : Array Name :=
  (findNodes stx fun s =>
      s.getKind == ``Lean.Parser.Command.set_option || s.getKind == ``Lean.Parser.Term.set_option ||
      s.getKind == ``Lean.Parser.Tactic.set_option).map fun s => s[1].getId

/-! ## Text helpers -/

def sliceBytes (s : String) (a b : Nat) : String :=
  String.fromUTF8! (s.toUTF8.extract a b)

def lineOf (fm : FileMap) (pos : Nat) : Nat := (fm.toPosition ⟨pos⟩).line

/-- Apply byte edits `(start, stop, replacement)` (non-overlapping) to `s`. -/
def applyEdits (s : String) (edits : Array (Nat × Nat × String)) : String := Id.run do
  let edits := edits.qsort (·.1 < ·.1)
  let b := s.toUTF8
  let mut out := ByteArray.empty
  let mut pos := 0
  for (a, z, r) in edits do
    out := out ++ b.extract pos a ++ r.toUTF8
    pos := z
  out := out ++ b.extract pos b.size
  return String.fromUTF8! out

/-! ## Scope rendering -/

def renderDataValue : DataValue → String
  | .ofString s => s.quote
  | .ofBool b => toString b
  | .ofName n => s!"`{n}"
  | .ofNat n => toString n
  | .ofInt i => toString i
  | .ofSyntax s => toString s

def renderOpen : OpenDecl → String
  | .simple ns [] => s!"open {nameText ns}"
  | .simple ns ex => s!"open {nameText ns} hiding {" ".intercalate (ex.map nameText)}"
  | .explicit id decl =>
    s!"open {nameText decl.getPrefix} renaming {nameText (Name.mkSimple decl.getString!)} → {nameText id}"

/-- `@[expose] public noncomputable meta section` header reproducing the scope flags. -/
def sectionHeaderOf (sc : Elab.Command.Scope) : String :=
  let expose := sc.attrs.any fun a => (a.raw.reprint.getD "").trimAscii.toString == "expose"
  if !(sc.isPublic || sc.isMeta || expose) then "" else
  (if expose then "@[expose] " else "") ++ (if sc.isPublic then "public " else "") ++
  (if sc.isNoncomputable then "noncomputable " else "") ++ (if sc.isMeta then "meta " else "") ++
  "section"

structure ScopeRender where
  opens : Array String
  scopeCmds : Array String
  diags : Array Diag

def renderScope (sess : Session) (sc : Elab.Command.Scope) : ScopeRender := Id.run do
  let mut diags := #[]
  let opens := sc.openDecls.reverse.toArray.map renderOpen
  let mut cmds := #[]
  unless sc.levelNames.isEmpty do
    cmds := cmds.push s!"universe {" ".intercalate (sc.levelNames.reverse.map nameText)}"
  for v in sc.varDecls do
    match v.raw.reprint with
    | some t => cmds := cmds.push s!"variable {t.trimAscii}"
    | none => diags := diags.push { severity := "unsupported", code := "variable-reprint",
                                     msg := "cannot reprint a section variable binder" }
  let userOf (u : Name) := u.eraseMacroScopes
  unless sc.includedVars.isEmpty do
    cmds := cmds.push s!"include {" ".intercalate (sc.includedVars.map (nameText ∘ userOf))}"
  unless sc.omittedVars.isEmpty do
    cmds := cmds.push s!"omit {" ".intercalate (sc.omittedVars.map (nameText ∘ userOf))}"
  for (k, v) in sc.opts do
    unless sess.hostOpts.contains k do
      cmds := cmds.push s!"set_option {k} {renderDataValue v}"
  unless sc.attrs.all (fun a => (a.raw.reprint.getD "").trimAscii.toString == "expose") do
    diags := diags.push { severity := "unsupported", code := "section-attrs",
                          msg := "section-level attributes are not rendered" }

  return { opens, scopeCmds := cmds, diags }

/-! ## Axioms -/

partial def axiomsOf (env : Environment) (n : Name) : StateM (Std.HashMap Name (Array Name)) (Array Name) := do
  if let some a := (← get)[n]? then return a
  -- insert a placeholder to cut cycles (none in a well-formed environment)
  modify (·.insert n #[])
  let res ← match env.find? n with
    | some (.axiomInfo _) => pure #[n]
    | some ci => do
      let mut acc : Array Name := #[]
      for c in ci.getUsedConstantsAsSet do
        for a in ← axiomsOf env c do
          unless acc.contains a do acc := acc.push a
      pure acc
    | none => pure #[]
  modify (·.insert n res)
  return res

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-! ## Group construction -/

structure FileCtx where
  workspace : String
  file : String
  module : Name
  imports : Array Name
  input : String
  fileMap : FileMap
  baseEnv : Environment
  /-- Local-effect texts with the scope depth they were issued at. -/
  localEffects : Array (Nat × String) := #[]
  isModule : Bool := false
  importSpecs : Array String := #[]
  /-- Groups of this file that registered lemmas in the simp / grind sets. -/
  simpSetGroups : Array String := #[]
  grindSetGroups : Array String := #[]
  /-- Effect groups of this file so far (conservative frontend dependencies). -/
  effectGroups : Array String := #[]

inductive Outcome where
  | group (g : GroupRec) (bytes : ByteArray)
  | skipped (why : String)
  | failed (diags : Array Diag)

def baseId : String := s!"lean:{Lean.githash}"

def classNameOf : NameClass → String
  | .pub => "pub" | .pubAux => "pubAux" | .scoped => "scoped"

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

/-- Base constant of a reserved name: `f.eq_1 ↦ f`, `_private.M.0.m.eq_1 ↦ m` if `m` exists. -/
def reservedBase (env : Environment) (n : Name) : Option (Name × Name) :=
  let candidates := [n, privateToUserName n]
  candidates.findSome? fun c =>
    match c with
    | .str p s => if env.contains p then some (p, Name.mkSimple s) else none
    | _ => none

/-- Package identity: declaration content + capsule + frontend dependencies. -/
def packageId (declId : String) (c : Capsule) (feDeps : Array String) : String :=
  let w : W := {}
  let w := (w.str "paralean-package-v1").str declId
  let w := w.str (toJson c).compress
  let w := (feDeps.qsort (· < ·)).foldl W.str (w.nat feDeps.size)
  Sha256.hashHex w.out

/-- Elaborator and syntax-kind names used by the command (from its syntax and info trees). -/
partial def frontendNames (stx : Syntax) (trees : Array InfoTree) : NameSet := Id.run do
  let mut acc := syntaxKinds stx
  for t in trees do
    acc := t.foldInfo (init := acc) fun _ i acc =>
      match i with
      | .ofTermInfo ti => syntaxKinds ti.stx (acc.insert ti.elaborator)
      | .ofCommandInfo ci => acc.insert ci.elaborator
      | .ofTacticInfo ti => syntaxKinds ti.stx (acc.insert ti.elaborator)
      | .ofMacroExpansionInfo mi => syntaxKinds mi.output (syntaxKinds mi.stx acc)
      | _ => acc
  return acc

/-- Constants referenced by term info in the info trees (attribute targets etc.). -/
def referencedConsts (trees : Array InfoTree) : NameSet := Id.run do
  let mut acc : NameSet := {}
  for t in trees do
    acc := t.foldInfo (init := acc) fun _ i acc =>
      match i with
      | .ofTermInfo ti => match ti.expr with
        | .const n _ => acc.insert n
        | _ => acc
      -- lemmas a `simp` call used (recorded by fork hook 4, or by `Paralean.Hooks` on stock)
      | .ofCustomInfo ci => match Fork.simpUsed? ci <|> (ci.value.get? Hooks.SimpUsed).map (·.names) with
        | some names => names.foldl (·.insert ·) acc
        | none => acc
      | _ => acc
  return acc

/-- Map syntax kinds to the declarations implementing them (macros and elaborators). -/
def implementors (env : Environment) (kinds : NameSet) : Array Name := Id.run do
  let mut out := #[]
  for k in kinds do
    for e in macroAttribute.getEntries env k do out := out.push e.declName
    for e in Term.termElabAttribute.getEntries env k do out := out.push e.declName
    for e in Command.commandElabAttribute.getEntries env k do out := out.push e.declName
    for e in Tactic.tacticElabAttribute.getEntries env k do out := out.push e.declName
  return out

/--
Analyse one elaborated command. Returns the outcome and the updated session/file context.
`expectDecl?` is set when replaying a stored group: the produced declaration ID must match.
-/
def analyze (sess : Session) (fc : FileCtx) (r : CmdResult) (pidOverride? : Option String := none) :
    IO (Session × FileCtx × Outcome) := do
  -- canonical instance names the fork chose during this command (fork hook 5)
  let forkNames ← Fork.takeChosen
  let env := r.envAfter
  let kind := r.stx.getKind
  let line := lineOf fc.fileMap r.startPos
  let endLine := lineOf fc.fileMap r.endPos
  let mkDiag (sev code msg : String) : Diag := { severity := sev, code, msg, file := fc.file, line }
  -- pop local effects whose section has closed
  let depth := r.scopesAfter.length
  let fc := { fc with localEffects := fc.localEffects.filter (·.1 ≤ depth) }
  let errs := r.msgs.filter (·.severity == .error)
  if !errs.isEmpty then
    let mut ds := #[]
    for m in errs do ds := ds.push (mkDiag "reject" "elab-error" (← m.toString).trimAscii.toString)
    return (sess, fc, .failed ds)
  -- fork hook 3: a declaration the kernel rejected is never published (stock Lean would have
  -- re-added it as an axiom; the fork keeps it out of the kernel environment)
  if !r.unchecked.isEmpty then
    return (sess, fc, .failed #[mkDiag "reject" "kernel-rejected"
      s!"the kernel rejected {r.unchecked.toList}"])
  let text := sliceBytes fc.input r.startPos r.endPos
  -- `remote%` elements and on-demand loads (name resolution): constants of published
  -- packages are dependencies, never members of this command's group.
  let remotePid? := (findNodes r.stx fun s =>
      s.getKind == `Paralean.Remote.remoteTerm || s.getKind == `Paralean.Remote.remoteCmd)[0]?.bind
    fun s => s[1].isStrLit?
  let logged ← Remote.loadLog.swap #[]
  let mut sess := sess
  let mut consumed : NameSet := {}
  if let some st := sess.remoteStore? then
    let roots := (remotePid?.toArray) ++ logged
    if !roots.isEmpty then
      let mut metas : Array GroupRec := #[]
      let mut todo := roots
      let mut seen : Std.HashSet String := {}
      let mut cache := sess.remoteMetas
      while !todo.isEmpty do
        let g := todo.back!
        todo := todo.pop
        if seen.contains g then continue
        seen := seen.insert g
        let m ← match cache[g]? with
          | some m => pure m
          | none => do let m ← st.getMeta g; cache := cache.insert g m; pure m
        metas := metas.push m
        todo := todo ++ m.deps ++ m.feDeps
      let mut index := sess.index
      let mut remoteAxioms := sess.remoteAxioms
      for ci in r.newConsts do
        let n := ci.name
        if n.getString!.endsWith "_remote_proof" then
          remoteAxioms := remoteAxioms.insert n
          consumed := consumed.insert n
          continue
        let tag := n.components.findSome? fun c => match c with
          | .str .anonymous s => plComponent? s
          | _ => none
        let l := normName sess.mainModule n
        for m in metas do
          sess := { sess with pkgs := sess.pkgs.insert m.gid (m.declId, m.members.map (·.local_)) }
        if let some m := metas.find? fun m =>
            (if m.capsule.relocate then some m.short else none) == tag &&
            m.members.any (fun mr => renameName (sess.remoteRenames.getD m.gid {}) mr.local_ == l) then
          let own := sess.remoteRenames.getD m.gid {}
          let orig := (m.members.find? (fun mr => renameName own mr.local_ == l)).map (·.local_) |>.getD l
          index := index.insert n (m.gid, orig)
          consumed := consumed.insert n
      sess := { sess with index, remoteAxioms, remoteMetas := cache }
  if remotePid?.isSome then
    return (sess, fc, .skipped "remote")
  let r := { r with newConsts := r.newConsts.filter fun c => !consumed.contains c.name }
  let mut diags : Array Diag := #[]
  for o in bypassOptions do
    if (r.scopeBefore.opts.find? o).isSome || (setOptionNames r.stx).contains o then
      diags := diags.push (mkDiag "reject" "bypass-option" s!"option {o} disables or weakens checking")
  -- Section-local effects (`local notation`, `attribute [local ...]`, `open scoped`) are not
  -- published; their text travels in the capsule of every later command in the section.
  -- Constants they create are capsule scaffolding.
  let isOpenScoped := kind == ``Lean.Parser.Command.open &&
    !(findNodes r.stx (·.getKind == ``Lean.Parser.Command.openScoped)).isEmpty
  if (hasLocalAttrKind r.stx && !isDeclarationCmd r.stx) || isOpenScoped then
    let scaffold := r.newConsts.foldl (fun s c => s.insert c.name) sess.scaffold
    return ({ sess with scaffold }, { fc with localEffects := fc.localEffects.push (r.scopesAfter.length, text) },
      .skipped "local-effect")
  -- Elaboration is pinned synchronous (auxiliary names and publication timing depend on
  -- it). A command or scope that changes `Elab.async` is rejected.
  if (setOptionNames r.stx).contains `Elab.async || Elab.async.get r.scopeBefore.opts then
    diags := diags.push (mkDiag "reject" "async-override"
      "`Elab.async` is pinned to false; changing it is not permitted")
  if r.newConsts.isEmpty then
    if scopeKinds.contains kind then
      return (sess, fc, .skipped "scope")
    let touched := r.touched.filter fun (n, _) => !isNoiseExt n
    if touched.isEmpty then
      return (sess, fc, .skipped "no-effect")
  -- Classify new constants.
  let roots := declaredRoots r.stx r.scopeBefore.currNamespace
  let isDecl := isDeclarationCmd r.stx
  let mut members : Array EncMember := #[]
  let mut memberRecs : Array MemberRec := #[]
  let mut realized : Array Name := #[]
  let coreCtx : Core.Context := { fileName := fc.file, fileMap := fc.fileMap }
  let coreSt : Core.State := { env }
  let instNames := (Meta.instanceExtension.getState env).instanceNames
  -- Instance names (docs/p0-interfaces.md §3.2). Auto-named instances and deriving outputs
  -- are public: users can write them and two groups producing one collide. An anonymous
  -- `instance` is named canonically by `InstName` (no `_n`, no project suffix); the
  -- hook reports which names it chose, with the stock name for the G2 oracle.
  let libNames ← InstName.chosen.swap #[]
  let chosen : Std.HashMap Name Name := if (← Fork.use).instnames then
      forkNames.foldl (fun m c => m.insert c.canonical c.stock) {}
    else libNames.foldl (fun m (c, st) => m.insert c st) {}
  -- the fork's names must be byte-identical to this library's (`InstName.canonicalName`)
  for c in forkNames do
    let some ci := env.find? c.canonical <|> env.find? (mkPrivateName env c.canonical) | continue
    -- in the command's namespace: the stock base name drops components that match it
    let ctx : Core.Context := { fileName := fc.file, fileMap := fc.fileMap,
                                currNamespace := r.scopeBefore.currNamespace,
                                openDecls := r.scopeBefore.openDecls }
    let (lib, _) ← ((InstName.canonicalName ci.type).run' {} {}).toIO ctx { env }
    unless c.canonical.getPrefix ++ lib == c.canonical do
      diags := diags.push (mkDiag "reject" "instance-name-mismatch"
        s!"the fork named an instance {c.canonical}, the library computes {c.canonical.getPrefix ++ lib}")
  let anonInstCmd := (findNodes r.stx (·.getKind == ``Lean.Parser.Command.instance)).any (·[3].isNone)
  let derives :=
    !(findNodes r.stx fun s => s.getKind == ``Lean.Parser.Command.optDeriving && !s[0].isNone).isEmpty ||
    !(findNodes r.stx (·.getKind == ``Lean.Parser.Command.deriving)).isEmpty
  if anonInstCmd && chosen.isEmpty && (← IO.getEnv "PARALEAN_STOCK_INSTANCE_NAMES").isNone &&
      (← IO.getEnv "PARALEAN_NO_HOOKS").isNone then
    -- e.g. an anonymous instance inside `mutual`, which bypasses the declaration elaborator
    diags := diags.push (mkDiag "unsupported" "noncanonical-instance"
      "anonymous instance not named by the canonical scheme")
  -- Deriving outputs keep the deriving handler's spelling (a stock export cannot name
  -- them). That spelling is canonical as long as stock did not deduplicate it: a `_n`
  -- suffix means the name was already taken, which is a collision, never a rename.
  if derives then
    for ci in r.newConsts do
      let n := ci.name
      unless instNames.contains n && !roots.contains n && !chosen.contains n do continue
      if let .str p s := n then
        match s.splitOn "_" |>.reverse with
        | k :: rest =>
          if k.toNat?.isSome && !rest.isEmpty && r.envBefore.contains (.str p ("_".intercalate rest.reverse)) then
            diags := diags.push (mkDiag "reject" "instance-name-clash"
              s!"derived instance would be named {n} because {Name.str p ("_".intercalate rest.reverse)} \
                already exists: a collision (canonical instance names take no `_n` suffix)")
        | [] => pure ()
  -- an auxiliary belongs to a public root if some proper prefix is a non-internal new name
  let newNames : NameSet := r.newConsts.foldl (fun s c => s.insert c.name) {}
  let publicRootOf (n : Name) : Bool :=
    let rec go : Name → Bool
      | .str p _ => (newNames.contains p && !p.isInternal) || go p
      | .num p _ => go p
      | .anonymous => false
    go n
  for ci in r.newConsts do
    let n := ci.name
    if isReservedName env n then
      realized := realized.push n
      continue
    -- provenance cross-check (p0-interfaces.md §3.2): the collector knows which constants
    -- `realizeConst` created; the spelling classifier above decides membership
    if r.realizedNames.contains n then
      diags := diags.push (mkDiag "note" "provenance"
        s!"{n} was created by realizeConst but is not spelled as a reserved name")
    let user := privateToUserName n
    let hasPl := n.components.any fun c => match c with
      | .str .anonymous s => (plComponent? s).isSome | _ => false
    let underRoot := roots.any (·.isPrefixOf user)
    -- Provenance classes (LEAN-NAMES.md): scoped = private, or an internal/hygienic name
    -- outside any public root. Auto-named instances, deriving outputs and names that
    -- attributes, `alias`, notation or `initialize` create are public: two workspaces
    -- producing them must collide.
    let (auto, _) ← (isAutoDeclOrPrivate_Internal n).toIO coreCtx coreSt
    -- eager auxiliaries of a public root are public (`casesOn`, `injEq`, …); internal
    -- auxiliaries (`_proof_n`, `match_n`, `_sizeOf_n`, …) are scoped even under one
    let cls : NameClass :=
      if isPrivateName n || hasPl then .scoped
      else if roots.contains n then .pub
      else if auto then (if (underRoot || publicRootOf n) && !n.isInternal && !n.hasMacroScopes
        then .pubAux else .scoped)
      else .pub
    -- canonical instance names are written into the capsule (`genMarker`), so replay and
    -- export produce the same spelling
    let l := normName sess.mainModule n
    members := members.push { local_ := l, cls, info := canonLevelParams ci }
    memberRecs := memberRecs.push { name := n, local_ := l, cls := classNameOf cls, kind := kindOf ci
                                    stock := chosen[n]? }
  -- hygienic names: number them per group in creation order
  let mut hygCount : Std.HashMap Name Nat := {}
  for i in [0:members.size] do
    let l := members[i]!.local_
    if l.components.getLast? == some `_hyg then
      let k := hygCount.getD l 0
      hygCount := hygCount.insert l (k + 1)
      let l' := Name.mkNum l k
      members := members.set! i { members[i]! with local_ := l' }
      memberRecs := memberRecs.set! i { memberRecs[i]! with local_ := l' }
  -- local identities must be unique (they key metadata and in-memory references)
  let sortedLocals := (members.map (·.local_.toString)).qsort (· < ·)
  for i in [1:sortedLocals.size] do
    if sortedLocals[i]! == sortedLocals[i-1]! then
      diags := diags.push (mkDiag "unsupported" "identity-clash"
        s!"two members normalize to {sortedLocals[i]!}")
  let memberSet : Std.HashMap Name Name :=
    members.foldl (fun m x => m.insert x.info.name x.local_) {}
  let wireDep : String → Name → Option (String × Nat) := fun pid l => do
    let (d, ls) ← sess.pkgs[pid]?
    let i ← ls.idxOf? l
    pure (d, i)
  -- Resolve references.
  let rec resolve (fuel : Nat) (c : Name) : Except String Ref := do
    match fuel with
    | 0 => throw s!"reference depth exceeded at {c}"
    | fuel + 1 =>
    if let some l := memberSet[c]? then return .self l
    if let some (gid, l) := sess.index[c]? then return .dep gid l
    if (env.getModuleIdxFor? c).isSome then return .base c
    if isReservedName env c then
      match reservedBase env c with
      | some (b, s) => return .res (← resolve fuel b) s
      | none => throw s!"reserved name {c} has no resolvable base"
    if sess.scaffold.contains c then
      throw s!"reference to capsule scaffolding constant {c}"
    throw s!"unresolvable reference {c}"
  -- canonical member numbering (OPEN-22); metadata follows the same order
  members ← match canonicalOrder baseId members (resolve 64) wireDep with
    | .ok ms => pure ms
    | .error e => return (sess, fc, .failed (diags.push (mkDiag "reject" "encode" e)))
  let recOf : Std.HashMap Name MemberRec := memberRecs.foldl (fun m r => m.insert r.local_ r) {}
  memberRecs := members.map fun m => recOf.getD m.local_ default
  let wire := WireCtx.ofMembers members wireDep
  for i in [0:members.size] do
    let m := members[i]!
    if let .ok b := encodeGroup baseId #[m] (resolve 64) wire then
      memberRecs := memberRecs.set! i { memberRecs[i]! with hash := (groupIdOf b).take 12 |>.toString }
    let stmt : EncMember := { m with info := .axiomInfo {
      name := m.info.name, levelParams := m.info.levelParams, type := m.info.type, isUnsafe := false } }
    if let .ok b := encodeGroup baseId #[stmt] (resolve 64) wire then
      memberRecs := memberRecs.set! i { memberRecs[i]! with typeHash := groupIdOf b }
      if let some t := sess.targets.find? (·.name == m.info.name) then
        unless t.typeHash == groupIdOf b do
          diags := diags.push (mkDiag "reject" "changed-target"
            s!"{m.info.name} does not have the pinned statement {t.typeHash.take 12} (got {(groupIdOf b).take 12})")
  let encoded := encodeGroup baseId members (resolve 64) wire
  let bytes ← match encoded with
    | .ok b => pure b
    | .error e => return (sess, fc, .failed (diags.push (mkDiag "reject" "encode" e)))
  let declId := groupIdOf bytes
  -- Kernel dependencies.
  let mut deps : Array String := #[]
  let mut usedNames : NameSet := {}
  for m in members do
    for c in m.info.getUsedConstantsAsSet do
      usedNames := usedNames.insert c
      if let some (gid, _) := sess.index[c]? then
        unless deps.contains gid do deps := deps.push gid
  -- reserved names realized from groups: depend on the base group
  for c in usedNames.toArray do
    if !memberSet.contains c && !(sess.index.contains c) && isReservedName env c then
      if let some (b, _) := reservedBase env c then
        if let some (gid, _) := sess.index[(privateToUserName b)]? <|> sess.index[b]? then
          unless deps.contains gid do deps := deps.push gid
  -- Frontend dependencies: elaborators/macros/parsers used, attribute commands on deps.
  let feNames := frontendNames r.stx r.trees
  let impl := implementors r.envBefore feNames
  let mut feDeps : Array String := #[]
  for n in feNames.toArray ++ impl do
    if let some (gid, _) := sess.index[n]? then
      unless deps.contains gid || feDeps.contains gid do feDeps := feDeps.push gid
  -- constants named in the source (e.g. `simp [lemma]` with a defeq lemma) need not occur
  -- in the kernel term, but the capsule still needs them in scope
  for c in (referencedConsts r.trees).toArray do
    if memberSet.contains c then continue
    if let some (gid, _) := sess.index[c]? then
      unless deps.contains gid || feDeps.contains gid do feDeps := feDeps.push gid
  -- Tactics whose lemma use is not recorded (everything simp-/grind-like except the hooked
  -- `simp`/`simp_all`) may depend on any lemma the file registered in those sets.
  let kindStrs := (syntaxKinds r.stx).toArray.map (·.toString.toLower)
  let hooked := [``Lean.Parser.Tactic.simp, ``Lean.Parser.Tactic.simpAll].map (·.toString.toLower)
  let unobservedSimp := kindStrs.any fun k => (k.splitOn "simp").length > 1 && !hooked.contains k
  let usesGrind := kindStrs.any fun k => (k.splitOn "grind").length > 1
  if unobservedSimp then
    for g in fc.simpSetGroups do
      unless deps.contains g || feDeps.contains g do feDeps := feDeps.push g
  if usesGrind then
    -- grind's preprocessing also normalizes with simp-set lemmas
    for g in fc.grindSetGroups ++ fc.simpSetGroups do
      unless deps.contains g || feDeps.contains g do feDeps := feDeps.push g
  -- `set_option X`: the option is declared by a `register_option X` group (a constant
  -- named X) or, for trace classes and other initializer-registered options, by some
  -- initializer group
  for o in setOptionNames r.stx do
    if (r.envBefore.getModuleIdxFor? o).isSome then continue
    match sess.index[o]? with
    | some (gid, _) => unless deps.contains gid || feDeps.contains gid do feDeps := feDeps.push gid
    | none =>
      if (r.envBefore.find? o).isNone then
        for gid in sess.initGroups do
          unless deps.contains gid || feDeps.contains gid do feDeps := feDeps.push gid
  for c in usedNames.toArray ++ (referencedConsts r.trees).toArray do
    for gid in sess.effectTargets.getD c #[] do
      unless deps.contains gid || feDeps.contains gid do feDeps := feDeps.push gid
  -- Axioms (transitive, via the elaborated environment).
  -- Lean's `collectAxioms` follows original declaration kinds: in a `module`, imported
  -- theorems are axiom-shaped but carry precomputed axiom data.
  let mut axs : Array Name := #[]
  for m in members do
    let (a, _) ← (Lean.collectAxioms (m := CoreM) m.info.name).toIO coreCtx coreSt
    for x in a do unless axs.contains x do axs := axs.push x
  for a in axs do
    unless allowedAxioms.contains a || sess.remoteAxioms.contains a do
      diags := diags.push (mkDiag "reject" "axiom" s!"depends on disallowed axiom {a}")
  for m in members do
    if let .axiomInfo _ := m.info then
      diags := diags.push (mkDiag "reject" "new-axiom" s!"declares axiom {m.info.name}")
  for d in deps ++ feDeps do
    if sess.rejected.contains d then
      diags := diags.push (mkDiag "reject" "rejected-dep" s!"depends on rejected group {d.take 12}")
  -- Name literals that spell a module-private or hygienic name (`initialize` handlers,
  -- quotations of local syntax) make the body itself module-dependent.
  for m in members do
    let hit := (m.info.value?.getD (mkConst ``True)).find? fun e => match e with
      | .lit (.strVal s) => s == "_private" || s == "_@"
      | _ => false
    if hit.isSome then
      diags := diags.push (mkDiag "unsupported" "module-dependent-literal"
        s!"{m.info.name} embeds a module-private or hygienic name literal; its body depends on the module it is elaborated in")
  -- Capsule.
  let sr := renderScope sess r.scopeBefore
  diags := diags ++ sr.diags.map fun (d : Diag) => { d with file := fc.file, line }
  let publicNames := memberRecs.filterMap fun (m : MemberRec) => if m.cls == "pub" then some m.name else none
  let hasScopedKind := !(findNodes r.stx (·.getKind == ``Lean.Parser.Term.scoped)).isEmpty
  -- relocating a `scoped` command would scope it to the relocation namespace
  -- inside a `module`, private names are already module-keyed; segments of one file are
  -- joined with `import all`, so no relocation
  let relocate := isDecl && publicNames.isEmpty && !members.isEmpty && !hasScopedKind && !fc.isModule
  if isDecl && publicNames.isEmpty && hasScopedKind then
    diags := diags.push (mkDiag "info" "scoped-not-relocated"
      "scoped command with only generated names keeps its spelling (no relocation)")
  let mut text := text
  -- start of the declaration value (for the `remote%` header form)
  let valueKinds := [``Lean.Parser.Command.declValSimple, ``Lean.Parser.Command.declValEqns,
    ``Lean.Parser.Command.whereStructInst]
  let mut valueStart : Option Nat :=
    if kind == ``Lean.Parser.Command.declaration then
      (findNodes r.stx (fun s => valueKinds.contains s.getKind))[0]?.bind fun v =>
        v.getPos?.map (·.byteIdx - r.startPos)
    else none
  let anonInst := (findNodes r.stx (·.getKind == ``Lean.Parser.Command.instance)).any (·[3].isNone)
  if relocate || (anonInst && isDecl) then
    let mut edits : Array (Nat × Nat × String) := #[]
    if relocate then
      for p in findNodes r.stx (·.getKind == ``Lean.Parser.Command.private) do
        if let (some a, some z) := (p.getPos?, p.getTailPos?) then
          edits := edits.push (a.byteIdx - r.startPos, z.byteIdx - r.startPos, "")
    -- generated instance names depend on the module root and on which constants are
    -- module-local, so the capsule names the instance explicitly
    for inst in findNodes r.stx (·.getKind == ``Lean.Parser.Command.instance) do
      if inst[3].isNone then
        -- the instance is the member whose name no other member's name extends
        let rootsM := members.filter fun (m : EncMember) =>
          !members.any fun (o : EncMember) => o.info.name != m.info.name && o.info.name.isPrefixOf m.info.name
        -- attributes may derive further roots from it (e.g. `@[to_dual]`); the instance
        -- itself is the root created first
        let firstIdx (m : EncMember) := (r.newConsts.findIdx? (·.name == m.info.name)).getD 0
        let isInst (m : EncMember) := (Meta.instanceExtension.getState env).instanceNames.contains m.info.name
        let rootsM := ((rootsM.filter isInst).qsort fun a b => firstIdx a < firstIdx b).extract 0 1
        match rootsM.toList with
        | [m] =>
          let anchorTok := if inst[2].isNone then inst[1] else inst[2]
          if let some z := anchorTok.getTailPos? then
            let nm := Name.mkSimple m.info.name.getString!
            edits := edits.push (z.byteIdx - r.startPos, z.byteIdx - r.startPos, s!" {genMarker} {nameText nm}")
        | _ => diags := diags.push (mkDiag "unsupported" "anon-instance"
            "cannot identify the generated instance name to make it explicit")
    text := applyEdits text edits
    if let some v := valueStart then
      valueStart := some (edits.foldl (fun acc (a, z, rep) =>
        if a < v then acc + rep.utf8ByteSize - (z - a) else acc) v)
    let hasNonPrivRoot := roots.any fun n => !(memberRecs.any (fun (x : MemberRec) => x.name == mkPrivateNameCore sess.mainModule n))
    if roots.size > 0 && hasNonPrivRoot && !(findNodes r.stx (·.getKind == ``Lean.Parser.Command.private)).isEmpty then
      diags := diags.push (mkDiag "unsupported" "mixed-visibility" "command mixes private and public declarations")
  let capsule : Capsule := {
    workspace := fc.workspace, file := fc.file, module := fc.module
    startLine := line, endLine, imports := fc.imports
    noncomputable_ := r.scopeBefore.isNoncomputable
    sectionHeader := sectionHeaderOf r.scopeBefore
    isModule := fc.isModule, importSpecs := fc.importSpecs
    currNamespace := r.scopeBefore.currNamespace
    opens := sr.opens, scopeCmds := sr.scopeCmds
    localEffects := fc.localEffects.map (fun (x : Nat × String) => x.2)
    text, relocate, valueStart }
  let pid := pidOverride?.getD (packageId declId capsule feDeps)
  let short := (pid.take 8).toString
  let anchor := if publicNames.isEmpty then
      some (capsule.currNamespace ++ Name.mkSimple s!"_pl_{short}") else none
  let isEffect := members.isEmpty || !isDecl
  let g : GroupRec := {
    gid := pid, declId, kind := if isEffect then "effect" else "decl", cmdKind := kind
    members := memberRecs, realized, deps, feDeps, feDepsConservative := fc.effectGroups
    publicNames, anchor, touched := r.touched.filter fun (n, _) => !isNoiseExt n
    axioms := axs, capsule, diags, encSize := bytes.size }
  -- Update the index.
  let mut index := sess.index
  for (m : MemberRec) in memberRecs do index := index.insert m.name (pid, m.local_)
  let pkgs := sess.pkgs.insert pid (declId, memberRecs.map (·.local_))
  let mut effectTargets := sess.effectTargets
  -- attribute-like commands target constants; an effect group with members (notation,
  -- `compile_inductive%`, …) targets only workspace constants, not the base it mentions
  if members.isEmpty || isEffect then
    for c in referencedConsts r.trees do
      if !members.isEmpty && !sess.index.contains c then continue
      effectTargets := effectTargets.insert c ((effectTargets.getD c #[]).push pid)
  let fc := if isEffect && !hasLocalAttrKind r.stx then { fc with effectGroups := fc.effectGroups.push pid } else fc
  let touchedNames := r.touched.map (·.1.toString)
  let fc := if touchedNames.any (· == "Lean.Meta.simpExtension") then
      { fc with simpSetGroups := fc.simpSetGroups.push pid } else fc
  let fc := if touchedNames.any (·.startsWith "Lean.Meta.Grind.") then
      { fc with grindSetGroups := fc.grindSetGroups.push pid } else fc
  let rejected := if diags.any (·.severity == "reject") then sess.rejected.insert pid else sess.rejected
  let initGroups := if r.touched.any (fun (n, _) => n == `Lean.regularInitAttr || n == `Lean.builtinInitAttr)
    then sess.initGroups.push pid else sess.initGroups
  return ({ sess with index, pkgs, effectTargets, rejected, initGroups }, fc, .group g bytes)

end Paralean
