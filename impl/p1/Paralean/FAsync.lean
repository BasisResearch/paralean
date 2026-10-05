import Lean
import Paralean.Replay

/-!
F-async soundness experiment (`impl/p1/fixtures/fasync/FAsync.lean`).

* `observe`: elaborate the fixture command by command with the stock frontend under a
  given `Elab.async` setting and record what the environment exposes for the bad theorems
  right after each command returns, and at the end of the file.
* `forge`: act as a dishonest worker that reports success. Publish groups built from the
  terms the worker had (the ill-typed term the tactic assigned; the error-recovered
  terms), with their capsules. Then run the validator (source replay + kernel replay +
  axiom audit) without consulting any worker signal.
-/

namespace Paralean.FAsync
open Lean Elab

def watched : List Name := [`FA.kernelBad, `FA.usesKernelBad, `FA.lateBad, `FA.usesLateBad, `FA.fine]

def kindStr : ConstantKind → String
  | .defn => "def" | .thm => "theorem" | .axiom => "axiom" | .opaque => "opaque"
  | .quot => "quot" | .induct => "inductive" | .ctor => "ctor" | .recursor => "rec"

/-- Elaborate with the given async setting; return a report and the final environment. -/
unsafe def observe (path : System.FilePath) (async : Bool) : IO (Array String × Environment) := do
  enableInitializersExecution
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let opts := Elab.async.set {} async
  let (env, messages) ← processHeader header opts messages inputCtx (mainModule := `FAsync)
  let st := Command.mkState env messages opts
  let out ← IO.mkRef (#[] : Array String)
  let st ← runCommands st inputCtx parserState fun r => do
    let line := (inputCtx.fileMap.toPosition ⟨r.startPos⟩).line
    let errs := r.msgs.filter (·.severity == .error)
    let mut seen := #[]
    for n in watched do
      if let some c := r.envAfter.findAsync? n then
        unless (r.envBefore.findAsync? n).isSome do
          seen := seen.push s!"{n}:{kindStr c.kind}"
    if !seen.isEmpty || !errs.isEmpty then
      out.modify (·.push s!"  L{line} {r.stx.getKind.getString!}: new visible {seen}, \
        errors reported when the command returned: {errs.size}")
    return none
  -- after the file: wait for every pending task, then inspect the final kinds
  let env := st.env
  let _ := env.checked.get
  let mut fin := #[]
  for n in watched do
    match env.find? n with
    | some ci =>
      let ctx : Core.Context := { fileName := "<fasync>", fileMap := default }
      let (axs, _) ← (Lean.collectAxioms (m := CoreM) n).toIO ctx { env }
      fin := fin.push s!"  final {n}: {kindOf ci}, axioms {axs}"
    | none => fin := fin.push s!"  final {n}: absent"
  let allMsgs := st.messages.toList.filter (·.severity == .error)
  let _ := allMsgs
  return ((← out.get) ++ fin, env)

/-- Build and publish forged groups from the terms the worker had, then validate. -/
unsafe def forge (path : System.FilePath) (storeDir : System.FilePath) : IO (Array String) := do
  let (_, env) ← observe path false
  let store : Store := { root := storeDir }
  if ← storeDir.pathExists then IO.FS.removeDirAll storeDir
  store.init
  let input ← IO.FS.readFile path
  let elabCmd := "open Lean Elab Tactic in\nelab \"cheat_close\" : tactic => do\n  (← getMainGoal).assign (mkConst ``True.intro)"
  let ty (n : Name) := (env.find? n).map (·.type) |>.getD (mkConst ``True)
  -- (name, claimed value, capsule text, local effects)
  let specs : List (Name × Expr × String × Array String) := [
    (`FA.kernelBad, mkConst ``True.intro, "theorem FA.kernelBad : 1 = 2 := by cheat_close", #[elabCmd]),
    (`FA.usesKernelBad, mkApp4 (mkConst ``Eq.symm [1]) (mkConst ``Nat) (ty `FA.kernelBad).appFn!.appArg!
        (ty `FA.kernelBad).appArg! (mkConst `FA.kernelBad),
      "theorem FA.usesKernelBad : 2 = 1 := FA.kernelBad.symm", #[]),
    -- the error-recovered term the elaborator produced: well-typed, uses `sorryAx`
    (`FA.lateBad, mkApp2 (mkConst ``sorryAx [0]) (ty `FA.lateBad) (mkConst ``Bool.true),
      "theorem FA.lateBad : 1 = 2 := by\n  have _h : True := trivial\n  simp", #[]),
    (`FA.usesLateBad, mkApp4 (mkConst ``Eq.symm [1]) (mkConst ``Nat) (ty `FA.lateBad).appFn!.appArg!
        (ty `FA.lateBad).appArg! (mkConst `FA.lateBad), "theorem FA.usesLateBad : 2 = 1 := FA.lateBad.symm", #[])]
  let mut pids : Std.HashMap Name String := {}
  let mut gids := #[]
  let mut report := #[]
  for (n, v, text, effs) in specs do
    let ci : ConstantInfo := .thmInfo { name := n, levelParams := [], type := ty n, value := v, all := [n] }
    let resolve (c : Name) : Except String Ref :=
      if c == n then .ok (.self c)
      else match pids[c]? with
        | some p => .ok (.dep p c)
        | none => .ok (.base c)
    let some bytes := (encodeGroup baseId #[{ local_ := n, cls := .pub, info := ci }] resolve).toOption
      | throw <| IO.userError "forge: encode failed"
    let declId ← store.putObject bytes
    let deps := (ci.getUsedConstantsAsSet.toArray.filterMap pids.get?)
    let capsule : Capsule := {
      workspace := "worker", file := "FAsync.lean", module := `FAsync, startLine := 0, endLine := 0
      imports := #[`Lean], noncomputable_ := false, currNamespace := .anonymous, opens := #[]
      scopeCmds := #[], localEffects := effs, text, relocate := false }
    let pid := packageId declId capsule #[]
    let g : GroupRec := {
      gid := pid, declId, kind := "decl", cmdKind := `Lean.Parser.Command.declaration
      members := #[{ name := n, local_ := n, cls := "pub", kind := "theorem" }], realized := #[]
      deps, feDeps := #[], feDepsConservative := #[], publicNames := #[n], anchor := none
      touched := #[], axioms := #[], capsule, diags := #[], encSize := bytes.size }
    store.putMeta g
    pids := pids.insert n pid
    gids := gids.push pid
  let _ := input
  let _ ← store.putFileRec {
    workspace := "worker", file := "FAsync.lean", module := `FAsync, imports := #[`Lean]
    groups := gids, skipped := #[], diags := #[], prelude := #[] }
  -- The validator: no worker signal is consulted.
  let cat ← Catalog.load store (← store.currentFiles)
  let sr ← sourceReplay cat cat.order #[`Lean]
  let (kr, _) ← kernelReplay store cat cat.order sr
  for gid in cat.order do
    let g := cat.get! gid
    let s := sr.results.find? (·.gid == gid)
    let k := kr.find? (·.gid == gid)
    report := report.push s!"  {g.publicNames}: source replay {if s.any (·.ok) then "ACCEPTS" else "rejects"}, \
      kernel+axiom validator {if k.any (·.ok) then "ACCEPTS" else "rejects"}"
    for d in (s.map (·.diags)).getD #[] ++ (k.map (·.diags)).getD #[] do
      report := report.push s!"      {d.code}: {(d.msg.take 140).toString}"
  return report

end Paralean.FAsync
