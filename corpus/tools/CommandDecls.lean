import Lean

/-!
Reference oracle for P1 command-granularity capture (P0 corpus).

Elaborates one Lean file command by command with stock Lean, synchronously, and
prints one JSON object per command: the constants it added (with a name class)
and the persistent environment extensions whose exported entries changed.
This is the expected group membership a capture implementation must reproduce.
It is not the capture implementation.

Usage: lean --run CommandDecls.lean <file.lean> <MainModuleName>
(run under `lake env` when the file imports Mathlib).
-/

open Lean Elab Frontend

namespace Paralean.Corpus

/-- Name class as defined in docs/p0-interfaces.md §Names. -/
def classify (env : Environment) (n : Name) : CoreM String := do
  if isReservedName env n then return "reserved"
  if isPrivateName n then return "scoped-private"
  if (← isAutoDeclOrPrivate_Internal n) then return "scoped-generated"
  return "public"

def constKind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def localConsts (env : Environment) : NameSet :=
  env.toKernelEnv.constants.foldStage2 (fun s n _ => s.insert n) {}

/-- Per-extension count of private-level exported entries. -/
def extCounts (env : Environment) : IO (Std.HashMap Name Nat) := do
  let pExts ← persistentEnvExtensionsRef.get
  let mut m := {}
  for pExt in pExts do
    let state := pExt.getState (asyncMode := .sync) env
    let n := (pExt.exportEntriesFn env state).private.size
    if n > 0 then m := m.insert pExt.name n
  return m

def jstr (s : String) : String := (Json.str s).compress

unsafe def main (args : List String) : IO UInt32 := do
  let [file, modName] := args | IO.eprintln "usage: CommandDecls <file> <Module>"; return 2
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let opts := Elab.async.set {} false
  let mainModule := modName.toName
  let (env, messages) ← processHeader header opts messages inputCtx (mainModule := mainModule)
  let env := env.setMainModule mainModule
  let cmdState := Command.mkState env messages opts
  let fm := inputCtx.fileMap
  let rec loop (fuel : Nat) (idx : Nat) (prevConsts : NameSet)
      (prevExt : Std.HashMap Name Nat) (errs : Nat) : FrontendM (Nat × Nat) := do
    match fuel with
    | 0 => return (idx, errs)
    | fuel + 1 =>
      let before := (← get).commandState.messages.toList.length
      let done ← processCommand
      let st ← get
      let env := st.commandState.env
      let cmd := st.commands.back!
      let consts := localConsts env
      let added := consts.toList.filter (!prevConsts.contains ·)
      let ext ← extCounts env
      let mut extDelta : Array String := #[]
      for (k, v) in ext.toList do
        let old := prevExt.getD k 0
        if v != old then extDelta := extDelta.push s!"{jstr k.toString}:{(v : Int) - old}"
      let newMsgs := st.commandState.messages.toList.drop before
      let newErrs := (newMsgs.filter (·.severity == .error)).length
      let coreCtx : Core.Context := { fileName := file, fileMap := fm, options := opts }
      let mut items : Array String := #[]
      for n in added.toArray.qsort Name.lt do
        let (cls, _) ← (classify env n).toIO coreCtx { env }
        let kind := (env.find? n).map constKind |>.getD "?"
        items := items.push s!"\{\"name\":{jstr n.toString},\"class\":{jstr cls},\"kind\":{jstr kind}}"
      let line := (fm.toPosition (cmd.getPos?.getD 0)).line
      let bytes := match cmd.getRange? with
        | some r => r.stop.byteIdx - r.start.byteIdx
        | none => 0
      unless cmd.getKind == ``Parser.Command.eoi do
        IO.println s!"\{\"cmd\":{idx},\"line\":{line},\"bytes\":{bytes},\"syntax\":{jstr cmd.getKind.toString},\"errors\":{newErrs},\"added\":[{",".intercalate items.toList}],\"ext\":\{{",".intercalate extDelta.toList}}}"
      if done then return (idx, errs + newErrs)
      loop fuel (idx + 1) consts ext (errs + newErrs)
  let env0 := cmdState.env
  let ((n, errs), st) ← (loop 100000 0 (localConsts env0) (← extCounts env0) 0 { inputCtx }).run
    { commandState := cmdState, parserState, cmdPos := parserState.pos }
  for m in st.commandState.messages.toList do
    if m.severity == .error then IO.eprintln (← m.toString)
  IO.eprintln s!"commands={n} errors={errs}"
  return if errs == 0 then 0 else 1

end Paralean.Corpus

unsafe def main (args : List String) : IO UInt32 := Paralean.Corpus.main args
