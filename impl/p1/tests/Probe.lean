import Lean
open Lean Elab Frontend

unsafe def main (args : List String) : IO Unit := do
  let [sysroot, file] := args | throw <| IO.userError "usage"
  initSearchPath sysroot
  enableInitializersExecution
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  let env := env.setMainModule `Probe1
  let opts := Elab.async.set {} false
  let cmdState := Command.mkState env messages opts
  let pExts ← persistentEnvExtensionsRef.get
  let rec loop (fuel : Nat) : FrontendM Unit := do
    match fuel with
    | 0 => pure ()
    | fuel+1 =>
    let before := (← getCommandState).env
    let stBefore := pExts.map fun e => ptrAddrUnsafe (e.getState before)
    let done ← processCommand
    let after := (← getCommandState).env
    let stx := (← get).commands.back!
    let bl ← before.getLocalConstantInfos
    let bset : NameSet := bl.foldl (fun s c => s.insert c.name) {}
    let al ← after.getLocalConstantInfos
    let new := (al.filter fun c => !bset.contains c.name).toList.map fun c => (c.name, c.toConstantInfo)
    let touched := (pExts.zip stBefore).filterMap fun (e, p) =>
      if ptrAddrUnsafe (e.getState after) != p then
        let n0 := (e.exportEntriesFn before (e.getState before)).private.size
        let n1 := (e.exportEntriesFn after (e.getState after)).private.size
        if n0 != n1 then some (e.name, n1 - n0) else none
      else none
    IO.println s!"== {stx.getKind} new={new.length} touched={touched.toList}"
    for (n, ci) in new do
      IO.println s!"   {n} kind={ci.isTheorem}/{ci.isDefinition}/{ci.isInductive} reserved={isReservedName after n} private={isPrivateName n} internal={n.isInternal} impl={n.isImplementationDetail}"
    unless done do loop fuel
  let (_, s) ← (loop 1000 { inputCtx }).run { commandState := cmdState, parserState, cmdPos := parserState.pos }
  let env := s.commandState.env
  IO.println s!"value? {env.contains `Probe.value} fib? {env.contains `Probe.fib} foo_nat? {env.contains `Probe.foo_nat}"
  IO.println s!"map2: {env.constants.map₂.toList.map (·.1)}"
  IO.println s!"local: {(← env.getLocalConstantInfos).map (·.name)}"
  IO.println s!"nmsgs {s.commandState.messages.toList.length} hasErr {s.commandState.messages.hasErrors}"
  for m in s.commandState.messages.toList do
    IO.println s!"MSG: {← m.toString}"
