import Lean
open Lean Elab Frontend

unsafe def main (args : List String) : IO Unit := do
  let [sysroot, file] := args | throw <| IO.userError "usage"
  initSearchPath sysroot
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  let env := env.setMainModule `Probe1
  let opts := Elab.async.set {} false
  let cmdState := Command.mkState env messages opts
  let st ← IO.processCommandsIncrementally inputCtx parserState cmdState none
  let env := st.commandState.env
  IO.println s!"value? {env.contains `Probe.value} fib? {env.contains `Probe.fib} foo_nat? {env.contains `Probe.foo_nat}"
  IO.println s!"local: {(← env.getLocalConstantInfos).map (·.name)}"
  for m in st.commandState.messages.toList do
    IO.println s!"MSG: {← m.toString}"
