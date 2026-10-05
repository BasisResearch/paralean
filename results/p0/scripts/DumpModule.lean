import Lean
/-! Import one module at private level and dump its own constants:
`name kind hash(type) hash(value)`. Run under `lake env` of the tree to inspect.
Diff two dumps to compare two builds of the same module semantically. -/
open Lean

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def main (args : List String) : IO UInt32 := do
  let [m] := args | return 2
  initSearchPath (← findSysroot)
  let mod := m.toName
  let env ← importModules #[{ module := mod }] {} (level := .private)
  let some idx := env.getModuleIdx? mod | return 3
  let rows := env.header.moduleData[idx.toNat]!.constants.map fun c =>
    s!"{c.name} {kindOf c} {c.type.hash} {(c.value? (allowOpaque := true)).map (·.hash) |>.getD 0}"
  for l in rows.qsort (· < ·) do IO.println l
  return 0
