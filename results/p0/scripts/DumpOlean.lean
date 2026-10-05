import Lean
/-! Dump one .olean part: per constant `name kind hash(type) hash(value)`, then per-extension
entry counts. Diff two dumps to compare builds semantically. -/
open Lean

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

unsafe def main (args : List String) : IO UInt32 := do
  let [a] := args | return 2
  let (m, r) ← readModuleData a
  let rows := m.constants.map fun c =>
    s!"C {c.name} {kindOf c} {c.type.hash} {(c.value? (allowOpaque := true)).map (·.hash) |>.getD 0}"
  for l in rows.qsort (· < ·) do IO.println l
  for (n, xs) in m.entries.qsort (fun a b => a.1.lt b.1) do IO.println s!"E {n} {xs.size}"
  r.free
  return 0
