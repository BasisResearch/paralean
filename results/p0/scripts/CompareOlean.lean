import Lean
/-! Compare two .olean(.private) files constant by constant (names, kinds, types, values). -/
open Lean

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

unsafe def main (args : List String) : IO UInt32 := do
  let [a, b] := args | return 2
  let (ma, ra) ← readModuleData a
  let (mb, rb) ← readModuleData b
  let toMap (m : ModuleData) : Std.HashMap Name ConstantInfo :=
    m.constants.foldl (fun s c => s.insert c.name c) {}
  let A := toMap ma; let B := toMap mb
  let onlyA := A.toList.filter (fun (n, _) => !B.contains n) |>.map (·.1)
  let onlyB := B.toList.filter (fun (n, _) => !A.contains n) |>.map (·.1)
  let mut tyDiff := #[]; let mut valDiff := #[]
  for (n, ca) in A.toList do
    if let some cb := B[n]? then
      if ca.type != cb.type then tyDiff := tyDiff.push n
      else if ca.value? (allowOpaque := true) != cb.value? (allowOpaque := true) then valDiff := valDiff.push (n, kindOf ca)
  IO.println s!"constants A={A.size} B={B.size} onlyA={onlyA.length} onlyB={onlyB.length} typeDiff={tyDiff.size} valueDiff={valDiff.size}"
  IO.println s!"  onlyA: {onlyA.take 6}"
  IO.println s!"  onlyB: {onlyB.take 6}"
  IO.println s!"  typeDiff: {tyDiff.toList.take 6}"
  IO.println s!"  valueDiff: {valDiff.toList.take 8}"
  let ea := ma.entries.map (·.1); let eb := mb.entries.map (·.1)
  let mut extDiff := #[]
  for (n, xs) in ma.entries do
    let ys := (mb.entries.find? (·.1 == n)).map (·.2.size) |>.getD 0
    if xs.size != ys then extDiff := extDiff.push (n, xs.size, ys)
  IO.println s!"  ext entry-count diffs: {extDiff.toList.take 8} (extsA={ea.size} extsB={eb.size})"
  ra.free; rb.free
  return 0
