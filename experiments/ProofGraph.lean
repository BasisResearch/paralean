import Std

/-! A finite model of proof status. Edges represent already checked conditional
proofs. This file does not check terms, persist data, or implement networking. -/

namespace Paralean.Experiment

structure Edge where
  revision : Nat
  parent : Nat
  children : List Nat
  deriving Repr

/-- Start from no proved goals. An edge fires only after all its children do.
Every productive pass adds at least one goal; there are at most `edges.length`
distinct parents. Cycles without a grounded proof never enter the result. -/
def proved (revision : Nat) (edges : List Edge) : List Nat := Id.run do
  let edges := edges.filter (·.revision == revision)
  let mut known : List Nat := []
  for _ in [:edges.length] do
    for edge in edges do
      if edge.children.all known.contains && !known.contains edge.parent then
        known := edge.parent :: known
  return known.mergeSort (· ≤ ·)

def assertGoals (label : String) (actual expected : List Nat) : IO Unit := do
  if actual != expected then
    throw <| IO.userError s!"FAIL: {label}: got {actual}, expected {expected}"
  IO.println s!"PASS: {label}"

def graphExperiments : IO Unit := do
  let circular := [Edge.mk 0 1 [2], Edge.mk 0 2 [1]]
  assertGoals "mutual justification proves nothing" (proved 0 circular) []
  assertGoals "self justification proves nothing" (proved 0 [⟨0, 1, [1]⟩]) []
  let grounded := circular ++ [⟨0, 2, []⟩]
  assertGoals "alternative proof grounds a cycle" (proved 0 grounded) [1, 2]
  let awaiting := [Edge.mk 0 3 [1, 2], Edge.mk 0 1 []]
  assertGoals "AND waits for every child" (proved 0 awaiting) [1]
  let complete := awaiting ++ [⟨0, 2, []⟩]
  assertGoals "AND closes with all witnesses" (proved 0 complete) [1, 2, 3]
  assertGoals "reordering messages preserves status"
    (proved 0 complete.reverse) (proved 0 complete)
  assertGoals "duplicate messages preserve status"
    (proved 0 (complete ++ complete)) (proved 0 complete)
  assertGoals "old evidence cannot close a new revision"
    (proved 1 (complete ++ [⟨1, 3, [1, 2]⟩])) []
  assertGoals "new evidence closes only its own revision"
    (proved 1 (complete ++ [⟨1, 3, [1, 2]⟩, ⟨1, 1, []⟩, ⟨1, 2, []⟩])) [1, 2, 3]

end Paralean.Experiment

def main : IO Unit := Paralean.Experiment.graphExperiments
