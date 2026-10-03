import Paralean
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let prefixes := #[`ParaleanRegistry, `Durability, `ParaleanConvergence, `ParaleanComposition]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (·.isPrefixOf name) then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      count := count + 1
  unless count > 0 do
    throwError "Axiom audit found no project declarations"
  logInfo m!"PASS: {count} project declarations use only the permitted stock Lean axioms"
