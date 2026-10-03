import Lean

open Lean

/-! Executable design experiments. This is not the production admission service. -/

namespace Paralean.Experiment

def addChecked (env : Kernel.Environment) (decl : Declaration) :
    Except Kernel.Exception Kernel.Environment :=
  env.addDeclCore 1000000 10000 decl none

def valueDecl (n : Nat) : Declaration := .defnDecl {
  name := `sharedValue
  levelParams := []
  type := mkConst ``Nat
  value := mkNatLit n
  hints := .abbrev
  safety := .safe
}

def targetType : Expr :=
  mkApp3 (mkConst ``Eq [Level.succ Level.zero])
    (mkConst ``Nat) (mkConst `sharedValue) (mkNatLit 0)

def proofDecl : Declaration := .thmDecl {
  name := `sharedValue_zero
  levelParams := []
  type := targetType
  value := mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero])
    (mkConst ``Nat) (mkConst `sharedValue)
}

def requireOk (label : String) (result : Except Kernel.Exception α) : IO α := do
  match result with
  | .ok value => pure value
  | .error _ => throw <| IO.userError s!"FAIL: {label}"

def requireError (label : String) (result : Except Kernel.Exception α) : IO Unit := do
  match result with
  | .ok _ => throw <| IO.userError s!"FAIL: {label} unexpectedly accepted"
  | .error _ => IO.println s!"PASS: {label}"

/-- A decomposition is an ordinary theorem with explicit proof parameters. -/
theorem compose (P Q : Prop) (step : P → Q) (child : P) : Q := step child

/-- A closed result applies a decomposition to closed witnesses. -/
theorem closed : 0 = 0 :=
  compose True (0 = 0) (fun _ => rfl) True.intro

#print axioms compose
#print axioms closed

def kernelExperiments (sysroot : System.FilePath) : IO Unit := do
  initSearchPath sysroot
  let base := (← importModules #[{ module := `Init }] {}).toKernelEnv
  let oldEnv ← requireOk "old definition" (addChecked base (valueDecl 0))
  let newEnv ← requireOk "new definition" (addChecked base (valueDecl 1))
  let _ ← requireOk "original proof" (addChecked oldEnv proofDecl)
  IO.println "PASS: original proof accepted"
  requireError "same signature, changed body invalidates proof" (addChecked newEnv proofDecl)
  let _ ← requireOk "old snapshot survives" (addChecked oldEnv proofDecl)
  IO.println "PASS: old snapshot remains valid"

  -- A well-typed result can still solve a different task. Check the pinned target.
  let wrongStatement : Declaration := .thmDecl {
    name := `sharedValue_zero
    levelParams := []
    type := mkConst ``True
    value := mkConst ``True.intro
  }
  let _ ← requireOk "different statement" (addChecked oldEnv wrongStatement)
  if targetType == mkConst ``True then
    throw <| IO.userError "FAIL: target comparison"
  IO.println "PASS: kernel acceptance alone does not enforce the target"

  -- The kernel permits axioms. Admission needs a separate axiom policy.
  let withAxiom ← requireOk "axiom declaration" (addChecked base (.axiomDecl {
    name := `unapprovedAxiom
    levelParams := []
    type := mkConst ``False
    isUnsafe := false
  }))
  let _ ← requireOk "axiom-backed proof" (addChecked withAxiom (.thmDecl {
    name := `badConclusion
    levelParams := []
    type := mkConst ``False
    value := mkConst `unapprovedAxiom
  }))
  IO.println "PASS: axiom policy is required in addition to kernel checking"

end Paralean.Experiment

def main (args : List String) : IO Unit := do
  let [sysroot] := args
    | throw <| IO.userError "usage: lean --run experiments/KernelBoundary.lean <lean --print-prefix>"
  Paralean.Experiment.kernelExperiments sysroot
