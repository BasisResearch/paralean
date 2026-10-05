/-! G4 source/line mapping probe: accepted declarations that make stock Lean report
diagnostics (linter and deprecation warnings) at known lines, spread over namespaces,
a section with a variable, a multi-line command and an anonymous instance. -/
namespace DiagMap

def old (n : Nat) : Nat := n + 1

@[deprecated old (since := "2026-01-01")]
def older (n : Nat) : Nat := old n

theorem uses_older (n : Nat) : older n = n + 1 := rfl

def unusedArg (n : Nat) (m : Nat) : Nat :=
  n + 1

section
variable (k : Nat)

theorem multi_line (a b : Nat)
    (h : a = b) :
    older a = older b := by
  rw [h]

end

class Pointed (α : Type) where
  pt : α

instance : Pointed Nat := ⟨older 0⟩

end DiagMap
