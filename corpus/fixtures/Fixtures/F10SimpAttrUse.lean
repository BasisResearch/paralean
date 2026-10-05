import Fixtures.F10SimpAttrDecl
/-! F10b: tagging with a custom simp set, `@[simp]`, and `attribute [-simp]`. -/
namespace F10

def triple (n : Nat) : Nat := 3 * n

@[f10_simps] theorem triple_def (n : Nat) : triple n = 3 * n := rfl

@[simp] theorem triple_zero : triple 0 = 0 := rfl

theorem triple_one : triple 1 = 3 := by simp only [f10_simps]

theorem triple_zero' : triple 0 = 0 := by simp

end F10
