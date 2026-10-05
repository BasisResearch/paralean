/-! F11a: scoped and local notation, scoped instances, scoped simp. -/
namespace F11

def star (a b : Nat) : Nat := a * b + 1

scoped infixl:70 " ⋆ " => star

scoped notation "‖" a "‖" => a + 0

local notation "twice" x => x + x

theorem star_def (a b : Nat) : a ⋆ b = a * b + 1 := rfl

theorem twice_eq (x : Nat) : (twice x) = 2 * x := by omega

class Pointed (α : Type) where
  pt : α

scoped instance : Pointed Nat := ⟨42⟩

end F11
