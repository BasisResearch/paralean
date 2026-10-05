import Fixtures.F14.A
/-! F14 expected export, file 3 of 3: B's second group, depending on A's `helper`. -/
namespace Cross

theorem helper_c (n : Nat) : helper_b (helper_b n) = n + 2 := by
  rw [helper n]; rfl

end Cross
