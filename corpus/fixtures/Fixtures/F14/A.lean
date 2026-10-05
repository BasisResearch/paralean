import Fixtures.F14.B1
/-! F14 expected export, file 2 of 3: A's group, depending on B's `helper_b`. -/
namespace Cross

@[simp] theorem helper (n : Nat) : helper_b n = n + 1 := rfl

end Cross
