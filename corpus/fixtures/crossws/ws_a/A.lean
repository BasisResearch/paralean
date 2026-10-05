-- Workspace A (agent view). Requires B's published `Cross.helper_b`.
namespace Cross

@[simp] theorem helper (n : Nat) : helper_b n = n + 1 := rfl

end Cross
