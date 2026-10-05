-- Workspace B (agent view). `helper_c` is written after A publishes `helper`.
namespace Cross

def helper_b (n : Nat) : Nat := n + 1

-- requires A's published `Cross.helper`
theorem helper_c (n : Nat) : helper_b (helper_b n) = n + 2 := by
  rw [helper n]; rfl

end Cross
