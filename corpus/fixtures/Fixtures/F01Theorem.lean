/-! F01: theorems, including ones whose proofs create `proof_n` auxiliaries. -/
namespace F01

theorem two_eq : 1 + 1 = 2 := rfl

theorem le_succ_self (n : Nat) : n ≤ n + 1 := Nat.le_succ n

theorem small : 10 < 20 ∧ 3 ≠ 4 := by
  constructor <;> decide

/-- A proof inside a definition body becomes the auxiliary `bounded.proof_1`. -/
def bounded : {n : Nat // n < 10} := ⟨3, by decide⟩

theorem bounded_val : bounded.val = 3 := rfl

theorem uses_small : 3 ≠ 4 := small.2

end F01
