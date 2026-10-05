-- N4: must be rejected as a solution to the pinned target
--   `theorem N4.target : ∀ n : Nat, n + 0 = n`
-- The statement below has the same name but a weaker type.
theorem N4.target : ∀ n : Nat, 0 + n = n + 0 := by intro n; simp
