-- N5: must be rejected when replayed against the *new* upstream revision
--   `def N5.value : Nat := 1` (pinned dependency revision was `:= 0`).
def N5.value : Nat := 0
theorem N5.value_zero : N5.value = 0 := rfl
