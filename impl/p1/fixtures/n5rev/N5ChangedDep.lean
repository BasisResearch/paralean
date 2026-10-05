-- N5 upstream revision: `value` changes from 0 to 1; the old proof must not survive.
def N5.value : Nat := 1
theorem N5.value_zero : N5.value = 0 := rfl
