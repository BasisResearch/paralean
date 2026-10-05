namespace P
notation "⟪" x "⟫" => x + 1
scoped notation "⟪⟪" x "⟫⟫" => x + 2
macro "twice!" x:term : term => `($x + $x)
syntax "thrice!" term : term
macro_rules | `(thrice! $x) => `($x + $x + $x)
instance : Inhabited (Nat × Nat) := ⟨(0, 0)⟩
initialize counter : IO.Ref Nat ← IO.mkRef 0
attribute [simp] Nat.add_comm
theorem t : ⟪1⟫ = 2 := rfl
example : twice! 1 = 2 := rfl
open Nat in
theorem t2 : succ 0 = 1 := rfl
end P
