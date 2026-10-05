import Fixtures.F11ScopedDecl
/-! F11b: consumers that must see scoped state only after `open`. -/

open F11 in
theorem F11.use_star : 2 ⋆ 3 = 7 := rfl

section
open scoped F11
theorem F11.use_norm : ‖(5 : Nat)‖ = 5 := rfl
theorem F11.use_pt : (F11.Pointed.pt : Nat) = 42 := rfl
end
