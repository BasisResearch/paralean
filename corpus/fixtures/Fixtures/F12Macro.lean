import Lean
/-! F12: `macro`, `syntax` + `macro_rules`, `elab`, and a declared tactic. Generated
parser/macro constants carry macro scopes or `_aux` names. -/
open Lean Elab Term Meta

namespace F12

macro "dbl!" x:term : term => `($x + $x)

syntax "sq!" term : term
macro_rules
  | `(sq! $x) => `($x * $x)

elab "nat_lit_count!" : term => return mkNatLit 3

syntax "triv_tac" : tactic
macro_rules
  | `(tactic| triv_tac) => `(tactic| first | rfl | decide)

theorem dbl_two : (dbl! 2) = 4 := rfl
theorem sq_three : (sq! 3) = 9 := rfl
theorem count_eq : (nat_lit_count! : Nat) = 3 := rfl
theorem triv_ok : 2 + 2 = 4 := by triv_tac

end F12
