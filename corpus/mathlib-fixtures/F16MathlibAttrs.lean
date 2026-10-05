import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Simps.Basic
import Mathlib.Data.Nat.Factorial.Basic
/-! F16: attribute-generated declarations (`@[to_additive]`, `@[simps]`) and Mathlib
scoped notation. An attribute that calls `addDecl` puts its outputs in the group of
the command carrying the attribute. -/

namespace F16

@[to_additive /-- additive twin -/]
theorem mul_one_one {M : Type*} [MulOneClass M] (a : M) : a * 1 * 1 = a := by
  rw [mul_one, mul_one]

structure Pair where
  fst : Nat
  snd : Nat

@[simps] def swap (p : Pair) : Pair := ⟨p.snd, p.fst⟩

theorem swap_swap (p : Pair) : swap (swap p) = p := by cases p; rfl

theorem swap_fst_eq (p : Pair) : (swap p).fst = p.snd := by simp

open Nat in
theorem fact_three : 3 ! = 6 := rfl

end F16
