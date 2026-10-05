import Lean
/-! F-async: false proofs that fail only in the kernel or in a late tactic, each followed
by a declaration in the same file that uses it. -/
open Lean Elab Tactic

/-- Closes any goal with `True.intro`. The elaborator does not type-check metavariable
assignments, so the ill-typed proof is caught only by the kernel. -/
elab "cheat_close" : tactic => do
  (← getMainGoal).assign (mkConst ``True.intro)

theorem FA.kernelBad : 1 = 2 := by cheat_close

theorem FA.usesKernelBad : 2 = 1 := FA.kernelBad.symm

theorem FA.lateBad : 1 = 2 := by
  have _h : True := trivial
  simp

theorem FA.usesLateBad : 2 = 1 := FA.lateBad.symm

theorem FA.fine : 1 + 1 = 2 := rfl

#print axioms FA.usesKernelBad
#print axioms FA.usesLateBad
