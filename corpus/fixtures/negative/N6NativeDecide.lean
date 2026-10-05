-- N6: must be rejected under the baseline axiom policy (`Lean.ofReduceBool` /
-- `Lean.trustCompiler` are outside {propext, Classical.choice, Quot.sound}).
theorem N6.bad : 2 ^ 20 = 1048576 := by native_decide
#print axioms N6.bad
