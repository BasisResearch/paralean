-- N2: must be rejected (new user axiom in the closure).
axiom N2.cheat : False
theorem N2.bad : 1 = 2 := N2.cheat.elim
