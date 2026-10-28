-- paralean: published projection of Seven.lean

theorem P5.add_comm_7 : ∀ n : Nat, n + 7 = 7 + n := by
  run_tac
    for _ in [:100] do
      Lean.Elab.Tactic.evalTactic (← `(tactic| have hscal : (1 : Nat) + 1 = 2 := by decide))
      Lean.Elab.Tactic.evalTactic (← `(tactic| clear hscal))
  intro n
  exact P5.add_comm_general n 7
