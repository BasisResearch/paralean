import Lean

theorem P5.add_comm_general : ∀ a b : Nat, a + b = b + a := by
  exact Nat.add_comm

theorem P5.add_comm_1 : ∀ n : Nat, n + 1 = 1 + n := by
  run_tac
    for _ in [:2000] do
      Lean.Elab.Tactic.evalTactic (← `(tactic| have hscal : (1 : Nat) + 1 = 2 := by decide))
      Lean.Elab.Tactic.evalTactic (← `(tactic| clear hscal))
  intro n
  exact P5.add_comm_general n 1

theorem P5.add_comm_2 : ∀ n : Nat, n + 2 = 2 + n := by
  run_tac
    for _ in [:2000] do
      Lean.Elab.Tactic.evalTactic (← `(tactic| have hscal : (1 : Nat) + 1 = 2 := by decide))
      Lean.Elab.Tactic.evalTactic (← `(tactic| clear hscal))
  intro n
  exact P5.add_comm_general n 2

theorem P5.add_comm_3 : ∀ n : Nat, n + 3 = 3 + n := by
  run_tac
    for _ in [:2000] do
      Lean.Elab.Tactic.evalTactic (← `(tactic| have hscal : (1 : Nat) + 1 = 2 := by decide))
      Lean.Elab.Tactic.evalTactic (← `(tactic| clear hscal))
  intro n
  exact P5.add_comm_general n 3

theorem P5.add_comm_4 : ∀ n : Nat, n + 4 = 4 + n := by
  run_tac
    for _ in [:2000] do
      Lean.Elab.Tactic.evalTactic (← `(tactic| have hscal : (1 : Nat) + 1 = 2 := by decide))
      Lean.Elab.Tactic.evalTactic (← `(tactic| clear hscal))
  intro n
  exact P5.add_comm_general n 4

theorem P5.add_comm_5 : ∀ n : Nat, n + 5 = 5 + n := by
  run_tac
    for _ in [:2000] do
      Lean.Elab.Tactic.evalTactic (← `(tactic| have hscal : (1 : Nat) + 1 = 2 := by decide))
      Lean.Elab.Tactic.evalTactic (← `(tactic| clear hscal))
  intro n
  exact P5.add_comm_general n 5

theorem P5.add_comm_6 : ∀ n : Nat, n + 6 = 6 + n := by
  run_tac
    for _ in [:2000] do
      Lean.Elab.Tactic.evalTactic (← `(tactic| have hscal : (1 : Nat) + 1 = 2 := by decide))
      Lean.Elab.Tactic.evalTactic (← `(tactic| clear hscal))
  intro n
  exact P5.add_comm_general n 6

theorem P5.add_comm_7 : ∀ n : Nat, n + 7 = 7 + n := by
  run_tac
    for _ in [:2000] do
      Lean.Elab.Tactic.evalTactic (← `(tactic| have hscal : (1 : Nat) + 1 = 2 := by decide))
      Lean.Elab.Tactic.evalTactic (← `(tactic| clear hscal))
  intro n
  exact P5.add_comm_general n 7

theorem P5.add_comm_8 : ∀ n : Nat, n + 8 = 8 + n := by
  run_tac
    for _ in [:2000] do
      Lean.Elab.Tactic.evalTactic (← `(tactic| have hscal : (1 : Nat) + 1 = 2 := by decide))
      Lean.Elab.Tactic.evalTactic (← `(tactic| clear hscal))
  intro n
  exact P5.add_comm_general n 8

theorem P5.add_comm_up_to_eight : ∀ n : Nat, (n + 1 = 1 + n) ∧ (n + 2 = 2 + n) ∧ (n + 3 = 3 + n) ∧ (n + 4 = 4 + n) ∧ (n + 5 = 5 + n) ∧ (n + 6 = 6 + n) ∧ (n + 7 = 7 + n) ∧ (n + 8 = 8 + n) := by
  intro n
  exact ⟨P5.add_comm_1 n, P5.add_comm_2 n, P5.add_comm_3 n, P5.add_comm_4 n, P5.add_comm_5 n, P5.add_comm_6 n, P5.add_comm_7 n, P5.add_comm_8 n⟩
