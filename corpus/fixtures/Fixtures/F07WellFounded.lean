/-! F07: well-founded recursion (`termination_by`, `decreasing_by`), `_unary`
auxiliaries, and reserved `induct`/`eq_def` names. -/
namespace F07

def log2 (n : Nat) : Nat :=
  if h : n < 2 then 0 else 1 + log2 (n / 2)
termination_by n
decreasing_by omega

def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

theorem log2_eight : log2 8 = 3 := by
  simp [log2]

theorem ack_pos (m n : Nat) : 0 < ack m n := by
  induction m, n using ack.induct with
  | case1 n => simp [ack]
  | case2 m ih => rw [ack]; exact ih
  | case3 m n _ ih2 => rw [ack]; exact ih2

end F07
