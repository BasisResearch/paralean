/-! F02: non-recursive definitions, `match_n` auxiliaries, `abbrev`, and consumer-side
reserved names (`eq_1`, `eq_def`) realized lazily. -/
namespace F02

def double (n : Nat) : Nat := n + n

abbrev Pred := Nat → Prop

def classify : Nat → String
  | 0 => "zero"
  | 1 => "one"
  | _ => "many"

/-- Uses the reserved equation lemmas, which the consumer realizes; never published. -/
theorem classify_zero : classify 0 = "zero" := by rw [classify.eq_1]

theorem double_eq (n : Nat) : double n = n + n := by rw [double.eq_def]

theorem classify_two : classify 2 = "many" := by simp [classify]

end F02
