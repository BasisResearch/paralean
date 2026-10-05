/-! F06: structural recursion (`below`/`brecOn` compilation) and consumer-realized
`induct`/`eq_n` names. -/
namespace F06

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

theorem fib_five : fib 5 = 5 := by decide

theorem sumList_append (xs ys : List Nat) : sumList (xs ++ ys) = sumList xs + sumList ys := by
  induction xs with
  | nil => simp [sumList]
  | cons x xs ih => simp [sumList, ih, Nat.add_assoc]

theorem fib_pos (n : Nat) (h : 0 < n) : 0 < fib n := by
  induction n using fib.induct with
  | case1 => contradiction
  | case2 => decide
  | case3 n ih1 ih2 => simp only [fib]; omega

end F06
