/-! F04: plain, indexed and nested inductives (eager `casesOn`, `noConfusion`,
`below`, `brecOn`, `ctorIdx`, `injEq`, SizeOf). -/
namespace F04

inductive Color | red | green | blue
  deriving DecidableEq

inductive Vec (α : Type) : Nat → Type
  | nil : Vec α 0
  | cons {n} : α → Vec α n → Vec α (n + 1)

inductive Tree where
  | node : List Tree → Tree

theorem red_ne_green : Color.red ≠ Color.green := by decide

theorem cons_inj {α n} (a b : α) (v w : Vec α n) (h : Vec.cons a v = Vec.cons b w) : a = b := by
  cases h; rfl

end F04
