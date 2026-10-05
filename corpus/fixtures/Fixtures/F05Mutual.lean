/-! F05: mutual blocks. Each `mutual … end` is one command and one atomic group. -/
namespace F05

mutual
  inductive Even : Nat → Prop
    | zero : Even 0
    | succ : Odd n → Even (n + 1)
  inductive Odd : Nat → Prop
    | succ : Even n → Odd (n + 1)
end

mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

theorem isEven_two : isEven 2 = true := by decide

theorem even_two : Even 2 := .succ (.succ .zero)

end F05
