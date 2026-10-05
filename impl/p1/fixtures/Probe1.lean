namespace Probe

def value : Nat := 0

theorem value_zero : value = 0 := rfl

inductive Color where
  | red | green | blue
  deriving Repr, DecidableEq

structure Point where
  x : Nat
  y : Nat

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

theorem fib_two : fib 2 = 1 := by simp [fib]

private def aux (n : Nat) : Nat := n + 1

theorem aux_pos (n : Nat) : 0 < aux n := by unfold aux; omega

class Foo (α : Type) where
  foo : α

instance : Foo Nat := ⟨3⟩

@[simp] theorem foo_nat : (Foo.foo : Nat) = 3 := rfl

mutual
inductive Even : Nat → Prop
  | zero : Even 0
  | succ : Odd n → Even (n + 1)
inductive Odd : Nat → Prop
  | succ : Even n → Odd (n + 1)
end

theorem ack_zero (n : Nat) : ack 0 n = n + 1 := by rw [ack]

end Probe
