/-! F08: private declarations and generated names (`instFooNat`, deriving handlers). -/
namespace F08

private def secret (n : Nat) : Nat := n * 3

private theorem secret_zero : secret 0 = 0 := rfl

def reveal (n : Nat) : Nat := secret n + 1

theorem reveal_zero : reveal 0 = 1 := by simp [reveal, secret_zero]

class Foo (α : Type) where
  foo : α

/-- Auto-named `instFooNat`: a generated name keyed by group. -/
instance : Foo Nat := ⟨7⟩

inductive Shape | circle (r : Nat) | square (s : Nat)
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

theorem foo_nat : (Foo.foo : Nat) = 7 := rfl

end F08
