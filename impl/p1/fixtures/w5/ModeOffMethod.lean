structure Foo where n : Nat
def Foo.field (x : Foo) : Nat := x.n + 1
def use (x : Foo) : Nat := x.field
example : use ⟨0⟩ = 1 := by decide
