module
/-! F15: module system (as used by every Mathlib file at this pin): `public section`,
`@[expose]`, `private`, and `meta`. Capsules must carry the visibility context. -/

namespace F15

public section

def hidden (n : Nat) : Nat := n + 2

@[expose] def shown (n : Nat) : Nat := n + 3

theorem shown_eq (n : Nat) : shown n = n + 3 := rfl

private def helper : Nat := 5

def usesHelper : Nat := helper + 1

end

meta def metaHelper : Nat := 9

end F15
