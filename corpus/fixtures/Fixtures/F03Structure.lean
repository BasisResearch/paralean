/-! F03: structures with defaults, `extends`, classes, projections and `mk.injEq`. -/
namespace F03

structure Point where
  x : Nat
  y : Nat := 0
  deriving Repr

structure Point3 extends Point where
  z : Nat

class HasSize (α : Type) where
  size : α → Nat

theorem point_ext (p q : Point) (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  cases p; cases q; simp_all

def origin3 : Point3 := { x := 0, z := 0 }

theorem origin3_y : origin3.y = 0 := rfl

end F03
