import Lean
-- N3: must be rejected. `debug.skipKernelTC` inserts an ill-typed theorem
-- (`Eq.refl 1 : 1 = 2`) without kernel checking; it has no axioms or sorry, so only
-- validator re-checking (not an axiom audit) catches it.
open Lean Elab Command in
set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl (.thmDecl {
  name := `N3.bad, levelParams := []
  type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 1) (mkNatLit 2)
  value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 1) })
#print axioms N3.bad
