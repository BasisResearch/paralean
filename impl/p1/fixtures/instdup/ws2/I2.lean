/-! Duplicate instance, workspace 2: the same instance type as ws1 (a collision), plus two
instances whose types differ only in a universe level. Stock Lean names those two
`instInhabitedULiftNat` and `instInhabitedULiftNat_1` (environment-dependent); the canonical
scheme gives them different digests and no `_n`. -/
namespace InstDup

instance : Inhabited (Nat × String × Bool) := ⟨(8, "y", false)⟩

instance : Inhabited (ULift.{1} Nat) := ⟨⟨1⟩⟩

instance : Inhabited (ULift.{2} Nat) := ⟨⟨2⟩⟩

end InstDup
