/-! Duplicate instance, workspace 1: an anonymous instance of `Inhabited (Nat × String × Bool)`. -/
namespace InstDup

instance : Inhabited (Nat × String × Bool) := ⟨(7, "x", true)⟩

end InstDup
