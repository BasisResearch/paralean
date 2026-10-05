/-! F09: commands that change instances or attributes without a public declaration of
their own. Each needs a canonical anchor (docs/p0-interfaces.md §Anchors). -/
namespace F09

structure Box (α : Type) where
  val : α

/-- Anonymous instance: produces only a generated name. -/
instance : Inhabited (Box Nat) := ⟨⟨0⟩⟩

def boxDefault : Box Nat := default

-- `deriving instance` as a stand-alone command.
deriving instance Repr for Box

theorem box_val (b : Box Nat) : b.val = b.val := rfl

def boxPred (b : Box Nat) : Prop := b.val = 0

/-- `attribute [instance]` adds no constant; only an instance-extension entry. -/
@[instance_reducible] def decBoxPred : DecidablePred boxPred := fun b => inferInstanceAs (Decidable (b.val = 0))
attribute [instance] decBoxPred

theorem default_boxPred : boxPred default := by decide

/-- `attribute [simp]` on an existing lemma: no constant, only a simp-set entry. -/
theorem box_mk_val (n : Nat) : (Box.mk n).val = n := rfl
attribute [simp] box_mk_val

end F09
