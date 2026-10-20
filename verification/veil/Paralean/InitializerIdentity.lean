import Paralean.LeanNames

/-! A refinement boundary for initializer and quotation bodies. `LeanNames`
proves relocation invariance for declaration names and their group-keyed
rendering. An embedded `Name` literal is data in a kernel term, and can be
observed by the initializer or a macro. It does not inherit that invariant. -/

namespace ParaleanInitializerIdentity
open ParaleanLeanNames

variable {mod atom sfx group : Type}

/-- The part of an initializer or quotation body relevant to this argument.
`literal` denotes the runtime name value, not the declaration's own name. -/
structure LiteralBody (mod atom sfx : Type) where
  literal : LeanName mod atom sfx
  deriving DecidableEq

def observe (b : LiteralBody mod atom sfx) : LeanName mod atom sfx := b.literal

/-- Exact body equality entails equality of observable name values. -/
theorem exact_implies_observable {a b : LiteralBody mod atom sfx}
    (h : a = b) : observe a = observe b := congrArg observe h

/-- Relocating a private name changes its value when the module changes. -/
theorem private_literal_changes (f : mod → mod) (m : mod) (b : atom)
    (hm : m ≠ f m) :
    observe (⟨LeanName.priv m b⟩ : LiteralBody mod atom sfx) ≠
      observe (⟨relocate f (LeanName.priv m b)⟩ : LiteralBody mod atom sfx) := by
  simpa [observe, relocate] using hm

/-- Yet group-keyed declaration rendering erases precisely that module path.
This is the scope of `LeanNames.render_relocate`. -/
theorem rendered_declaration_unchanged (f : mod → mod) (g : group)
    (m : mod) (b : atom) :
    render g (relocate f (LeanName.priv m b : LeanName mod atom sfx)) =
      render g (LeanName.priv m b) :=
  render_relocate f g _

/-- A quotient that identifies the two bodies cannot also reflect equality
of their observable literal names. Thus quotient equality cannot certify an
exact replay of this body. -/
theorem quotient_cannot_certify_exact (f : mod → mod) (m : mod) (b : atom)
    (hm : m ≠ f m) (Q : LiteralBody mod atom sfx → Nat)
    (hq : Q ⟨LeanName.priv m b⟩ = Q ⟨relocate f (LeanName.priv m b)⟩) :
    ¬ (∀ x y : LiteralBody mod atom sfx, Q x = Q y → observe x = observe y) := by
  intro hreflect
  exact private_literal_changes f m b hm (hreflect _ _ hq)

/-- Non-vacuous two-module example: scoped declaration names render equally,
while the initializer's embedded private name has a different runtime value. -/
theorem concrete_module_change :
    render (0 : Fin 1) (LeanName.priv (0 : Fin 2) (0 : Fin 1) :
      LeanName (Fin 2) (Fin 1) Unit) =
      render (0 : Fin 1) (LeanName.priv (1 : Fin 2) (0 : Fin 1)) ∧
    observe (⟨LeanName.priv (0 : Fin 2) (0 : Fin 1)⟩ :
      LiteralBody (Fin 2) (Fin 1) Unit) ≠
      observe (⟨LeanName.priv (1 : Fin 2) (0 : Fin 1)⟩ :
        LiteralBody (Fin 2) (Fin 1) Unit) := by
  constructor <;> decide

/-- A raw-hygiene lookup admits a candidate only when its key has exactly one
exported match. This fact is independent of the order in which the exported
constants were enumerated. The later declaration-ID check is still required:
matching a name does not establish equality of its body. -/
theorem singleton_hygiene_match_sound {candidate key : Type}
    [DecidableEq key] (candidates : List candidate) (rawKey : candidate → key)
    (capturedKey : key) (chosen : candidate)
    (h : candidates.filter (fun c => decide (rawKey c = capturedKey)) = [chosen]) :
    chosen ∈ candidates ∧ rawKey chosen = capturedKey ∧
      ∀ other ∈ candidates, rawKey other = capturedKey → other = chosen := by
  have hchosen : chosen ∈ candidates.filter (fun c => decide (rawKey c = capturedKey)) := by
    rw [h]
    simp
  have hpart := List.mem_filter.mp hchosen
  refine ⟨hpart.1, by simpa using hpart.2, ?_⟩
  intro other hmem hkey
  have hother : other ∈ candidates.filter (fun c => decide (rawKey c = capturedKey)) :=
    List.mem_filter.mpr ⟨hmem, by simpa [hkey]⟩
  rw [h] at hother
  simpa using hother

/-- Sorting the exported list leaves the singleton candidate unchanged. -/
theorem singleton_hygiene_match_perm {candidate key : Type}
    [DecidableEq key] (candidates reordered : List candidate)
    (rawKey : candidate → key) (capturedKey : key) (chosen : candidate)
    (hperm : candidates.Perm reordered)
    (h : candidates.filter (fun c => decide (rawKey c = capturedKey)) = [chosen]) :
    reordered.filter (fun c => decide (rawKey c = capturedKey)) = [chosen] := by
  have hfilter := hperm.filter (fun c => decide (rawKey c = capturedKey))
  rw [h] at hfilter
  exact hfilter.symm.eq_singleton

#print axioms exact_implies_observable
#print axioms private_literal_changes
#print axioms rendered_declaration_unchanged
#print axioms quotient_cannot_certify_exact
#print axioms concrete_module_change
#print axioms singleton_hygiene_match_sound
#print axioms singleton_hygiene_match_perm

end ParaleanInitializerIdentity
