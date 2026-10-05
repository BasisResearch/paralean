import Paralean.Groups

/-! Transparent workspaces. Each file is a declaration-level RGA over the Groups
registry. A published group carries an immutable file, anchor, Lamport timestamp,
author and tombstone flag. The anchor positions are ordered by one fixed total
order (the RGA preorder): ancestors in the anchor tree first, and at the first
divergence the sibling with the larger (ts, author) key first. A revision renders
at its lineage root's position; superseded groups and tombstones are not rendered.
Rendering and naming are pure functions of the known set. The model has no source
text: a rendered declaration is its ID, rendered names and pinned dependency IDs. -/
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ParaleanWorkspaces
open ParaleanGroups

noncomputable section
attribute [local instance] Classical.propDecidable

/-! ## Keys and the path order -/

/-- `(Lamport time, author tie-break)`. -/
abbrev Key := Nat × Nat

def KeyLt (a b : Key) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

theorem keyLt_irrefl (a : Key) : ¬KeyLt a a := by
  rcases a with ⟨a1, a2⟩; simp only [KeyLt]; omega

theorem keyLt_trans {a b c : Key} : KeyLt a b → KeyLt b c → KeyLt a c := by
  rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩; rcases c with ⟨c1, c2⟩
  simp only [KeyLt]; omega

theorem keyLt_asymm {a b : Key} : KeyLt a b → ¬KeyLt b a := by
  rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩; simp only [KeyLt]; omega

theorem keyLt_total (a b : Key) : KeyLt a b ∨ a = b ∨ KeyLt b a := by
  rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩; simp only [KeyLt, Prod.mk.injEq]; omega

/-- Root-first paths. A proper prefix comes first; at the first difference the
larger key comes first. -/
def PathLt : List Key → List Key → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | x :: p, y :: q => (x = y ∧ PathLt p q) ∨ KeyLt y x

theorem pathLt_irrefl : ∀ p : List Key, ¬PathLt p p
  | [] => by simp [PathLt]
  | x :: p => by
    simp only [PathLt, true_and, not_or]
    exact ⟨pathLt_irrefl p, keyLt_irrefl x⟩

theorem pathLt_trans : ∀ p q r : List Key, PathLt p q → PathLt q r → PathLt p r
  | [], [], _, h, _ => by simp [PathLt] at h
  | [], _ :: _, [], _, h => by simp [PathLt] at h
  | [], _ :: _, _ :: _, _, _ => by simp [PathLt]
  | _ :: _, [], _, h, _ => by simp [PathLt] at h
  | _ :: _, _ :: _, [], _, h => by simp [PathLt] at h
  | x :: p, y :: q, z :: r, h1, h2 => by
    simp only [PathLt] at *
    rcases h1 with ⟨rfl, h1⟩ | h1 <;> rcases h2 with ⟨rfl, h2⟩ | h2
    · exact Or.inl ⟨rfl, pathLt_trans p q r h1 h2⟩
    · exact Or.inr h2
    · exact Or.inr h1
    · exact Or.inr (keyLt_trans h2 h1)

theorem pathLt_asymm {p q : List Key} (h : PathLt p q) : ¬PathLt q p :=
  fun h' => pathLt_irrefl p (pathLt_trans p q p h h')

theorem pathLt_total : ∀ p q : List Key, p ≠ q → PathLt p q ∨ PathLt q p
  | [], [], h => absurd rfl h
  | [], _ :: _, _ => Or.inl (by simp [PathLt])
  | _ :: _, [], _ => Or.inr (by simp [PathLt])
  | x :: p, y :: q, h => by
    simp only [PathLt]
    rcases keyLt_total x y with hxy | rfl | hyx
    · exact Or.inr (Or.inr hxy)
    · have hpq : p ≠ q := fun he => h (by rw [he])
      rcases pathLt_total p q hpq with h' | h'
      · exact Or.inl (Or.inl ⟨rfl, h'⟩)
      · exact Or.inr (Or.inl ⟨rfl, h'⟩)
    · exact Or.inl (Or.inr hyx)

/-- Inserting the newest child `k` below path `P`: every path whose keys are all
older than `k` precedes `P ++ [k]` exactly when it is `P` or precedes `P`. -/
theorem pathLt_append_newest (k : Key) :
    ∀ (P Q : List Key), (∀ y ∈ Q, KeyLt y k) → (PathLt Q (P ++ [k]) ↔ Q = P ∨ PathLt Q P)
  | [], [], _ => by simp [PathLt]
  | [], y :: r, h => by
    have hy := h y (by simp)
    simp only [List.nil_append, PathLt, reduceCtorEq, or_false, iff_false, not_or,
      not_and]
    exact ⟨fun he => by subst he; exact absurd hy (keyLt_irrefl y), keyLt_asymm hy⟩
  | z :: P, [], _ => by simp [PathLt]
  | z :: P, y :: r, h => by
    have ih := pathLt_append_newest k P r (fun w hw => h w (by simp [hw]))
    simp only [List.cons_append, PathLt, List.cons.injEq]
    constructor
    · rintro (⟨rfl, h'⟩ | h')
      · rcases ih.1 h' with rfl | h''
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨rfl, h''⟩)
      · exact Or.inr (Or.inr h')
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, h'⟩ | h')
      · exact Or.inl ⟨rfl, ih.2 (Or.inl rfl)⟩
      · exact Or.inl ⟨rfl, ih.2 (Or.inr h')⟩
      · exact Or.inr h'


/-! ## Layout data and the fixed order -/

/-- Immutable per-group placement data. `tie` encodes authors for tie-breaks.
`key_inj`: `(ts, author)` identifies a group (an assumption: a node never reuses
a Lamport time). `tombstone d`: `d` is a deletion, a revision that supersedes its
ancestors and is never rendered itself. `univ` enumerates the finitely many groups. -/
structure Layout (node group file : Type) where
  fileOf : group → file
  anchor : group → Option group
  ts : group → Nat
  author : group → node
  tie : node → Nat
  tie_inj : ∀ m n, tie m = tie n → m = n
  key_inj : ∀ d e, ts d = ts e → author d = author e → d = e
  tombstone : group → Bool
  univ : List group
  univ_complete : ∀ d, d ∈ univ
  univ_nodup : univ.Nodup

variable {node group name snapshot file : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]

/-- Minimum of a list under a strict total order. -/
theorem list_min_by {α : Type} (R : α → α → Prop) (trans : ∀ a b c, R a b → R b c → R a c)
    (total : ∀ a b, a ≠ b → R a b ∨ R b a) (P : α → Prop) :
    ∀ l : List α, (∃ c ∈ l, P c) → ∃ w ∈ l, P w ∧ ∀ c ∈ l, P c → c ≠ w → R w c
  | [], ⟨_, h, _⟩ => absurd h (by simp)
  | z :: l, hne => by
    by_cases hl : ∃ c ∈ l, P c
    · obtain ⟨w, hw, hpw, hmin⟩ := list_min_by R trans total P l hl
      by_cases hz : P z ∧ z ≠ w
      · rcases total z w hz.2 with hzw | hwz
        · refine ⟨z, by simp, hz.1, fun c hc hpc hcz => ?_⟩
          rcases List.mem_cons.1 hc with rfl | hc
          · exact absurd rfl hcz
          · by_cases hcw : c = w
            · subst hcw; exact hzw
            · exact trans _ _ _ hzw (hmin c hc hpc hcw)
        · refine ⟨w, by simp [hw], hpw, fun c hc hpc hcw => ?_⟩
          rcases List.mem_cons.1 hc with rfl | hc
          · exact hwz
          · exact hmin c hc hpc hcw
      · refine ⟨w, by simp [hw], hpw, fun c hc hpc hcw => ?_⟩
        rcases List.mem_cons.1 hc with rfl | hc
        · exact absurd ⟨hpc, hcw⟩ hz
        · exact hmin c hc hpc hcw
    · obtain ⟨c, hc, hpc⟩ := hne
      have hpz : P z := by
        rcases List.mem_cons.1 hc with rfl | hc
        · exact hpc
        · exact absurd ⟨c, hc, hpc⟩ hl
      refine ⟨z, by simp, hpz, fun c hc hpc hcz => ?_⟩
      rcases List.mem_cons.1 hc with rfl | hc
      · exact absurd rfl hcz
      · exact absurd ⟨c, hc, hpc⟩ hl

def KeyLe (a b : Key) : Prop := KeyLt a b ∨ a = b

theorem keyLe_trans {a b c : Key} : KeyLe a b → KeyLe b c → KeyLe a c := by
  rintro (h1 | rfl) (h2 | rfl)
  · exact Or.inl (keyLt_trans h1 h2)
  · exact Or.inl h1
  · exact Or.inl h2
  · exact Or.inr rfl

theorem keyLt_of_lt_of_le {a b c : Key} : KeyLt a b → KeyLe b c → KeyLt a c := by
  rintro h1 (h2 | rfl)
  · exact keyLt_trans h1 h2
  · exact h1

theorem keyLt_of_le_of_lt {a b c : Key} : KeyLe a b → KeyLt b c → KeyLt a c := by
  rintro (h1 | rfl) h2
  · exact keyLt_trans h1 h2
  · exact h2

namespace Layout
variable (L : Layout node group file)

def key (d : group) : Key := (L.ts d, L.tie (L.author d))

theorem key_injective {d e : group} (h : L.key d = L.key e) : d = e := by
  simp only [key, Prod.mk.injEq] at h
  exact L.key_inj d e h.1 (L.tie_inj _ _ h.2)

theorem key_lt_of_ts {d e : group} (h : L.ts d < L.ts e) : KeyLt (L.key d) (L.key e) :=
  Or.inl h

/-- `m` is the minimum-key element of `S`. -/
def KeyMin (S : group → Prop) (m : group) : Prop :=
  S m ∧ ∀ c, S c → c ≠ m → KeyLt (L.key m) (L.key c)

def minOf (S : group → Prop) : group :=
  if h : ∃ m, L.KeyMin S m then Classical.choose h else default

theorem keyMin_unique {S : group → Prop} {m m' : group} (h : L.KeyMin S m) (h' : L.KeyMin S m') :
    m = m' := by
  by_contra hne
  exact keyLt_asymm (h.2 m' h'.1 (Ne.symm hne)) (h'.2 m h.1 hne)

theorem keyMin_exists {S : group → Prop} (h : ∃ c, S c) : ∃ m, L.KeyMin S m := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨w, _, hw, hmin⟩ := list_min_by (fun a b => KeyLt (L.key a) (L.key b))
    (fun _ _ _ => keyLt_trans)
    (fun a b hab => by
      rcases keyLt_total (L.key a) (L.key b) with h | h | h
      · exact Or.inl h
      · exact absurd (L.key_injective h) hab
      · exact Or.inr h)
    S L.univ ⟨c, L.univ_complete c, hc⟩
  exact ⟨w, hw, fun c hc hcw => hmin c (L.univ_complete c) hc hcw⟩

theorem minOf_spec {S : group → Prop} (h : ∃ c, S c) : L.KeyMin S (L.minOf S) := by
  have hex := L.keyMin_exists h
  unfold minOf; rw [dif_pos hex]; exact Classical.choose_spec hex

theorem minOf_eq {S : group → Prop} {m : group} (h : L.KeyMin S m) : L.minOf S = m :=
  L.keyMin_unique (L.minOf_spec ⟨m, h.1⟩) h

theorem keyMin_le {S : group → Prop} {m c : group} (h : L.KeyMin S m) (hc : S c) :
    KeyLe (L.key m) (L.key c) := by
  by_cases hcm : c = m
  · subst hcm; exact Or.inr rfl
  · exact Or.inl (h.2 c hc hcm)

/-- A larger set has a smaller (or equal) minimum. -/
theorem minOf_mono {S T : group → Prop} (hST : ∀ c, S c → T c) (hS : ∃ c, S c) :
    KeyLe (L.key (L.minOf T)) (L.key (L.minOf S)) :=
  L.keyMin_le (L.minOf_spec (let ⟨c, hc⟩ := hS; ⟨c, hST c hc⟩)) (hST _ (L.minOf_spec hS).1)

/-- Root-first anchor path. It follows an anchor only to an older group, so it is
defined for every group; on reachable published groups the guard makes every
anchor older (`anchor_closed`), so it is the real anchor chain (`path_published`). -/
def path (d : group) : List Key :=
  match L.anchor d with
  | none => [L.key d]
  | some a => if h : L.ts a < L.ts d then path a ++ [L.key d] else [L.key d]
termination_by L.ts d

theorem path_none {d : group} (h : L.anchor d = none) : L.path d = [L.key d] := by
  rw [path]; simp [h]

theorem path_some {d a : group} (h : L.anchor d = some a) (hlt : L.ts a < L.ts d) :
    L.path d = L.path a ++ [L.key d] := by
  rw [path]; simp [h, hlt]

theorem path_split (d : group) : ∃ P, L.path d = P ++ [L.key d] := by
  rw [path]
  split
  · exact ⟨[], rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨[], rfl⟩

theorem path_inj {d e : group} (h : L.path d = L.path e) : d = e := by
  obtain ⟨P, hP⟩ := L.path_split d
  obtain ⟨Q, hQ⟩ := L.path_split e
  rw [hP, hQ] at h
  have := congrArg List.getLast? h
  simp only [List.getLast?_concat, Option.some.injEq] at this
  exact L.key_injective this

theorem path_bound : ∀ (t : Nat) (d : group), L.ts d = t → ∀ y ∈ L.path d, y.1 ≤ L.ts d := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro d hd y hy
    rw [path] at hy
    split at hy
    · simp only [List.mem_singleton] at hy; subst hy; simp [key]
    · rename_i a _
      split at hy
      · rename_i hlt
        rcases List.mem_append.1 hy with hy | hy
        · have := ih (L.ts a) (hd ▸ hlt) a rfl y hy; omega
        · simp only [List.mem_singleton] at hy; subst hy; simp [key]
      · simp only [List.mem_singleton] at hy; subst hy; simp [key]

theorem path_older {d e : group} (h : L.ts d < L.ts e) : ∀ y ∈ L.path d, KeyLt y (L.key e) :=
  fun y hy => Or.inl (Nat.lt_of_le_of_lt (L.path_bound _ d rfl y hy) h)

/-- The fixed RGA order on anchor positions. -/
def Prec (d e : group) : Prop := PathLt (L.path d) (L.path e)

theorem prec_irrefl (d : group) : ¬L.Prec d d := pathLt_irrefl _
theorem prec_trans {d e g : group} : L.Prec d e → L.Prec e g → L.Prec d g :=
  pathLt_trans _ _ _
theorem prec_asymm {d e : group} : L.Prec d e → ¬L.Prec e d := pathLt_asymm
theorem prec_total {d e : group} (h : d ≠ e) : L.Prec d e ∨ L.Prec e d :=
  pathLt_total _ _ (fun he => h (L.path_inj he))

/-- `Prec` is a strict total order on anchor positions. -/
theorem prec_strict_total_order :
    (∀ d, ¬L.Prec d d) ∧ (∀ d e g, L.Prec d e → L.Prec e g → L.Prec d g) ∧
    (∀ d e, d ≠ e → L.Prec d e ∨ L.Prec e d) :=
  ⟨L.prec_irrefl, fun _ _ _ => L.prec_trans, fun _ _ h => L.prec_total h⟩

end Layout

/-! ## Rendering live heads

A revision has no anchor position of its own: it occupies the position of its
lineage root, the minimum-key group among itself and its revision ancestors.
Groups are ordered by their root's anchor position, and groups sharing a root
(concurrent revisions of one lineage) by their own key, oldest first. A group is
rendered iff it is known, not a tombstone, and not superseded by a known group
that has it as an ancestor. -/

variable (L : Layout node group file) (th : Theory node group name snapshot)

/-- The lineage root that fixes `d`'s position. -/
def root (d : group) : group := L.minOf (fun a => a = d ∨ th.ancestors d a = true)

theorem root_spec (d : group) :
    L.KeyMin (fun a => a = d ∨ th.ancestors d a = true) (root L th d) :=
  L.minOf_spec ⟨d, Or.inl rfl⟩

theorem root_mem (d : group) : root L th d = d ∨ th.ancestors d (root L th d) = true :=
  (root_spec L th d).1

/-- A group with no revision ancestors is its own root. -/
theorem root_fresh (d : group) (h : ∀ a, th.ancestors d a = false) : root L th d = d :=
  L.minOf_eq ⟨Or.inl rfl, fun c hc hcd => by
    rcases hc with rfl | hc
    · exact absurd rfl hcd
    · rw [h c] at hc; cases hc⟩

/-- A revision whose ancestry is exactly `w` and `w`'s ancestry, and which is newer
than `w`, has `w`'s root: it renders in `w`'s place. -/
theorem revision_root (r w : group)
    (hanc : ∀ a, th.ancestors r a = true ↔ a = w ∨ th.ancestors w a = true)
    (hts : L.ts w < L.ts r) : root L th r = root L th w := by
  have hw := root_spec L th w
  refine L.minOf_eq ⟨?_, fun c hc hcm => ?_⟩
  · rcases hw.1 with h | h
    · exact Or.inr ((hanc _).2 (Or.inl h))
    · exact Or.inr ((hanc _).2 (Or.inr h))
  · rcases hc with rfl | hc
    · exact keyLt_of_le_of_lt (L.keyMin_le hw (Or.inl rfl)) (L.key_lt_of_ts hts)
    · exact hw.2 c ((hanc c).1 hc) hcm

/-- The render order: by root position, then by own key. -/
def PosLt (d e : group) : Prop :=
  L.Prec (root L th d) (root L th e) ∨
    (root L th d = root L th e ∧ KeyLt (L.key d) (L.key e))

theorem posLt_irrefl (d : group) : ¬PosLt L th d d := by
  rintro (h | ⟨_, h⟩)
  · exact L.prec_irrefl _ h
  · exact keyLt_irrefl _ h

theorem posLt_trans {d e g : group} : PosLt L th d e → PosLt L th e g → PosLt L th d g := by
  rintro (h1 | ⟨h1, k1⟩) (h2 | ⟨h2, k2⟩)
  · exact Or.inl (L.prec_trans h1 h2)
  · exact Or.inl (by rw [← h2]; exact h1)
  · exact Or.inl (by rw [h1]; exact h2)
  · exact Or.inr ⟨h1.trans h2, keyLt_trans k1 k2⟩

theorem posLt_asymm {d e : group} (h : PosLt L th d e) : ¬PosLt L th e d :=
  fun h' => posLt_irrefl L th d (posLt_trans L th h h')

theorem posLt_total {d e : group} (h : d ≠ e) : PosLt L th d e ∨ PosLt L th e d := by
  by_cases hr : root L th d = root L th e
  · rcases keyLt_total (L.key d) (L.key e) with k | k | k
    · exact Or.inl (Or.inr ⟨hr, k⟩)
    · exact absurd (L.key_injective k) h
    · exact Or.inr (Or.inr ⟨hr.symm, k⟩)
  · rcases L.prec_total hr with p | p
    · exact Or.inl (Or.inl p)
    · exact Or.inr (Or.inl p)

/-- `PosLt` is a strict total order on all groups. -/
theorem posLt_strict_total_order :
    (∀ d, ¬PosLt L th d d) ∧ (∀ d e g, PosLt L th d e → PosLt L th e g → PosLt L th d g) ∧
    (∀ d e, d ≠ e → PosLt L th d e ∨ PosLt L th e d) :=
  ⟨posLt_irrefl L th, fun _ _ _ => posLt_trans L th, fun _ _ h => posLt_total L th h⟩

/-- A revision with `w`'s root takes `w`'s place relative to every other lineage. -/
theorem revision_in_place (r w g : group)
    (hanc : ∀ a, th.ancestors r a = true ↔ a = w ∨ th.ancestors w a = true)
    (hts : L.ts w < L.ts r) (hg : root L th g ≠ root L th w) :
    (PosLt L th g r ↔ PosLt L th g w) ∧ (PosLt L th r g ↔ PosLt L th w g) := by
  have hr := revision_root L th r w hanc hts
  unfold PosLt
  rw [hr]
  constructor
  · constructor
    · rintro (h | ⟨h, _⟩)
      · exact Or.inl h
      · exact absurd h hg
    · rintro (h | ⟨h, _⟩)
      · exact Or.inl h
      · exact absurd h hg
  · constructor
    · rintro (h | ⟨h, _⟩)
      · exact Or.inl h
      · exact absurd h.symm hg
    · rintro (h | ⟨h, _⟩)
      · exact Or.inl h
      · exact absurd h.symm hg

def sortBy {α : Type} (R : α → α → Prop) (l : List α) : List α :=
  l.mergeSort (fun a b => decide (a = b ∨ R a b))

theorem sortBy_pairwise {α : Type} (R : α → α → Prop)
    (trans : ∀ a b c, R a b → R b c → R a c) (total : ∀ a b, a ≠ b → R a b ∨ R b a)
    (l : List α) (hl : l.Nodup) : (sortBy R l).Pairwise R := by
  unfold sortBy
  have hle := List.pairwise_mergeSort (le := fun a b => decide (a = b ∨ R a b))
    (by
      intro a b c hab hbc
      simp only [decide_eq_true_eq] at *
      rcases hab with rfl | hab <;> rcases hbc with rfl | hbc
      · exact Or.inl rfl
      · exact Or.inr hbc
      · exact Or.inr hab
      · exact Or.inr (trans _ _ _ hab hbc))
    (by
      intro a b
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      by_cases h : a = b
      · exact Or.inl (Or.inl h)
      · rcases total a b h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr (Or.inr h'))
    l
  have hnd : (l.mergeSort (fun a b => decide (a = b ∨ R a b))).Nodup :=
    (List.mergeSort_perm l _).symm.nodup hl
  refine (hle.and (List.nodup_iff_pairwise_ne.1 hnd)).imp ?_
  rintro a b ⟨hab, hne⟩
  simp only [decide_eq_true_eq] at hab
  rcases hab with rfl | h
  · exact absurd rfl hne
  · exact h

/-- Rendered iff known, not a tombstone, and not superseded by a known revision. -/
def Live (K : group → Bool) (d : group) : Prop :=
  K d = true ∧ L.tombstone d = false ∧ ¬∃ e, K e = true ∧ th.ancestors e d = true

/-- The rendered file `f` of known set `K`: its live heads in the fixed order. -/
def render (K : group → Bool) (f : file) : List group :=
  (sortBy (PosLt L th) L.univ).filter (fun d => decide (Live L th K d) && decide (L.fileOf d = f))

def insertK (K : group → Bool) (d : group) : group → Bool := fun e => K e || decide (e = d)

theorem render_pairwise (K : group → Bool) (f : file) : (render L th K f).Pairwise (PosLt L th) :=
  (sortBy_pairwise (PosLt L th) (fun _ _ _ => posLt_trans L th) (fun _ _ h => posLt_total L th h)
    L.univ L.univ_nodup).filter _

theorem render_mem (K : group → Bool) (f : file) (d : group) :
    d ∈ render L th K f ↔ Live L th K d ∧ L.fileOf d = f := by
  simp [render, sortBy, List.mem_filter, List.mem_mergeSort, L.univ_complete]

theorem render_nodup (K : group → Bool) (f : file) : (render L th K f).Nodup :=
  List.nodup_iff_pairwise_ne.2 ((render_pairwise L th K f).imp (by
    intro a b h he
    subst he
    exact posLt_irrefl L th a h))

theorem tombstone_not_rendered (K : group → Bool) (f : file) (d : group)
    (h : L.tombstone d = true) : d ∉ render L th K f := by
  rw [render_mem]; rintro ⟨⟨_, ht, _⟩, _⟩; rw [h] at ht; cases ht

theorem superseded_not_rendered (K : group → Bool) (f : file) (d e : group)
    (he : K e = true) (hed : th.ancestors e d = true) : d ∉ render L th K f := by
  rw [render_mem]; rintro ⟨⟨_, _, hs⟩, _⟩; exact hs ⟨e, he, hed⟩

/-- **Render function** (definitional). Equal known sets give equal renders. -/
theorem render_function (s s' : CanonicalState node group name snapshot) (n m : node)
    (h : s.known n = s'.known m) (f : file) :
    render L th (s.known n) f = render L th (s'.known m) f := by rw [h]

theorem eq_of_pairwise_mem {α : Type} {R : α → α → Prop} (irr : ∀ a, ¬R a a)
    (asym : ∀ a b, R a b → ¬R b a) :
    ∀ l₁ l₂ : List α, l₁.Pairwise R → l₂.Pairwise R → (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 (by simp)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).1 (by simp)) (by simp)
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    rw [List.pairwise_cons] at h₁ h₂
    have hab : a = b := by
      by_contra hne
      have ha : a ∈ l₂ := by
        rcases List.mem_cons.1 ((h a).1 (by simp)) with he | he
        · exact absurd he hne
        · exact he
      have hb : b ∈ l₁ := by
        rcases List.mem_cons.1 ((h b).2 (by simp)) with he | he
        · exact absurd he.symm hne
        · exact he
      exact asym _ _ (h₁.1 b hb) (h₂.1 a ha)
    subst hab
    congr 1
    refine eq_of_pairwise_mem irr asym l₁ l₂ h₁.2 h₂.2 (fun x => ?_)
    have hx := h x
    simp only [List.mem_cons] at hx
    constructor
    · intro hm
      rcases hx.1 (Or.inr hm) with he | he
      · subst he; exact absurd (h₁.1 _ hm) (irr _)
      · exact he
    · intro hm
      rcases hx.2 (Or.inr hm) with he | he
      · subst he; exact absurd (h₂.1 _ hm) (irr _)
      · exact he

/-- **Canonical form.** Any strictly sorted presentation of the live heads of
`f` is the render. -/
theorem render_unique (K : group → Bool) (f : file) (l : List group)
    (hs : l.Pairwise (PosLt L th)) (hm : ∀ d, d ∈ l ↔ Live L th K d ∧ L.fileOf d = f) :
    l = render L th K f :=
  eq_of_pairwise_mem (posLt_irrefl L th) (fun _ _ => posLt_asymm L th) l _ hs
    (render_pairwise L th K f) (fun d => (hm d).trans (render_mem L th K f d).symm)

/-! ## Positions in a list -/

def Precedes {α : Type} (l : List α) (x y : α) : Prop := ∃ l₁ l₂, l = l₁ ++ x :: l₂ ∧ y ∈ l₂

theorem precedes_of_pairwise {α : Type} {R : α → α → Prop} (asym : ∀ a b, R a b → ¬R b a) :
    ∀ (l : List α) {x y : α}, l.Pairwise R → x ∈ l → y ∈ l → R x y → Precedes l x y
  | [], _, _, _, hx, _, _ => absurd hx (by simp)
  | z :: l, x, y, hp, hx, hy, hr => by
    rw [List.pairwise_cons] at hp
    by_cases hzx : z = x
    · subst hzx
      have hy' : y ∈ l := by
        rcases List.mem_cons.1 hy with he | he
        · subst he; exact absurd hr (fun h => asym _ _ h h)
        · exact he
      exact ⟨[], l, rfl, hy'⟩
    · have hx' : x ∈ l := by
        rcases List.mem_cons.1 hx with he | he
        · exact absurd he.symm hzx
        · exact he
      by_cases hzy : z = y
      · subst hzy; exact absurd hr (asym _ _ (hp.1 x hx'))
      · have hy' : y ∈ l := by
          rcases List.mem_cons.1 hy with he | he
          · exact absurd he.symm hzy
          · exact he
        obtain ⟨l₁, l₂, he, hm⟩ := precedes_of_pairwise asym l hp.2 hx' hy' hr
        exact ⟨z :: l₁, l₂, by rw [he]; rfl, hm⟩

theorem pairwise_of_precedes {α : Type} {R : α → α → Prop} {l : List α} {x y : α}
    (hp : l.Pairwise R) (h : Precedes l x y) : R x y := by
  obtain ⟨l₁, l₂, rfl, hy⟩ := h
  rw [List.pairwise_append, List.pairwise_cons] at hp
  exact hp.2.1.1 y hy

theorem render_precedes_iff (K : group → Bool) (f : file) (x y : group) :
    Precedes (render L th K f) x y ↔
      x ∈ render L th K f ∧ y ∈ render L th K f ∧ PosLt L th x y := by
  constructor
  · intro h
    obtain ⟨l₁, l₂, he, hy⟩ := h
    refine ⟨by rw [he]; simp, by rw [he]; simp [hy], ?_⟩
    exact pairwise_of_precedes (render_pairwise L th K f) ⟨l₁, l₂, he, hy⟩
  · rintro ⟨hx, hy, hr⟩
    exact precedes_of_pairwise (fun _ _ => posLt_asymm L th) _ (render_pairwise L th K f) hx hy hr

/-- **Stable relative order.** Two groups rendered in both `K` and `K'` appear in
the same relative order in both renders. -/
theorem render_order_stable (K K' : group → Bool) (f : file) (x y : group)
    (hx : x ∈ render L th K f) (hy : y ∈ render L th K f)
    (hx' : x ∈ render L th K' f) (hy' : y ∈ render L th K' f) :
    Precedes (render L th K f) x y ↔ Precedes (render L th K' f) x y := by
  rw [render_precedes_iff, render_precedes_iff]
  exact ⟨fun h => ⟨hx', hy', h.2.2⟩, fun h => ⟨hx, hy, h.2.2⟩⟩

/-- **Monotone up to supersession.** Dropping from the old render the groups no
longer live in `K'` leaves a sublist of the new render. -/
theorem render_sublist_live (K K' : group → Bool) (f : file) :
    ((render L th K f).filter (fun d => decide (Live L th K' d))).Sublist (render L th K' f) := by
  have he : (render L th K f).filter (fun d => decide (Live L th K' d)) =
      (render L th K' f).filter (fun d => decide (Live L th K d)) := by
    unfold render
    rw [List.filter_filter, List.filter_filter]
    congr 1
    funext d
    by_cases h1 : Live L th K d <;> by_cases h2 : Live L th K' d <;> simp [h1, h2]
  rw [he]
  exact List.filter_sublist

/-- **Why a group disappears.** If `K ⊆ K'` and `d` is rendered in `K` but not in
`K'`, then `K'` newly contains a revision or tombstone that supersedes `d`. -/
theorem render_disappears (K K' : group → Bool) (hK : ∀ d, K d = true → K' d = true) (f : file)
    (d : group) (hd : d ∈ render L th K f) (hd' : d ∉ render L th K' f) :
    ∃ e, K' e = true ∧ K e = false ∧ th.ancestors e d = true := by
  rw [render_mem] at hd hd'
  obtain ⟨⟨hk, ht, hs⟩, hf⟩ := hd
  by_contra hno
  apply hd'
  refine ⟨⟨hK d hk, ht, ?_⟩, hf⟩
  rintro ⟨e, he, hed⟩
  cases hke : K e
  · exact hno ⟨e, he, hke, hed⟩
  · exact hs ⟨e, hke, hed⟩

/-! ## The layered transition system -/

/-- Conditions on node `n` staging group `d`: its anchor is a lineage root (no
ancestors) of the same file that `n` knows or has itself pending; its Lamport
time exceeds every group `n` knows or has pending; `n` is its author; its
revision ancestors are known and in the same file; and every same-file
dependency renders above it (`PosLt e d`). -/
def Staged (s : CanonicalState node group name snapshot) (n : node) (d : group) : Prop :=
  (∀ a, L.anchor d = some a →
    (s.known n a = true ∨ s.pending n a = true) ∧ L.fileOf a = L.fileOf d ∧
      ∀ b, th.ancestors a b = false) ∧
  (∀ e, s.known n e = true ∨ s.pending n e = true → L.ts e < L.ts d) ∧ L.author d = n ∧
  (∀ a, th.ancestors d a = true → s.known n a = true ∧ L.fileOf a = L.fileOf d) ∧
  (∀ e, th.deps d e = true → L.fileOf e = L.fileOf d → PosLt L th e d)

/-- Every newly pending group was staged under `Staged`. -/
def StageGuard (s t : CanonicalState node group name snapshot) : Prop :=
  ∀ n d, t.pending n d = true → s.pending n d = false → Staged L th s n d

/-- A group newly published from `n`'s pending bit has an anchor that `n` knows
(so an anchor that was `n`'s own pending group is published first). -/
def PublishGuard (s t : CanonicalState node group name snapshot) : Prop :=
  ∀ n d, t.published d = true → s.published d = false → s.pending n d = true →
    ∀ a, L.anchor d = some a → s.known n a = true

def Guard (s t : CanonicalState node group name snapshot) : Prop :=
  StageGuard L th s t ∧ PublishGuard L s t

def Next (s t : CanonicalState node group name snapshot) : Prop :=
  (∃ l, GroupsNext th s l t) ∧ Guard L th s t

inductive Reachable : CanonicalState node group name snapshot → Prop where
  | initial {s} : GroupsInit th s → Reachable s
  | step {s t} : Reachable s → Next L th s t → Reachable t

theorem guard_stutter (s : CanonicalState node group name snapshot) : Guard L th s s :=
  ⟨fun n d h h' => (by rw [h] at h'; cases h'), fun n d h h' => (by rw [h] at h'; cases h')⟩

theorem stageGuard_of_no_new_pending (s t : CanonicalState node group name snapshot)
    (h : ∀ n d, t.pending n d = true → s.pending n d = true) : StageGuard L th s t := by
  intro n d ht hs; rw [h n d ht] at hs; cases hs

theorem publishGuard_of_no_new_published (s t : CanonicalState node group name snapshot)
    (h : ∀ d, t.published d = true → s.published d = true) : PublishGuard L s t := by
  intro n d ht hs; rw [h d ht] at hs; cases hs

theorem guard_of_no_new_pending (s t : CanonicalState node group name snapshot)
    (h : ∀ n d, t.pending n d = true → s.pending n d = true)
    (hp : ∀ d, t.published d = true → s.published d = true) : Guard L th s t :=
  ⟨stageGuard_of_no_new_pending L th s t h, publishGuard_of_no_new_published L s t hp⟩

/-- Implementability: staging reads only `n`'s own known and pending sets and
immutable data; publication reads only the publisher's known set. -/
theorem staged_local (s s' : CanonicalState node group name snapshot) (n : node) (d : group)
    (h : s.known n = s'.known n) (hp : s.pending n = s'.pending n) :
    Staged L th s n d ↔ Staged L th s' n d := by
  simp only [Staged, h, hp]

theorem reachable_groups {s} (hr : Reachable L th s) : ParaleanGroups.Reachable th s := by
  induction hr with
  | initial hi => exact ParaleanGroups.Reachable.initial hi
  | step _ hn ih =>
    obtain ⟨⟨l, ht⟩, _⟩ := hn
    exact ParaleanGroups.Reachable.step ih ht

/-! ### Registry transition facts -/

theorem groups_published_update (rg rg' : CanonicalState node group name snapshot) (n : node)
    (d : group) (h : GroupsNext th rg (.publish n d) rg') :
    ∀ e, rg'.published e = true ↔ e = d ∨ rg.published e = true := by
  simp only [GroupsNext, ParaleanGroups.Next, NextAct, publish.ext.derived_eq] at h
  dsimp [publish.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
    Veil.canonicalFieldRepresentation] at h
  split_ifs at h <;> rcases h with ⟨_, _, _, rfl⟩ <;>
    simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp]
  all_goals grind

theorem groups_published_unchanged (rg rg' : CanonicalState node group name snapshot)
    (l : Label node group name snapshot) (hg : ∀ n d, l ≠ .publish n d)
    (ht : GroupsNext th rg l rg') : rg'.published = rg.published := by
  cases l <;>
    simp only [GroupsNext, ParaleanGroups.Next, NextAct, prepare.ext.derived_eq,
      publish.ext.derived_eq, receive.ext.derived_eq, commit.ext.derived_eq,
      crash.ext.derived_eq, recover.ext.derived_eq, partition.ext.derived_eq,
      reconnect.ext.derived_eq, heal.ext.derived_eq] at ht
  all_goals
    try exact False.elim (hg _ _ rfl)
  all_goals
    dsimp [prepare.ext.tr, receive.ext.tr, commit.ext.tr, crash.ext.tr, recover.ext.tr,
      partition.ext.tr, reconnect.ext.tr, heal.ext.tr, getFrom, setIn, readFrom,
      Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
      canonicalFieldRep, Veil.canonicalFieldRepresentation] at ht
    repeat' rcases ht with ⟨ha, ht⟩
    try subst rg'
    rfl

theorem groups_published_source (rg rg' : CanonicalState node group name snapshot)
    (l : Label node group name snapshot) (ht : GroupsNext th rg l rg') (h : group)
    (hp : rg'.published h = true) : rg.published h = true ∨ ∃ m, rg.pending m h = true := by
  by_cases hl : ∃ n d, l = .publish n d
  · obtain ⟨n, d, rfl⟩ := hl
    have hpend := ((publish_enabled_iff th rg n d).1 ⟨rg', ht⟩).2.2
    rcases (groups_published_update th rg rg' n d ht h).1 hp with he | hold
    · subst he; exact Or.inr ⟨n, hpend⟩
    · exact Or.inl hold
  · have hg : ∀ n d, l ≠ .publish n d := fun n d he => hl ⟨n, d, he⟩
    rw [groups_published_unchanged th rg rg' l hg ht] at hp
    exact Or.inl hp

theorem groups_init_empty (rg : CanonicalState node group name snapshot) (h : GroupsInit th rg) :
    (∀ d, rg.published d = false) ∧ ∀ n d, rg.pending n d = false := by
  simp only [GroupsInit, Init, initializer.ext.tr] at h
  dsimp [getFrom, setIn, readFrom, Veil.FieldRepresentation.get, instIsSubStateOfRefl,
    instIsSubReaderOfRefl, canonicalFieldRep, Veil.canonicalFieldRepresentation] at h
  subst h
  refine ⟨fun d => ?_, fun n d => ?_⟩ <;>
    simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp]

/-- A pending bit is cleared only by publishing that group or by a crash that
clears every pending bit of the node. -/
theorem groups_pending_cleared (rg rg' : CanonicalState node group name snapshot)
    (l : Label node group name snapshot) (ht : GroupsNext th rg l rg') (n : node) (a : group)
    (hs : rg.pending n a = true) (hc : rg'.pending n a = false) :
    rg'.published a = true ∨ ∀ d, rg'.pending n d = false := by
  cases l <;>
    simp only [GroupsNext, ParaleanGroups.Next, NextAct, prepare.ext.derived_eq,
      publish.ext.derived_eq, receive.ext.derived_eq, commit.ext.derived_eq,
      crash.ext.derived_eq, recover.ext.derived_eq, partition.ext.derived_eq,
      reconnect.ext.derived_eq, heal.ext.derived_eq] at ht
  all_goals
    dsimp [prepare.ext.tr, publish.ext.tr, receive.ext.tr, commit.ext.tr, crash.ext.tr,
      recover.ext.tr, partition.ext.tr, reconnect.ext.tr, heal.ext.tr, getFrom, setIn, readFrom,
      Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
      canonicalFieldRep, Veil.canonicalFieldRepresentation] at ht
  all_goals try split_ifs at ht
  all_goals
    repeat' rcases ht with ⟨_, ht⟩
    try subst rg'
    simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp] at hc ⊢
    try grind

/-! ### Anchor and ancestry closure -/

def AnchorOK (P : group → Bool) (d : group) : Prop :=
  ∀ a, L.anchor d = some a → P a = true ∧ L.fileOf a = L.fileOf d ∧ L.ts a < L.ts d

def AncOK (P : group → Bool) (d : group) : Prop :=
  ∀ a, th.ancestors d a = true → P a = true ∧ L.fileOf a = L.fileOf d ∧ L.ts a < L.ts d

def Inv (s : CanonicalState node group name snapshot) : Prop :=
  (∀ d, s.published d = true → AnchorOK L s.published d ∧ AncOK L th s.published d) ∧
  (∀ n d, s.pending n d = true →
    AnchorOK L (fun a => s.published a || s.pending n a) d ∧ AncOK L th s.published d ∧
      L.author d = n)

theorem anchorOK_mono {P Q : group → Bool} (hPQ : ∀ d, P d = true → Q d = true) {d : group}
    (h : AnchorOK L P d) : AnchorOK L Q d := by
  intro a ha
  obtain ⟨h1, h2, h3⟩ := h a ha
  exact ⟨hPQ a h1, h2, h3⟩

theorem ancOK_mono {P Q : group → Bool} (hPQ : ∀ d, P d = true → Q d = true) {d : group}
    (h : AncOK L th P d) : AncOK L th Q d := by
  intro a ha
  obtain ⟨h1, h2, h3⟩ := h a ha
  exact ⟨hPQ a h1, h2, h3⟩

theorem reachable_inv (ha : TheoryAssumptions th) {s} (hr : Reachable L th s) : Inv L th s := by
  induction hr with
  | initial hi =>
    obtain ⟨hp, hq⟩ := groups_init_empty th _ hi
    refine ⟨fun d h => ?_, fun n d h => ?_⟩
    · rw [hp d] at h; cases h
    · rw [hq n d] at h; cases h
  | @step s t hr hn ih =>
    obtain ⟨⟨l, ht⟩, hg, hpub⟩ := hn
    have mono := (registry_step_persistent th s t l ht).1
    have hsafe := ParaleanGroups.reachable_safe th ha (reachable_groups L th hr)
    -- An anchor that is published or `n`'s own pending group stays so while `n` has
    -- some pending group.
    have keep : ∀ n d a, t.pending n d = true → s.published a = true ∨ s.pending n a = true →
        (t.published a || t.pending n a) = true := by
      intro n d a hd ha'
      simp only [Bool.or_eq_true]
      rcases ha' with h | h
      · exact Or.inl (mono a h)
      · cases hta : t.pending n a
        · rcases groups_pending_cleared th s t l ht n a h hta with h' | h'
          · exact Or.inl h'
          · rw [h' d] at hd; cases hd
        · exact Or.inr rfl
    refine ⟨fun d hd => ?_, fun n d hd => ?_⟩
    · by_cases hsd : s.published d = true
      · exact ⟨anchorOK_mono L mono (ih.1 d hsd).1, ancOK_mono L th mono (ih.1 d hsd).2⟩
      · have hsd' : s.published d = false := by simpa using hsd
        rcases groups_published_source th s t l ht d hd with hold | ⟨m, hm⟩
        · exact absurd hold hsd
        · refine ⟨fun a han => ?_, ancOK_mono L th mono (ih.2 m d hm).2.1⟩
          obtain ⟨_, hf, hts⟩ := (ih.2 m d hm).1 a han
          exact ⟨mono a (hsafe.2.2.1 m a (hpub m d hd hsd' hm a han)), hf, hts⟩
    · by_cases hs : s.pending n d = true
      · refine ⟨fun a han => ?_, ancOK_mono L th mono (ih.2 n d hs).2.1, (ih.2 n d hs).2.2⟩
        obtain ⟨hk, hf, hts⟩ := (ih.2 n d hs).1 a han
        simp only [Bool.or_eq_true] at hk
        exact ⟨keep n d a hd hk, hf, hts⟩
      · have hs' : s.pending n d = false := by simpa using hs
        obtain ⟨hanc, hts, hauth, hancs, _⟩ := hg n d hd hs'
        refine ⟨fun a haa => ?_, fun a haa => ?_, hauth⟩
        · obtain ⟨hk, hf, _⟩ := hanc a haa
          refine ⟨keep n d a hd ?_, hf, hts a hk⟩
          rcases hk with hk | hk
          · exact Or.inl (hsafe.2.2.1 n a hk)
          · exact Or.inr hk
        · obtain ⟨hk, hf⟩ := hancs a haa
          exact ⟨mono a (hsafe.2.2.1 n a hk), hf, hts a (Or.inl hk)⟩

/-- **Anchor closure.** A published group's anchor is published, in the same
file, and older. -/
theorem anchor_closed (ha : TheoryAssumptions th) {s} (hr : Reachable L th s) (d a : group)
    (hd : s.published d = true) (han : L.anchor d = some a) :
    s.published a = true ∧ L.fileOf a = L.fileOf d ∧ L.ts a < L.ts d :=
  (reachable_inv L th ha hr).1 d hd |>.1 a han

/-- **Ancestry closure.** A published group's revision ancestors are published,
in the same file, and older. -/
theorem ancestors_closed (ha : TheoryAssumptions th) {s} (hr : Reachable L th s) (d a : group)
    (hd : s.published d = true) (han : th.ancestors d a = true) :
    s.published a = true ∧ L.fileOf a = L.fileOf d ∧ L.ts a < L.ts d :=
  (reachable_inv L th ha hr).1 d hd |>.2 a han

theorem known_anchor_published (ha : TheoryAssumptions th) {s} (hr : Reachable L th s)
    (n : node) (d a : group) (hd : s.known n d = true) (han : L.anchor d = some a) :
    s.published a = true :=
  (anchor_closed L th ha hr d a
    (ParaleanGroups.known_published th ha (reachable_groups L th hr) n d hd) han).1

/-- At staging the author knows the anchor or has it pending itself. -/
theorem staged_anchor_known {s t} (hn : Next L th s t) (n : node) (d a : group)
    (hp : t.pending n d = true) (hf : s.pending n d = false) (han : L.anchor d = some a) :
    (s.known n a = true ∨ s.pending n a = true) ∧ L.fileOf a = L.fileOf d :=
  let h := (hn.2.1 n d hp hf).1 a han
  ⟨h.1, h.2.1⟩

theorem path_published (ha : TheoryAssumptions th) {s} (hr : Reachable L th s) (d a : group)
    (hd : s.published d = true) (han : L.anchor d = some a) :
    L.path d = L.path a ++ [L.key d] :=
  L.path_some han (anchor_closed L th ha hr d a hd han).2.2

/-- Well-formed known sets: every member is valid and newer than its ancestors. -/
def WF (K : group → Bool) : Prop :=
  ∀ d, K d = true → th.valid d = true ∧ ∀ a, th.ancestors d a = true → L.ts a < L.ts d

theorem reachable_wf_published (ha : TheoryAssumptions th) {s} (hr : Reachable L th s) :
    WF L th s.published := fun d hd =>
  ⟨ParaleanGroups.published_valid th ha (reachable_groups L th hr) d hd,
   fun a han => (ancestors_closed L th ha hr d a hd han).2.2⟩

theorem reachable_wf_known (ha : TheoryAssumptions th) {s} (hr : Reachable L th s) (n : node) :
    WF L th (s.known n) := fun d hd =>
  reachable_wf_published L th ha hr d
    (ParaleanGroups.known_published th ha (reachable_groups L th hr) n d hd)

theorem wf_mono {K K' : group → Bool} (h : ∀ d, K d = true → K' d = true) (hw : WF L th K') :
    WF L th K := fun d hd => hw d (h d hd)

theorem wf_not_self {K : group → Bool} (hw : WF L th K) {d : group} (hd : K d = true) :
    th.ancestors d d = false := by
  cases h : th.ancestors d d
  · rfl
  · exact absurd ((hw d hd).2 d h) (Nat.lt_irrefl _)

/-! ## Insertion and intention preservation -/

theorem staged_not_known {s : CanonicalState node group name snapshot} {n : node} {d : group}
    (hs : Staged L th s n d) : s.known n d = false := by
  cases h : s.known n d
  · rfl
  · exact absurd (hs.2.1 d (Or.inl h)) (Nat.lt_irrefl _)

theorem staged_not_pending {s : CanonicalState node group name snapshot} {n : node} {d : group}
    (hs : Staged L th s n d) : s.pending n d = false := by
  cases h : s.pending n d
  · rfl
  · exact absurd (hs.2.1 d (Or.inr h)) (Nat.lt_irrefl _)

theorem root_ts_le' {x : group} (hx : ∀ a, th.ancestors x a = true → L.ts a < L.ts x) :
    L.ts (root L th x) ≤ L.ts x := by
  rcases root_mem L th x with h | h
  · rw [h]; exact Nat.le_refl _
  · exact Nat.le_of_lt (hx _ h)

theorem root_ts_le {K : group → Bool} (hw : WF L th K) {x : group} (hx : K x = true) :
    L.ts (root L th x) ≤ L.ts x :=
  root_ts_le' L th (hw x hx).2

/-- Groups a node knows or has pending are newer than their revision ancestors. -/
theorem reachable_older (ha : TheoryAssumptions th) {s} (hr : Reachable L th s) (n : node)
    (x : group) (hx : s.known n x = true ∨ s.pending n x = true) :
    ∀ a, th.ancestors x a = true → L.ts a < L.ts x := by
  rcases hx with hx | hx
  · exact (reachable_wf_known L th ha hr n x hx).2
  · exact fun a h => ((reachable_inv L th ha hr).2 n x hx).2.1 a h |>.2.2

/-- `x`'s position is at or above the position of `d`'s anchor. -/
def Above (d x : group) : Prop :=
  ∃ a, L.anchor d = some a ∧ (root L th x = a ∨ L.Prec (root L th x) a)

/-- For a fresh insertion `d` (no revision ancestors) staged by `n`, a group `x`
that `n` knows or has pending renders above `d` exactly when its position is at
or above `d`'s anchor. -/
theorem staged_pos_iff {s : CanonicalState node group name snapshot} {n : node} {d : group}
    (hs : Staged L th s n d) (hfresh : ∀ b, th.ancestors d b = false)
    (x : group) (hx : s.known n x = true ∨ s.pending n x = true)
    (hxa : ∀ a, th.ancestors x a = true → L.ts a < L.ts x) :
    PosLt L th x d ↔ Above L th d x := by
  have hrd : root L th d = d := root_fresh L th d hfresh
  have hts : L.ts (root L th x) < L.ts d :=
    Nat.lt_of_le_of_lt (root_ts_le' L th hxa) (hs.2.1 x hx)
  have hne : root L th x ≠ d := fun h => by rw [h] at hts; exact Nat.lt_irrefl _ hts
  unfold PosLt Above
  rw [hrd]
  cases han : L.anchor d with
  | none =>
    simp only [reduceCtorEq, false_and, exists_false, iff_false, not_or, not_and]
    refine ⟨?_, fun h => absurd h hne⟩
    unfold Layout.Prec
    rw [L.path_none han]
    have := pathLt_append_newest (L.key d) [] (L.path (root L th x)) (L.path_older hts)
    simp only [List.nil_append] at this
    rw [this]
    obtain ⟨P, hP⟩ := L.path_split (root L th x)
    rw [hP]
    cases P <;> simp [PathLt]
  | some a =>
    have hta := hs.2.1 a (hs.1 a han).1
    simp only [Option.some.injEq, exists_eq_left']
    unfold Layout.Prec
    rw [L.path_some han hta, pathLt_append_newest (L.key d) _ _ (L.path_older hts)]
    constructor
    · rintro ((h | h) | ⟨h, _⟩)
      · exact Or.inl (L.path_inj h)
      · exact Or.inr h
      · exact absurd h hne
    · rintro (h | h)
      · exact Or.inl (Or.inl (by rw [h]))
      · exact Or.inl (Or.inr h)

/-- **Intention preservation** (both sides). Let `n` stage a fresh insertion `d`.
For every group `x` that `n` knows at staging or has itself pending (staged but
not yet published), in every render containing both: if `x`'s position is at or
above `d`'s anchor then `x` precedes `d`, and otherwise `d` precedes `x`. With no
anchor, `d` precedes every such `x`. -/
theorem intention_preserved (ha : TheoryAssumptions th) {s t : CanonicalState node group name snapshot}
    (hr : Reachable L th s) (hn : Next L th s t) (n : node) (d : group)
    (hp : t.pending n d = true) (hf : s.pending n d = false)
    (hfresh : ∀ b, th.ancestors d b = false) (x : group)
    (hx : s.known n x = true ∨ s.pending n x = true)
    (K' : group → Bool) (hx' : x ∈ render L th K' (L.fileOf d))
    (hd' : d ∈ render L th K' (L.fileOf d)) :
    (Above L th d x → Precedes (render L th K' (L.fileOf d)) x d) ∧
    (¬Above L th d x → Precedes (render L th K' (L.fileOf d)) d x) := by
  have hs := hn.2.1 n d hp hf
  have hiff := staged_pos_iff L th hs hfresh x hx (reachable_older L th ha hr n x hx)
  have hxd : x ≠ d := fun h => by
    subst h
    rcases hx with hx | hx
    · rw [staged_not_known L th hs] at hx; cases hx
    · rw [staged_not_pending L th hs] at hx; cases hx
  refine ⟨fun h => (render_precedes_iff L th _ _ x d).2 ⟨hx', hd', hiff.2 h⟩, fun h => ?_⟩
  rcases posLt_total L th hxd with h' | h'
  · exact absurd (hiff.1 h') h
  · exact (render_precedes_iff L th _ _ d x).2 ⟨hd', hx', h'⟩

/-- **Insertion at the anchor.** In the author's own render of its known set plus
a fresh `d`, the groups before `d` are exactly those at or above `d`'s anchor. -/
theorem insert_after_anchor (ha : TheoryAssumptions th) {s t : CanonicalState node group name snapshot}
    (hr : Reachable L th s) (hn : Next L th s t) (n : node) (d : group)
    (hp : t.pending n d = true) (hf : s.pending n d = false)
    (hfresh : ∀ b, th.ancestors d b = false) (htomb : L.tombstone d = false) (x : group)
    (hx : x ∈ render L th (insertK (s.known n) d) (L.fileOf d)) (hxd : x ≠ d) :
    Precedes (render L th (insertK (s.known n) d) (L.fileOf d)) x d ↔ Above L th d x := by
  have hs := hn.2.1 n d hp hf
  have hk : s.known n x = true := by
    have := ((render_mem L th _ _ x).1 hx).1.1
    simpa [insertK, hxd] using this
  have hdx : d ∈ render L th (insertK (s.known n) d) (L.fileOf d) := by
    rw [render_mem]
    refine ⟨⟨by simp [insertK], htomb, ?_⟩, rfl⟩
    rintro ⟨e, he, hed⟩
    simp only [insertK, Bool.or_eq_true, decide_eq_true_eq] at he
    rcases he with he | rfl
    · have := (reachable_wf_known L th ha hr n e he).2 d hed
      exact absurd (hs.2.1 e (Or.inl he)) (Nat.lt_asymm this)
    · rw [hfresh] at hed; cases hed
  rw [render_precedes_iff]
  have hiff := staged_pos_iff L th hs hfresh x (Or.inl hk)
    (reachable_wf_known L th ha hr n x hk).2
  exact ⟨fun h => hiff.1 h.2.2, fun h => ⟨hx, hdx, hiff.2 h⟩⟩

end

noncomputable section
attribute [local instance] Classical.propDecidable

variable {node group name snapshot file : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]
variable (L : Layout node group file) (th : Theory node group name snapshot)

/-! ## Dependencies stay above -/

/-- **Dependencies stay above.** The guard requires every same-file dependency
of a staged group to render above it, so in every render that shows both, the
dependency precedes the group. -/
theorem deps_precede {s t : CanonicalState node group name snapshot}
    (hn : Next L th s t) (n : node) (d : group)
    (hp : t.pending n d = true) (hf : s.pending n d = false)
    (e : group) (hde : th.deps d e = true) (hfe : L.fileOf e = L.fileOf d)
    (K' : group → Bool) (he' : e ∈ render L th K' (L.fileOf d))
    (hd' : d ∈ render L th K' (L.fileOf d)) :
    Precedes (render L th K' (L.fileOf d)) e d :=
  (render_precedes_iff L th K' _ e d).2 ⟨he', hd', (hn.2.1 n d hp hf).2.2.2.2 e hde hfe⟩

/-! ## Names -/

/-- Rendered-name encoding. `declared d y`: `d` introduces `y` (public or scoped).
`env y`: `y` comes from the environment or an import. `reserved` is the renderer's
namespace (for example names under a prefix the elaborator rejects in user
source). `fresh x d` is injective and always reserved; environment names are not
reserved. That a group declares no reserved name is not assumed here: it is the
per-group admission check `NamesChecked`. -/
structure Naming where
  isTarget : name → Prop
  declared : group → name → Prop
  env : name → Prop
  member_declared : ∀ d x, th.member d x = true → declared d x
  reserved : name → Prop
  fresh : name → group → name
  fresh_inj : ∀ x y d e, fresh x d = fresh y e → x = y ∧ d = e
  fresh_reserved : ∀ x d, reserved (fresh x d)
  env_unreserved : ∀ y, env y → ¬reserved y

/-- Admission check on each group's own declarations: a valid group declares no
reserved name. Validation rejects the group otherwise; it reads only that group. -/
def NamesChecked {th : Theory node group name snapshot} (N : Naming th) : Prop :=
  ∀ e y, th.valid e = true → N.declared e y → ¬N.reserved y

variable (N : Naming th)

/-- A fresh name never equals a name a checked, valid group declares. -/
theorem fresh_not_declared (hc : NamesChecked N) (x : name) (d e : group) (y : name)
    (he : th.valid e = true) (hy : N.declared e y) : N.fresh x d ≠ y := fun h =>
  hc e y he hy (h ▸ N.fresh_reserved x d)

theorem fresh_env (x : name) (d : group) (y : name) (hy : N.env y) : N.fresh x d ≠ y :=
  fun h => N.env_unreserved y hy (h ▸ N.fresh_reserved x d)

/-- `d`'s lineage for `x`: itself and the groups it revises for `x`. Immutable. -/
def LinSet (x : name) (d : group) : group → Prop := fun a => a = d ∨ th.revisions d a x = true

/-- The lineage root: the minimum-key member of the lineage. -/
def lroot (x : name) (d : group) : group := L.minOf (LinSet th x d)

/-- The lineage key. -/
def lkey (x : name) (d : group) : Key := L.key (lroot L th x d)

theorem lroot_spec (x : name) (d : group) : L.KeyMin (LinSet th x d) (lroot L th x d) :=
  L.minOf_spec ⟨d, Or.inl rfl⟩

theorem lroot_self (x : name) (d : group) (h : ∀ a, th.revisions d a x = false) :
    lroot L th x d = d :=
  L.minOf_eq ⟨Or.inl rfl, fun c hc hcd => by
    rcases hc with rfl | hc
    · exact absurd rfl hcd
    · rw [h c] at hc; cases hc⟩

theorem lkey_le_self (x : name) (d : group) : KeyLe (lkey L th x d) (L.key d) :=
  L.keyMin_le (lroot_spec L th x d) (Or.inl rfl)

/-- A revision's lineage key is at most the revised group's. -/
theorem lkey_le_of_revises (ha : TheoryAssumptions th) {x : name} {r w : group}
    (hv : th.valid r = true) (hrw : th.revisions r w x = true) :
    KeyLe (lkey L th x r) (lkey L th x w) := by
  unfold lkey lroot
  refine L.minOf_mono (fun c hc => ?_) ⟨w, Or.inl rfl⟩
  rcases hc with rfl | hc
  · exact Or.inr hrw
  · exact Or.inr ((ha.1.2.1 r w x hv hrw).2.2 c hc)

theorem lroot_eq_iff (x : name) (d e : group) :
    lroot L th x d = lroot L th x e ↔ lkey L th x d = lkey L th x e :=
  ⟨fun h => by unfold lkey; rw [h], fun h => L.key_injective h⟩

/-- The winner order: lineage key, then (within one lineage) own key. -/
def LinLt (x : name) (d e : group) : Prop :=
  KeyLt (lkey L th x d) (lkey L th x e) ∨
    (lroot L th x d = lroot L th x e ∧ KeyLt (L.key d) (L.key e))

theorem linLt_le {x : name} {d e : group} (h : LinLt L th x d e) :
    KeyLe (lkey L th x d) (lkey L th x e) := by
  rcases h with h | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr ((lroot_eq_iff L th x d e).1 h)

theorem linLt_trans {x : name} {d e g : group} :
    LinLt L th x d e → LinLt L th x e g → LinLt L th x d g := by
  rintro (h1 | ⟨h1, k1⟩) (h2 | ⟨h2, k2⟩)
  · exact Or.inl (keyLt_trans h1 h2)
  · exact Or.inl (by unfold lkey at *; rw [← h2]; exact h1)
  · exact Or.inl (by unfold lkey at *; rw [h1]; exact h2)
  · exact Or.inr ⟨h1.trans h2, keyLt_trans k1 k2⟩

theorem linLt_irrefl {x : name} (d : group) : ¬LinLt L th x d d := by
  rintro (h | ⟨_, h⟩) <;> exact keyLt_irrefl _ h

theorem linLt_total {x : name} {d e : group} (h : d ≠ e) : LinLt L th x d e ∨ LinLt L th x e d := by
  by_cases hr : lroot L th x d = lroot L th x e
  · rcases keyLt_total (L.key d) (L.key e) with k | k | k
    · exact Or.inl (Or.inr ⟨hr, k⟩)
    · exact absurd (L.key_injective k) h
    · exact Or.inr (Or.inr ⟨hr.symm, k⟩)
  · rcases keyLt_total (lkey L th x d) (lkey L th x e) with k | k | k
    · exact Or.inl (Or.inl k)
    · exact absurd ((lroot_eq_iff L th x d e).2 k) hr
    · exact Or.inr (Or.inl k)

/-- Candidates for `x`: rendered (`Live`: known, not a tombstone, and not
superseded by any known group, for any name) and declaring the non-target name
`x`. A group revised for one of its names only is superseded for all of them, so
an unrendered group never holds a name. -/
def Cand (K : group → Bool) (x : name) (d : group) : Prop :=
  Live L th K d ∧ th.member d x = true ∧ ¬N.isTarget x

theorem cand_live {K : group → Bool} {x : name} {d : group} (h : Cand L th N K x d) :
    Live L th K d := h.1

/-- A revision for any name is an ancestry edge. -/
theorem ancestors_of_revisions (ha : TheoryAssumptions th) {e d : group} {x : name}
    (h : th.revisions e d x = true) : th.ancestors e d = true :=
  (ha.1.1 e d).2 ⟨x, h⟩

/-- The winner is the candidate with the least lineage key (ties within one
lineage by own key). -/
def IsWinner (K : group → Bool) (x : name) (w : group) : Prop :=
  Cand L th N K x w ∧ ∀ c, Cand L th N K x c → c ≠ w → LinLt L th x w c

def winner (K : group → Bool) (x : name) : Option group :=
  if h : ∃ w, IsWinner L th N K x w then some (Classical.choose h) else none

/-- The rendered name of group `d`'s declaration of `x`. -/
def renamed (K : group → Bool) (d : group) (x : name) : name :=
  if winner L th N K x = some d ∨ N.isTarget x then x else N.fresh x d

theorem isWinner_unique {K : group → Bool} {x : name} {u w : group}
    (hu : IsWinner L th N K x u) (hw : IsWinner L th N K x w) : u = w := by
  by_contra hne
  exact linLt_irrefl L th u (linLt_trans L th (hu.2 w hw.1 (Ne.symm hne)) (hw.2 u hu.1 hne))

theorem winner_eq_some (K : group → Bool) (x : name) (w : group) :
    winner L th N K x = some w ↔ IsWinner L th N K x w := by
  unfold winner
  constructor
  · intro h
    split at h
    · rename_i hex
      cases h
      exact Classical.choose_spec hex
    · cases h
  · intro hw
    have hex : ∃ w, IsWinner L th N K x w := ⟨w, hw⟩
    rw [dif_pos hex]
    exact congrArg some (isWinner_unique L th N (Classical.choose_spec hex) hw)

theorem winner_exists (K : group → Bool) (x : name) (h : ∃ c, Cand L th N K x c) :
    ∃ w, winner L th N K x = some w := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨w, _, hw, hmin⟩ := list_min_by (LinLt L th x) (fun _ _ _ => linLt_trans L th)
    (fun _ _ h => linLt_total L th h) (Cand L th N K x) L.univ ⟨c, L.univ_complete c, hc⟩
  exact ⟨w, (winner_eq_some L th N K x w).2
    ⟨hw, fun c hc hcw => hmin c (L.univ_complete c) hc hcw⟩⟩

/-- **Name agreement** (definitional). Names are a function of the known set. -/
theorem names_agree (s s' : CanonicalState node group name snapshot) (n m : node)
    (h : s.known n = s'.known m) :
    renamed L th N (s.known n) = renamed L th N (s'.known m) := by
  rw [h]

/-- **Unique names.** Within one known set, distinct declarations of non-target
names by valid groups render to distinct names, given the per-group reserved-name
check. -/
theorem names_unique (hc : NamesChecked N) (K : group → Bool) (d e : group) (x y : name)
    (hx : ¬N.isTarget x) (hy : ¬N.isTarget y)
    (hd : th.valid d = true) (he : th.valid e = true)
    (hdx : th.member d x = true) (hey : th.member e y = true)
    (h : renamed L th N K d x = renamed L th N K e y) : d = e ∧ x = y := by
  unfold renamed at h
  simp only [hx, hy, or_false] at h
  split_ifs at h with h1 h2 h2
  · subst h
    rw [h1] at h2
    exact ⟨Option.some.inj h2, rfl⟩
  · exact absurd h.symm (fresh_not_declared th N hc y e d x hd (N.member_declared d x hdx))
  · exact absurd h (fresh_not_declared th N hc x d e y he (N.member_declared e y hey))
  · have := N.fresh_inj x y d e h
    exact ⟨this.2, this.1⟩

/-- **No capture of environment names.** A rendered name that is an environment
or imported name is the declared name itself, never a generated one. -/
theorem renamed_env (K : group → Bool) (d : group) (x y : name) (hy : N.env y)
    (h : renamed L th N K d x = y) : renamed L th N K d x = x := by
  unfold renamed at *
  split_ifs at h ⊢ with hw
  · rfl
  · exact absurd h (fresh_env th N x d y hy)

/-- **Revising the winner keeps the name.** If `w` wins `x` in `K` and `r` (not a
tombstone, and not itself superseded by a group of `K`) revises `w` for `x`, then
after adding `r` the winner is `r` or a group with `w`'s lineage root; never a
group from another lineage. -/
theorem revise_winner_keeps_name (ha : TheoryAssumptions th) (K : group → Bool) (x : name)
    (w r : group) (hw : winner L th N K x = some w) (hwf : WF L th (insertK K r))
    (hrw : th.revisions r w x = true) (hrt : L.tombstone r = false)
    (hnew : ¬∃ e, K e = true ∧ th.ancestors e r = true) :
    ∃ v, winner L th N (insertK K r) x = some v ∧
      (v = r ∨ lroot L th x v = lroot L th x w) := by
  obtain ⟨⟨⟨hkw, _, hhw⟩, hmw, htw⟩, hmin⟩ := (winner_eq_some L th N K x w).1 hw
  have hrK : insertK K r r = true := by simp [insertK]
  have hvr := (hwf r hrK).1
  have hKK : ∀ e, K e = true → insertK K r e = true := fun e he => by simp [insertK, he]
  have hrc : Cand L th N (insertK K r) x r := by
    refine ⟨⟨hrK, hrt, ?_⟩, (ha.1.2.1 r w x hvr hrw).1, htw⟩
    rintro ⟨e, he, her⟩
    simp only [insertK, Bool.or_eq_true, decide_eq_true_eq] at he
    rcases he with he | he
    · exact hnew ⟨e, he, her⟩
    · rw [he, wf_not_self L th hwf hrK] at her; cases her
  obtain ⟨v, hv⟩ := winner_exists L th N (insertK K r) x ⟨r, hrc⟩
  refine ⟨v, hv, ?_⟩
  by_cases hvr' : v = r
  · exact Or.inl hvr'
  · right
    by_contra hroot
    have hvw := (winner_eq_some L th N _ x v).1 hv
    obtain ⟨⟨hkv, hbv, hhv⟩, hmv, htv⟩ := hvw.1
    have hkv' : K v = true := by simpa [insertK, hvr'] using hkv
    have hvne : v ≠ w := by
      rintro rfl
      exact hhv ⟨r, hrK, ancestors_of_revisions th ha hrw⟩
    have hvc : Cand L th N K x v :=
      ⟨⟨hkv', hbv, fun ⟨e, he, hev⟩ => hhv ⟨e, hKK e he, hev⟩⟩, hmv, htv⟩
    have hwv : KeyLt (lkey L th x w) (lkey L th x v) := by
      rcases hmin v hvc hvne with h | ⟨h, _⟩
      · exact h
      · exact absurd h.symm hroot
    have hle := lkey_le_of_revises L th ha hvr hrw
    have hvr2 : KeyLe (lkey L th x v) (lkey L th x r) := linLt_le L th (hvw.2 r hrc (Ne.symm hvr'))
    exact keyLt_irrefl _ (keyLt_of_lt_of_le hwv (keyLe_trans hvr2 hle))

/-- **Provisional winners, honestly.** Suppose `K ⊆ K'` and the winner of `x`
moves to a different lineage. Then `K'` newly contains a group declaring `x`
whose lineage key is strictly below the old winner's (an earlier-clocked
concurrent declaration arrived); or `K'` newly contains a tombstone that revises
the old winner (its lineage was deleted); or the newest member `m` of the old
winner's `x`-lineage in `K'` is superseded by a group `e` that revises it for
another name only, and `e` or `m` is new (a partial revision retired the lineage). -/
theorem winner_change_explained (ha : TheoryAssumptions th) (K K' : group → Bool)
    (hK : ∀ d, K d = true → K' d = true) (hwf : WF L th K') (x : name) (w w' : group)
    (hw : winner L th N K x = some w) (hw' : winner L th N K' x = some w')
    (hne : lroot L th x w' ≠ lroot L th x w) :
    (∃ c, K' c = true ∧ K c = false ∧ th.member c x = true ∧
      KeyLt (lkey L th x c) (lkey L th x w)) ∨
    (∃ t, K' t = true ∧ K t = false ∧ L.tombstone t = true ∧ th.revisions t w x = true) ∨
    (∃ e m, K' e = true ∧ K' m = true ∧ (m = w ∨ th.revisions m w x = true) ∧
      th.ancestors e m = true ∧ th.revisions e m x = false ∧ (K e = false ∨ K m = false)) := by
  obtain ⟨⟨⟨hkw, hbw, hhw⟩, hmw, htw⟩, hmin⟩ := (winner_eq_some L th N K x w).1 hw
  have hW' := (winner_eq_some L th N K' x w').1 hw'
  have hkne : lkey L th x w' ≠ lkey L th x w := fun h => hne ((lroot_eq_iff L th x _ _).2 h)
  -- If `w'` is strictly below `w` in lineage key, it must be new.
  have strict : KeyLt (lkey L th x w') (lkey L th x w) →
      ∃ c, K' c = true ∧ K c = false ∧ th.member c x = true ∧
        KeyLt (lkey L th x c) (lkey L th x w) := by
    intro hlt
    refine ⟨w', hW'.1.1.1, ?_, hW'.1.2.1, hlt⟩
    cases hk : K w'
    · rfl
    · have hc : Cand L th N K x w' := ⟨⟨hk, hW'.1.1.2.1,
        fun ⟨e, he, hev⟩ => hW'.1.1.2.2 ⟨e, hK e he, hev⟩⟩, hW'.1.2.1, hW'.1.2.2⟩
      have hne' : w' ≠ w := fun h => hne (by rw [h])
      exact absurd (linLt_le L th (hmin w' hc hne')) (fun h =>
        keyLt_irrefl _ (keyLt_of_lt_of_le hlt h))
  -- No member of `w`'s lineage that is already in `K` (other than through `w`) supersedes it.
  have hold : ∀ m, (m = w ∨ th.revisions m w x = true) → ∀ e, K e = true → K m = true →
      th.ancestors e m = true → False := by
    intro m hm e he hkm hem
    rcases hm with rfl | hr
    · exact hhw ⟨e, he, hem⟩
    · exact hhw ⟨m, hkm, ancestors_of_revisions th ha hr⟩
  by_cases hlive : ∃ h, Cand L th N K' x h ∧ (h = w ∨ th.revisions h w x = true)
  · left
    obtain ⟨h, hc, hhw'⟩ := hlive
    have hle : KeyLe (lkey L th x h) (lkey L th x w) := by
      rcases hhw' with rfl | hr
      · exact Or.inr rfl
      · exact lkey_le_of_revises L th ha (hwf h hc.1.1).1 hr
    apply strict
    by_cases hh : h = w'
    · subst hh
      rcases hle with hle | hle
      · exact hle
      · exact absurd hle hkne
    · rcases keyLe_trans (linLt_le L th (hW'.2 h hc hh)) hle with h' | h'
      · exact h'
      · exact absurd h' hkne
  · right
    -- The newest member of `w`'s supersession set in `K'` is not rendered.
    let S : group → Prop := fun e => K' e = true ∧ (e = w ∨ th.revisions e w x = true)
    obtain ⟨m, _, ⟨hkm, hmw'⟩, hmax⟩ := list_min_by (fun a b => KeyLt (L.key b) (L.key a))
      (fun _ _ _ h1 h2 => keyLt_trans h2 h1)
      (fun a b hab => by
        rcases keyLt_total (L.key a) (L.key b) with h | h | h
        · exact Or.inr h
        · exact absurd (L.key_injective h) hab
        · exact Or.inl h)
      S L.univ ⟨w, L.univ_complete w, hK w hkw, Or.inl rfl⟩
    have hmx : th.member m x = true := by
      rcases hmw' with rfl | hr
      · exact hmw
      · exact (ha.1.2.1 m w x (hwf m hkm).1 hr).1
    have hnotc : ¬Cand L th N K' x m := fun hc => hlive ⟨m, hc, hmw'⟩
    by_cases htm : L.tombstone m = true
    · left
      have hmne : m ≠ w := by rintro rfl; rw [hbw] at htm; cases htm
      have hr : th.revisions m w x = true := by
        rcases hmw' with h | h
        · exact absurd h hmne
        · exact h
      refine ⟨m, hkm, ?_, htm, hr⟩
      cases hk : K m
      · rfl
      · exact absurd ⟨m, hk, ancestors_of_revisions th ha hr⟩ hhw
    · right
      have htm' : L.tombstone m = false := by simpa using htm
      have : ∃ e, K' e = true ∧ th.ancestors e m = true := by
        by_contra hno
        exact hnotc ⟨⟨hkm, htm', hno⟩, hmx, htw⟩
      obtain ⟨e, hke, hem⟩ := this
      have hts : L.ts m < L.ts e := (hwf e hke).2 m hem
      have hem' : e ≠ m := by rintro rfl; exact Nat.lt_irrefl _ hts
      have hrx : th.revisions e m x = false := by
        cases hr : th.revisions e m x
        · rfl
        · have hew : th.revisions e w x = true := by
            rcases hmw' with rfl | hr'
            · exact hr
            · exact (ha.1.2.1 e m x (hwf e hke).1 hr).2.2 w hr'
          exact absurd (hmax e (L.univ_complete e) ⟨hke, Or.inr hew⟩ hem')
            (keyLt_asymm (L.key_lt_of_ts hts))
      refine ⟨e, m, hke, hkm, hmw', hem, hrx, ?_⟩
      cases hke0 : K e
      · exact Or.inl rfl
      · cases hkm0 : K m
        · exact Or.inr rfl
        · exact absurd (hold m hmw' e hke0 hkm0 hem) id

/-- A rendered declaration: its ID, its rendered names, and its dependency and
snapshot data, which are keyed by group ID. -/
structure RenderedDecl where
  id : group
  names : name → name
  deps : group → Bool
  inSnapshot : snapshot → Bool

def renderDecl (K : group → Bool) (d : group) : RenderedDecl (group := group) (name := name)
    (snapshot := snapshot) :=
  ⟨d, renamed L th N K d, th.deps d, fun S => th.contents S d⟩

/-- **Dependencies are by ID** (definitional). The model has no source text: a
rendered declaration carries its ID and pinned dependency IDs, and renaming only
changes the `names` field. -/
theorem rename_preserves_deps (K K' : group → Bool) (d : group) :
    (renderDecl L th N K d).id = (renderDecl L th N K' d).id ∧
    (renderDecl L th N K d).deps = th.deps d ∧
    (renderDecl L th N K d).deps = (renderDecl L th N K' d).deps ∧
    (renderDecl L th N K d).inSnapshot = (renderDecl L th N K' d).inSnapshot :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The rendered view of every file: the render with rendered names. A pure
function of the known set. -/
def View (K : group → Bool) : file → List (RenderedDecl (group := group) (name := name)
    (snapshot := snapshot)) :=
  fun f => (render L th K f).map (renderDecl L th N K)

/-! ## Records carry their positions

Rendering and naming consult, for each known group, only data its own record
carries: file, key, tombstone flag, the IDs of its revision ancestors, its names,
its pinned dependency IDs, the anchor path of its lineage root and its lineage
key per name. The last two are computed by the author at staging (from groups it
knows or has pending) and stored in the record. A reader therefore never reads an
unknown anchor or ancestor, although Groups' `receive` is not causal. -/

/-- The data a record of `d` carries. -/
structure Carried (group name file : Type) where
  file : file
  key : Key
  rootPath : List Key
  tomb : Bool
  anc : group → Bool
  mem : name → Bool
  lineKey : name → Key
  deps : group → Bool

def carried (d : group) : Carried group name file :=
  ⟨L.fileOf d, L.key d, L.path (root L th d), L.tombstone d, th.ancestors d, th.member d,
    fun x => lkey L th x d, th.deps d⟩

/-- The render order compares carried root paths, then keys. -/
theorem posLt_iff_paths (d e : group) :
    PosLt L th d e ↔ PathLt (L.path (root L th d)) (L.path (root L th e)) ∨
      (L.path (root L th d) = L.path (root L th e) ∧ KeyLt (L.key d) (L.key e)) := by
  unfold PosLt Layout.Prec
  constructor
  · rintro (h | ⟨h, k⟩)
    · exact Or.inl h
    · exact Or.inr ⟨by rw [h], k⟩
  · rintro (h | ⟨h, k⟩)
    · exact Or.inl h
    · exact Or.inr ⟨L.path_inj h, k⟩

/-- The winner order compares carried lineage keys, then keys. -/
theorem linLt_iff_keys (x : name) (d e : group) :
    LinLt L th x d e ↔ KeyLt (lkey L th x d) (lkey L th x e) ∨
      (lkey L th x d = lkey L th x e ∧ KeyLt (L.key d) (L.key e)) := by
  unfold LinLt
  rw [lroot_eq_iff]

end

section Locality
variable {node group name snapshot file : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]
variable (L L' : Layout node group file) (th th' : Theory node group name snapshot)
  (K : group → Bool)

/-- Two layouts and theories agree on every record of `K`. They may differ
arbitrarily on groups outside `K`, including unknown anchors and ancestors. -/
def AgreeOn : Prop := ∀ d, K d = true → carried L th d = carried L' th' d

variable {L L' th th' K}

theorem live_carried (h : AgreeOn L L' th th' K) (d : group) :
    Live L th K d ↔ Live L' th' K d := by
  unfold Live
  constructor
  · rintro ⟨hk, ht, hs⟩
    have hd := h d hk
    refine ⟨hk, by have := congrArg Carried.tomb hd; simp [carried] at this; rw [← this]; exact ht,
      fun ⟨e, he, hed⟩ => hs ⟨e, he, ?_⟩⟩
    have := congrArg Carried.anc (h e he); simp [carried] at this; rw [this]; exact hed
  · rintro ⟨hk, ht, hs⟩
    have hd := h d hk
    refine ⟨hk, by have := congrArg Carried.tomb hd; simp [carried] at this; rw [this]; exact ht,
      fun ⟨e, he, hed⟩ => hs ⟨e, he, ?_⟩⟩
    have := congrArg Carried.anc (h e he); simp [carried] at this; rw [← this]; exact hed

theorem posLt_carried (h : AgreeOn L L' th th' K) {d e : group} (hd : K d = true)
    (he : K e = true) : PosLt L th d e ↔ PosLt L' th' d e := by
  have h1 := h d hd
  have h2 := h e he
  simp only [carried, Carried.mk.injEq] at h1 h2
  rw [posLt_iff_paths, posLt_iff_paths, h1.2.2.1, h2.2.2.1, h1.2.1, h2.2.1]

/-- **Rendering reads only known records.** If two layouts and theories agree on
the carried records of the known set `K`, they render `K` identically, whatever
they say about groups outside `K`. -/
theorem render_carried (h : AgreeOn L L' th th' K) (f : file) :
    render L th K f = render L' th' K f := by
  refine (render_unique L th K f _ ?_ (fun d => ?_)).symm
  · refine (render_pairwise L' th' K f).imp_of_mem (fun ha hb hab => ?_)
    have ka := ((render_mem L' th' K f _).1 ha).1.1
    have kb := ((render_mem L' th' K f _).1 hb).1.1
    exact (posLt_carried h ka kb).2 hab
  · rw [render_mem]
    constructor
    · rintro ⟨hl, hf⟩
      have := congrArg Carried.file (h d hl.1); simp [carried] at this
      exact ⟨(live_carried h d).2 hl, this ▸ hf⟩
    · rintro ⟨hl, hf⟩
      have := congrArg Carried.file (h d hl.1); simp [carried] at this
      exact ⟨(live_carried h d).1 hl, this ▸ hf⟩

theorem cand_carried (h : AgreeOn L L' th th' K) (N : Naming th) (N' : Naming th')
    (hT : N.isTarget = N'.isTarget) (x : name) (d : group) :
    Cand L th N K x d ↔ Cand L' th' N' K x d := by
  unfold Cand
  rw [hT]
  constructor
  · rintro ⟨hl, hm, ht⟩
    have := congrArg Carried.mem (h d hl.1); simp [carried] at this
    exact ⟨(live_carried h d).1 hl, this x ▸ hm, ht⟩
  · rintro ⟨hl, hm, ht⟩
    have := congrArg Carried.mem (h d hl.1); simp [carried] at this
    exact ⟨(live_carried h d).2 hl, (this x).symm ▸ hm, ht⟩

theorem linLt_carried (h : AgreeOn L L' th th' K) {d e : group} (hd : K d = true)
    (he : K e = true) (x : name) : LinLt L th x d e ↔ LinLt L' th' x d e := by
  have h1 := h d hd
  have h2 := h e he
  simp only [carried, Carried.mk.injEq] at h1 h2
  have k1 := congrFun h1.2.2.2.2.2.2.1 x
  have k2 := congrFun h2.2.2.2.2.2.2.1 x
  rw [linLt_iff_keys, linLt_iff_keys, k1, k2, h1.2.1, h2.2.1]

/-- **Names read only known records.** -/
theorem renamed_carried (h : AgreeOn L L' th th' K) (N : Naming th) (N' : Naming th')
    (hT : N.isTarget = N'.isTarget) (hF : N.fresh = N'.fresh) (d : group) (x : name) :
    renamed L th N K d x = renamed L' th' N' K d x := by
  have hw : ∀ w, IsWinner L th N K x w ↔ IsWinner L' th' N' K x w := by
    intro w
    unfold IsWinner
    constructor
    · rintro ⟨hc, hmin⟩
      refine ⟨(cand_carried h N N' hT x w).1 hc, fun c hc' hne => ?_⟩
      have hcc := (cand_carried h N N' hT x c).2 hc'
      exact (linLt_carried h hc.1.1 hcc.1.1 x).1 (hmin c hcc hne)
    · rintro ⟨hc, hmin⟩
      refine ⟨(cand_carried h N N' hT x w).2 hc, fun c hc' hne => ?_⟩
      have hcc := (cand_carried h N N' hT x c).1 hc'
      exact (linLt_carried h hc.1.1 hcc.1.1 x).2 (hmin c hcc hne)
  have hwin : winner L th N K x = winner L' th' N' K x := by
    cases h1 : winner L th N K x with
    | some w =>
      exact ((winner_eq_some L' th' N' K x w).2 ((hw w).1 ((winner_eq_some L th N K x w).1 h1))).symm
    | none =>
      cases h2 : winner L' th' N' K x with
      | none => rfl
      | some w =>
        have := (winner_eq_some L th N K x w).2 ((hw w).2 ((winner_eq_some L' th' N' K x w).1 h2))
        rw [h1] at this; cases this
  unfold renamed
  rw [hwin, hT, hF]

/-- **The rendered view reads only known records** (given the same snapshot
membership, which is registry data, not placement data). -/
theorem view_carried (h : AgreeOn L L' th th' K) (N : Naming th) (N' : Naming th')
    (hT : N.isTarget = N'.isTarget) (hF : N.fresh = N'.fresh) (hC : th.contents = th'.contents)
    (f : file) : View L th N K f = View L' th' N' K f := by
  unfold View
  rw [render_carried h f]
  refine List.map_congr_left (fun d hd => ?_)
  have hk := ((render_mem L' th' K f d).1 hd).1.1
  have hdeps := congrArg Carried.deps (h d hk)
  simp only [carried] at hdeps
  simp only [renderDecl, hdeps, hC, RenderedDecl.mk.injEq, true_and, and_true]
  funext x
  exact renamed_carried h N N' hT hF d x

end Locality

noncomputable section
attribute [local instance] Classical.propDecidable
variable {node group name snapshot file : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]
variable (L : Layout node group file) (th : Theory node group name snapshot) (N : Naming th)

/-! ## Eventual identity -/

structure Trace where
  state : Nat → CanonicalState node group name snapshot
  initial : Reachable L th (state 0)
  next : ∀ t, state (t + 1) = state t ∨ Next L th (state t) (state (t + 1))

variable {L th}

def Trace.toGroups (tr : Trace L th) : ParaleanGroups.Trace th where
  state := tr.state
  initial := reachable_groups L th tr.initial
  next t := by
    rcases tr.next t with he | ⟨⟨l, ht⟩, _⟩
    · exact Or.inl he
    · exact Or.inr ⟨l, ht⟩

/-- Receive steps create no pending bit, so the guard never blocks them and the
registry's receive fairness applies unchanged. -/
theorem receive_guard (s t : CanonicalState node group name snapshot) (n : node) (d : group)
    (h : ReceiveStep th s t n d) : Guard L th s t := by
  simp only [ReceiveStep, receive.ext.tr] at h
  dsimp [getFrom, setIn, instIsSubStateOfRefl, Veil.FieldRepresentation.get,
    canonicalFieldRep, Veil.canonicalFieldRepresentation] at h
  rcases h with ⟨_, _, _, _, rfl⟩
  apply guard_of_no_new_pending
  · intro m
    simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp]
  · exact fun _ h => h

/-- **Eventually identical** (a corollary of Groups' index convergence, since
`View` is a function of the known set). -/
theorem eventually_identical (tr : Trace L th) (ha : TheoryAssumptions th)
    (hf : tr.toGroups.HealFair) (rf : tr.toGroups.ReceiveFair)
    (nodes : List node) (allNodes : ∀ n, n ∈ nodes) :
    ParaleanConvergence.EventuallyAlways (fun t => ∀ n m,
      View L th N ((tr.state t).known n) = View L th N ((tr.state t).known m) ∧
      View L th N ((tr.state t).known n) = View L th N (tr.state t).published ∧
      renamed L th N ((tr.state t).known n) = renamed L th N ((tr.state t).known m)) := by
  obtain ⟨cutoff, hc⟩ := tr.toGroups.index_convergence ha hf rf nodes L.univ allNodes
    L.univ_complete
  refine ⟨cutoff, fun t ht n m => ?_⟩
  have hn : (tr.state t).known n = (tr.state t).published := hc t ht n
  have hm : (tr.state t).known m = (tr.state t).published := hc t ht m
  refine ⟨by rw [hn, hm], by rw [hn], by rw [hn, hm]⟩

end

/-! ## Concrete trace -/

namespace Example
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Nodes `false` (A) and `true` (B). Group 0 (by A) is the file's first
declaration and declares name 1. Groups 1 (by A) and 2 (by B) are concurrent
inserts after 0, both declaring name 0 and depending on 0. Group 3 (by A) later
revises 1 for name 0 and also depends on 0. -/
def exTheory : Theory Bool (Fin 4) Nat Bool where
  valid := fun _ => true
  deps := fun d e => decide (d ≠ 0 ∧ e = 0)
  ancestors := fun g a => decide (g = 3 ∧ a = 1)
  member := fun d x => decide ((d = 0 ∧ x = 1) ∨ (d ≠ 0 ∧ x = 0))
  revisions := fun g a x => decide (g = 3 ∧ a = 1 ∧ x = 0)
  contents := fun _ _ => false
  exportable := fun _ => true
  emptySnapshot := false

def exLayout : Layout Bool (Fin 4) Unit where
  fileOf := fun _ => ()
  anchor := fun d => if d = 1 ∨ d = 2 then some 0 else none
  ts := fun d => if d = 0 then 1 else if d = 3 then 3 else 2
  author := fun d => decide (d = 2)
  tie := fun b => if b then 1 else 0
  tie_inj := by decide
  key_inj := by decide
  tombstone := fun _ => false
  univ := [0, 1, 2, 3]
  univ_complete := by decide
  univ_nodup := by decide

def exNaming : Naming exTheory where
  isTarget := fun _ => False
  declared := fun d x => exTheory.member d x = true
  env := fun y => y % 2 = 1 ∧ 3 ≤ y
  member_declared := fun _ _ h => h
  fresh := fun x d => 2 * (2 + 4 * x + d.val)
  fresh_inj := by
    intro x y d e h
    have hd := d.isLt; have he := e.isLt
    have hx : x = y := by omega
    subst hx
    exact ⟨rfl, Fin.ext (by omega)⟩
  reserved := fun y => y % 2 = 0 ∧ 4 ≤ y
  fresh_reserved := fun x d => ⟨by omega, by omega⟩
  env_unreserved := by
    intro y ⟨h1, _⟩ ⟨h3, _⟩
    omega

def st (pub : Fin 4 → Bool) (kn pe : Bool → Fin 4 → Bool) (c : Nat) (rk : Fin 4 → Nat) :
    CanonicalState Bool (Fin 4) Nat Bool where
  published := pub
  known := kn
  pending := pe
  head := fun _ => false
  alive := fun _ => true
  online := fun _ => true
  stable := false
  clock := c
  rank := rk

/-- A = `false`, B = `true`. -/
def s0 := st (fun _ => false) (fun _ _ => false) (fun _ _ => false) 0 (fun _ => 0)
def s1 := st (fun _ => false) (fun _ _ => false) (fun n d => decide (n = false ∧ d = 0)) 0
  (fun _ => 0)
def s2 := st (fun d => decide (d = 0)) (fun n d => decide (n = false ∧ d = 0))
  (fun _ _ => false) 1 (fun _ => 0)
def s3 := st (fun d => decide (d = 0)) (fun _ d => decide (d = 0)) (fun _ _ => false) 1
  (fun _ => 0)
def s4 := st (fun d => decide (d = 0)) (fun _ d => decide (d = 0))
  (fun n d => decide (n = false ∧ d = 1)) 1 (fun _ => 0)
def s5 := st (fun d => decide (d = 0)) (fun _ d => decide (d = 0))
  (fun n d => decide ((n = false ∧ d = 1) ∨ (n = true ∧ d = 2))) 1 (fun _ => 0)
def s6 := st (fun d => decide (d = 0 ∨ d = 1)) (fun n d => decide (d = 0 ∨ (n = false ∧ d = 1)))
  (fun n d => decide (n = true ∧ d = 2)) 2 (fun d => if d = 1 then 1 else 0)
def s7 := st (fun d => decide (d ≠ 3))
  (fun n d => decide (d = 0 ∨ (n = false ∧ d = 1) ∨ (n = true ∧ d = 2)))
  (fun _ _ => false) 3 (fun d => if d = 3 then 0 else d.val)
def s8 := st (fun d => decide (d ≠ 3)) (fun n d => decide ((n = false ∨ d ≠ 1) ∧ d ≠ 3))
  (fun _ _ => false) 3 (fun d => if d = 3 then 0 else d.val)
def s9 := st (fun d => decide (d ≠ 3)) (fun _ d => decide (d ≠ 3)) (fun _ _ => false) 3
  (fun d => if d = 3 then 0 else d.val)
def s10 := st (fun d => decide (d ≠ 3)) (fun _ d => decide (d ≠ 3))
  (fun n d => decide (n = false ∧ d = 3)) 3 (fun d => if d = 3 then 0 else d.val)
def s11 := st (fun _ => true) (fun n d => decide (n = false ∨ d ≠ 3)) (fun _ _ => false) 4
  (fun d => d.val)
def s12 := st (fun _ => true) (fun _ _ => true) (fun _ _ => false) 4 (fun d => d.val)

theorem init0 : GroupsInit exTheory s0 := by
  dsimp [GroupsInit, Init, initializer.ext.tr, s0, st, exTheory, getFrom, setIn,
    readFrom, Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    canonicalFieldRep, Veil.canonicalFieldRepresentation]
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

local macro "ex_prepare" : tactic => `(tactic| (
  simp only [GroupsNext, ParaleanGroups.Next, NextAct, prepare.ext.derived_eq]
  dsimp [prepare.ext.tr, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, st, exTheory,
    getFrom, setIn, readFrom, Veil.FieldRepresentation.get, instIsSubStateOfRefl,
    instIsSubReaderOfRefl, canonicalFieldRep, Veil.canonicalFieldRepresentation]
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]
  try decide))

local macro "ex_publish" : tactic => `(tactic| (
  simp only [GroupsNext, ParaleanGroups.Next, NextAct, publish.ext.derived_eq]
  dsimp [publish.ext.tr, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, st, getFrom,
    setIn, readFrom, Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    canonicalFieldRep, Veil.canonicalFieldRepresentation]
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]
  try decide))

local macro "ex_receive" : tactic => `(tactic| (
  simp only [GroupsNext, ParaleanGroups.Next, NextAct, receive.ext.derived_eq]
  dsimp [receive.ext.tr, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, st, getFrom,
    setIn, readFrom, Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    canonicalFieldRep, Veil.canonicalFieldRepresentation]
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]
  try decide))

theorem step1 : GroupsNext exTheory s0 (.prepare false 0) s1 := by ex_prepare
theorem step2 : GroupsNext exTheory s1 (.publish false 0) s2 := by ex_publish
theorem step3 : GroupsNext exTheory s2 (.receive true 0) s3 := by ex_receive
theorem step4 : GroupsNext exTheory s3 (.prepare false 1) s4 := by ex_prepare
theorem step5 : GroupsNext exTheory s4 (.prepare true 2) s5 := by ex_prepare
theorem step6 : GroupsNext exTheory s5 (.publish false 1) s6 := by ex_publish
theorem step7 : GroupsNext exTheory s6 (.publish true 2) s7 := by ex_publish
theorem step8 : GroupsNext exTheory s7 (.receive false 2) s8 := by ex_receive
theorem step9 : GroupsNext exTheory s8 (.receive true 1) s9 := by ex_receive
theorem step10 : GroupsNext exTheory s9 (.prepare false 3) s10 := by ex_prepare
theorem step11 : GroupsNext exTheory s10 (.publish false 3) s11 := by ex_publish
theorem step12 : GroupsNext exTheory s11 (.receive true 3) s12 := by ex_receive

/-! Positions. -/

theorem root_of_fresh (d : Fin 4) (h : d ≠ 3) : root exLayout exTheory d = d :=
  root_fresh exLayout exTheory d (fun a => by simp [exTheory, h])

theorem root3 : root exLayout exTheory 3 = 1 := by
  rw [revision_root exLayout exTheory 3 1 (fun a => by simp [exTheory]) (by decide)]
  exact root_of_fresh 1 (by decide)

theorem path0 : exLayout.path 0 = [(1, 0)] := by
  rw [Layout.path_none exLayout (by decide)]; decide
theorem path1 : exLayout.path 1 = [(1, 0), (2, 0)] := by
  rw [Layout.path_some exLayout (a := 0) (by decide) (by decide), path0]; decide
theorem path2 : exLayout.path 2 = [(1, 0), (2, 1)] := by
  rw [Layout.path_some exLayout (a := 0) (by decide) (by decide), path0]; decide

theorem pos01 : PosLt exLayout exTheory 0 1 := by
  left; rw [root_of_fresh 0 (by decide), root_of_fresh 1 (by decide)]
  simp [Layout.Prec, path0, path1, PathLt]
theorem pos02 : PosLt exLayout exTheory 0 2 := by
  left; rw [root_of_fresh 0 (by decide), root_of_fresh 2 (by decide)]
  simp [Layout.Prec, path0, path2, PathLt]
theorem pos03 : PosLt exLayout exTheory 0 3 := by
  left; rw [root_of_fresh 0 (by decide), root3]
  simp [Layout.Prec, path0, path1, PathLt]
/-- The revision 3 renders in 1's place, which is below B's newer sibling 2. -/
theorem pos23 : PosLt exLayout exTheory 2 3 := by
  left; rw [root_of_fresh 2 (by decide), root3]
  simp [Layout.Prec, path1, path2, PathLt, KeyLt]

/-! Guards. -/

theorem guard_single {s t : CanonicalState Bool (Fin 4) Nat Bool} (n0 : Bool) (d0 : Fin 4)
    (h : ∀ n d, t.pending n d = true → s.pending n d = false → n = n0 ∧ d = d0)
    (hs : Staged exLayout exTheory s n0 d0)
    (hp : ∀ d, t.published d = true → s.published d = true) : Guard exLayout exTheory s t := by
  refine ⟨fun n d h1 h2 => ?_, publishGuard_of_no_new_published _ _ _ hp⟩
  obtain ⟨rfl, rfl⟩ := h n d h1 h2
  exact hs

local macro "ex_noguard" : tactic => `(tactic| (
  refine ⟨?_, ?_⟩
  · apply stageGuard_of_no_new_pending
    intro n d
    simp [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, st]
    try (revert n d; decide)
  · unfold PublishGuard
    simp [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, st, exLayout]
    try decide))

local macro "ex_nopub" : tactic => `(tactic| (
  intro d
  simp [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, st]))

local macro "ex_single" : tactic => `(tactic| (
  intro n d
  simp [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, st]
  try (revert n d; decide)))

local macro "ex_staged" : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, st, exLayout, exTheory]; done)
  all_goals try decide))

theorem guard1 : Guard exLayout exTheory s0 s1 :=
  guard_single false 0 (by ex_single) (by
    ex_staged) (by ex_nopub)
theorem guard2 : Guard exLayout exTheory s1 s2 := by ex_noguard
theorem guard3 : Guard exLayout exTheory s2 s3 := by ex_noguard
theorem guard4 : Guard exLayout exTheory s3 s4 :=
  guard_single false 1 (by ex_single) (by
    ex_staged
    intro e he _; simp [exTheory] at he; rw [he]; exact pos01) (by ex_nopub)
theorem guard5 : Guard exLayout exTheory s4 s5 :=
  guard_single true 2 (by ex_single) (by
    ex_staged
    intro e he _; simp [exTheory] at he; rw [he]; exact pos02) (by ex_nopub)
theorem guard6 : Guard exLayout exTheory s5 s6 := by ex_noguard
theorem guard7 : Guard exLayout exTheory s6 s7 := by ex_noguard
theorem guard8 : Guard exLayout exTheory s7 s8 := by ex_noguard
theorem guard9 : Guard exLayout exTheory s8 s9 := by ex_noguard
theorem guard10 : Guard exLayout exTheory s9 s10 :=
  guard_single false 3 (by ex_single) (by
    ex_staged
    intro e he _; simp [exTheory] at he; rw [he]; exact pos03) (by ex_nopub)
theorem guard11 : Guard exLayout exTheory s10 s11 := by ex_noguard
theorem guard12 : Guard exLayout exTheory s11 s12 := by ex_noguard

theorem r1 : Reachable exLayout exTheory s1 :=
  Reachable.step (Reachable.initial init0) ⟨⟨_, step1⟩, guard1⟩
theorem r2 : Reachable exLayout exTheory s2 := Reachable.step r1 ⟨⟨_, step2⟩, guard2⟩
theorem r3 : Reachable exLayout exTheory s3 := Reachable.step r2 ⟨⟨_, step3⟩, guard3⟩
theorem r4 : Reachable exLayout exTheory s4 := Reachable.step r3 ⟨⟨_, step4⟩, guard4⟩
theorem r5 : Reachable exLayout exTheory s5 := Reachable.step r4 ⟨⟨_, step5⟩, guard5⟩
theorem r6 : Reachable exLayout exTheory s6 := Reachable.step r5 ⟨⟨_, step6⟩, guard6⟩
theorem r7 : Reachable exLayout exTheory s7 := Reachable.step r6 ⟨⟨_, step7⟩, guard7⟩
theorem r8 : Reachable exLayout exTheory s8 := Reachable.step r7 ⟨⟨_, step8⟩, guard8⟩
theorem r9 : Reachable exLayout exTheory s9 := Reachable.step r8 ⟨⟨_, step9⟩, guard9⟩
theorem r10 : Reachable exLayout exTheory s10 := Reachable.step r9 ⟨⟨_, step10⟩, guard10⟩
theorem r11 : Reachable exLayout exTheory s11 := Reachable.step r10 ⟨⟨_, step11⟩, guard11⟩
theorem ex_reachable : Reachable exLayout exTheory s12 :=
  Reachable.step r11 ⟨⟨_, step12⟩, guard12⟩

theorem ex_assumptions : TheoryAssumptions exTheory := by
  simp only [TheoryAssumptions, Assumptions]
  refine ⟨?_, ?_, ?_⟩
  · simp only [valid_ancestry, exTheory, readFrom, instIsSubReaderOfRefl]
    refine ⟨fun g a => ?_, fun g a x _ h => ?_, fun g _ => ⟨if g = 0 then 1 else 0, ?_⟩⟩
    · simp
    · simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp
    · by_cases hg : g = 0 <;> simp [hg]
  · simp [empty_contents, exTheory, readFrom, instIsSubReaderOfRefl]
  · simp [empty_exportable, exTheory, readFrom, instIsSubReaderOfRefl]

/-! Renders. -/

theorem final_live (n : Bool) (d : Fin 4) :
    Live exLayout exTheory (s12.known n) d ↔ d ≠ 1 := by
  simp [Live, s12, st, exLayout, exTheory]

/-- Both nodes render `[0, 2, 3]`: the revision 3 replaces 1 in 1's position,
below B's later-keyed sibling 2. -/
theorem final_render (n : Bool) : render exLayout exTheory (s12.known n) () = [0, 2, 3] :=
  (render_unique exLayout exTheory _ () _
    (by simp [pos02, pos03, pos23])
    (fun d => by rw [final_live]; simp; revert d; decide)).symm

theorem final_identical :
    render exLayout exTheory (s12.known false) () = render exLayout exTheory (s12.known true) () := by
  rw [final_render, final_render]

/-- Groups newly known by `n` across one transition. -/
def arrivals (s t : CanonicalState Bool (Fin 4) Nat Bool) (n : Bool) : List (Fin 4) :=
  [0, 1, 2, 3].filter (fun d => t.known n d && !s.known n d)

def exTrace : List (CanonicalState Bool (Fin 4) Nat Bool) :=
  [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12]

/-- The order in which `n` learned groups along the trace. -/
def arrivalLog (n : Bool) : List (Fin 4) :=
  (exTrace.zip exTrace.tail).flatMap (fun p => arrivals p.1 p.2 n)

theorem arrival_orders : arrivalLog false = [0, 1, 2, 3] ∧ arrivalLog true = [0, 2, 1, 3] := by
  decide

/-- **Guard necessity.** Rendering by arrival order (append on receive) diverges on
this trace although both nodes know the same set. -/
theorem arrival_render_diverges :
    s12.known false = s12.known true ∧ arrivalLog false ≠ arrivalLog true := by
  refine ⟨rfl, ?_⟩
  rw [arrival_orders.1, arrival_orders.2]; decide

/-! Names. -/

theorem lroot_of_fresh (d : Fin 4) (h : d ≠ 3) : lroot exLayout exTheory 0 d = d :=
  lroot_self exLayout exTheory 0 d (fun a => by simp [exTheory, h])

theorem lroot3 : lroot exLayout exTheory 0 3 = 1 :=
  exLayout.minOf_eq ⟨Or.inr (by decide), fun c hc hc1 => by
    rcases hc with rfl | hc
    · simp [Layout.key, exLayout, KeyLt]
    · simp [exTheory] at hc; exact absurd hc hc1⟩

theorem lin12 : LinLt exLayout exTheory 0 1 2 := by
  left; unfold lkey; rw [lroot_of_fresh 1 (by decide), lroot_of_fresh 2 (by decide)]
  simp [Layout.key, exLayout, KeyLt]

theorem lin32 : LinLt exLayout exTheory 0 3 2 := by
  left; unfold lkey; rw [lroot3, lroot_of_fresh 2 (by decide)]
  simp [Layout.key, exLayout, KeyLt]

/-- Before the revision: groups 1 and 2 both declare name 0 and neither revises
the other. Group 1 has the smaller lineage key and keeps the name; group 2
renders as `fresh 0 2 = 8`. -/
theorem collision_resolved (n : Bool) :
    winner exLayout exTheory exNaming (s9.known n) 0 = some 1 ∧
    renamed exLayout exTheory exNaming (s9.known n) 1 0 = 0 ∧
    renamed exLayout exTheory exNaming (s9.known n) 2 0 = 8 := by
  have hw : winner exLayout exTheory exNaming (s9.known n) 0 = some 1 := by
    rw [winner_eq_some]
    refine ⟨?_, ?_⟩
    · simp [Cand, Live, s9, st, exTheory, exNaming, exLayout]
    · intro c hc hne
      simp [Cand, Live, s9, st, exTheory, exNaming, exLayout] at hc
      have hc2 : c = 2 := by revert c hne hc; decide
      subst hc2; exact lin12
  refine ⟨hw, ?_, ?_⟩
  · simp [renamed, hw]
  · rw [renamed, hw]; simp [exNaming]

/-- **Revising the winner keeps the name.** After A revises the winner 1 with 3,
the winner of name 0 is 3 (lineage root 1), and 2 still renders as `fresh 0 2`.
The rule "least own key among heads" would instead hand the name to 2, since
2's key `(2, 1)` is below 3's `(3, 0)`. -/
theorem revised_winner_keeps_name (n : Bool) :
    winner exLayout exTheory exNaming (s12.known n) 0 = some 3 ∧
    renamed exLayout exTheory exNaming (s12.known n) 3 0 = 0 ∧
    renamed exLayout exTheory exNaming (s12.known n) 2 0 = 8 ∧
    KeyLt (exLayout.key 2) (exLayout.key 3) := by
  have hw : winner exLayout exTheory exNaming (s12.known n) 0 = some 3 := by
    rw [winner_eq_some]
    refine ⟨?_, ?_⟩
    · simp [Cand, Live, s12, st, exTheory, exNaming, exLayout]
    · intro c hc hne
      simp [Cand, Live, s12, st, exTheory, exNaming, exLayout] at hc
      have hc2 : c = 2 := by revert c hne hc; decide
      subst hc2; exact lin32
  refine ⟨hw, ?_, ?_, ?_⟩
  · simp [renamed, hw]
  · rw [renamed, hw]; simp [exNaming]
  · simp [Layout.key, exLayout, KeyLt]

/-- The guard is exercised positively: B stages 2 with known anchor 0, and 0
precedes 2 in B's render of its known set plus 2. -/
theorem stage_follows_anchor :
    Precedes (render exLayout exTheory (insertK (s4.known true) 2) ()) 0 2 :=
  (insert_after_anchor exLayout exTheory ex_assumptions r4 ⟨⟨_, step5⟩, guard5⟩ true 2
    (by simp [s5, st]) (by simp [s4, st]) (fun b => by simp [exTheory]) rfl 0
    ((render_mem _ _ _ _ _).2 ⟨⟨by simp [insertK, s4, st], rfl, by simp [exTheory]⟩, rfl⟩)
    (by decide)).2 ⟨0, rfl, Or.inl (root_of_fresh 0 (by decide))⟩

/-- The revision's same-file dependency 0 precedes it once everything is known. -/
theorem final_dep_precedes : Precedes (render exLayout exTheory s12.published ()) 0 3 :=
  deps_precede exLayout exTheory ⟨⟨_, step10⟩, guard10⟩ false 3
    (by simp [s10, st]) (by simp [s9, st]) 0 (by decide) rfl _
    ((render_mem _ _ _ _ _).2 ⟨⟨rfl, rfl, by simp [exTheory]⟩, rfl⟩)
    ((render_mem _ _ _ _ _).2 ⟨⟨rfl, rfl, by simp [exTheory]⟩, rfl⟩)

/-- **Dependency guard necessity.** Had A anchored 1 at the file start, 1 would
render above its dependency 0, and the guard rejects that staging. -/
def exTop : Layout Bool (Fin 4) Unit :=
  { exLayout with anchor := fun d => if d = 2 then some 0 else none }

theorem dep_guard_needed :
    PosLt exTop exTheory 1 0 ∧ ¬Staged exTop exTheory s3 false 1 := by
  have r0 : root exTop exTheory 0 = 0 := root_fresh _ _ 0 (fun a => by simp [exTheory])
  have r1 : root exTop exTheory 1 = 1 := root_fresh _ _ 1 (fun a => by simp [exTheory])
  have p0 : exTop.path 0 = [(1, 0)] := by
    rw [Layout.path_none exTop (by decide)]; decide
  have p1 : exTop.path 1 = [(2, 0)] := by
    rw [Layout.path_none exTop (by decide)]; decide
  have h10 : PosLt exTop exTheory 1 0 := by
    left; rw [r0, r1]; simp [Layout.Prec, p0, p1, PathLt, KeyLt]
  exact ⟨h10, fun hs => posLt_asymm _ _ h10 (hs.2.2.2.2 0 (by decide) rfl)⟩

/-- **Deletion frees the name.** With 3 a tombstone revision of 1, 3 is not
rendered, 1 stays superseded, and the name passes to 2 (the tombstone branch of
`winner_change_explained`). -/
def exDel : Layout Bool (Fin 4) Unit := { exLayout with tombstone := fun d => decide (d = 3) }

theorem delete_frees_name (n : Bool) :
    render exDel exTheory (s12.known n) () = [0, 2] ∧
    winner exDel exTheory exNaming (s12.known n) 0 = some 2 := by
  have r0 : root exDel exTheory 0 = 0 := root_fresh _ _ 0 (fun a => by simp [exTheory])
  have r2 : root exDel exTheory 2 = 2 := root_fresh _ _ 2 (fun a => by simp [exTheory])
  have p0 : exDel.path 0 = [(1, 0)] := by
    rw [Layout.path_none exDel (by decide)]; decide
  have p2 : exDel.path 2 = [(1, 0), (2, 1)] := by
    rw [Layout.path_some exDel (a := 0) (by decide) (by decide), p0]; decide
  refine ⟨(render_unique exDel exTheory _ () _ ?_ (fun d => ?_)).symm, ?_⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true, implies_true]
    refine ⟨?_, fun _ h => h.elim⟩
    left; rw [r0, r2]; simp [Layout.Prec, p0, p2, PathLt]
  · simp [Live, s12, st, exDel, exLayout, exTheory]; revert d; decide
  · rw [winner_eq_some]
    refine ⟨?_, ?_⟩
    · simp [Cand, Live, s12, st, exTheory, exNaming, exDel, exLayout]
    · intro c hc hne
      simp [Cand, Live, s12, st, exTheory, exNaming, exDel, exLayout] at hc
      revert c hne hc; decide

/-- The example's groups pass the reserved-name check. -/
theorem ex_names_checked : NamesChecked exNaming := by
  intro e y _ hy ⟨h1, h2⟩
  simp only [exNaming, exTheory, decide_eq_true_eq] at hy
  omega

/-- `exTheory` with group 0 also declaring `8 = fresh 0 2`, a reserved name. -/
def exBad : Theory Bool (Fin 4) Nat Bool :=
  { exTheory with member := fun d x => decide ((d = 0 ∧ (x = 1 ∨ x = 8)) ∨ (d ≠ 0 ∧ x = 0)) }

def exBadNaming : Naming exBad :=
  { exNaming with
    declared := fun d x => exBad.member d x = true
    member_declared := fun _ _ h => h }

/-- **Reserved-name check necessity.** If a valid group may declare a name in the
renderer's namespace, uniqueness fails: group 2 loses name 0 and renders as
`fresh 0 2 = 8`, which group 0 declares and keeps. -/
theorem reserved_check_needed (n : Bool) :
    ¬NamesChecked exBadNaming ∧
    renamed exLayout exBad exBadNaming (s9.known n) 2 0 = 8 ∧
    renamed exLayout exBad exBadNaming (s9.known n) 0 8 = 8 := by
  have l1 : lroot exLayout exBad 0 1 = 1 := lroot_self _ _ 0 1 (fun a => by simp [exBad, exTheory])
  have l2 : lroot exLayout exBad 0 2 = 2 := lroot_self _ _ 0 2 (fun a => by simp [exBad, exTheory])
  have hw0 : winner exLayout exBad exBadNaming (s9.known n) 0 = some 1 := by
    rw [winner_eq_some]
    refine ⟨?_, ?_⟩
    · simp [Cand, Live, s9, st, exBad, exTheory, exBadNaming, exNaming, exLayout]
    · intro c hc hne
      simp [Cand, Live, s9, st, exBad, exTheory, exBadNaming, exNaming, exLayout] at hc
      have hc2 : c = 2 := by revert c hne hc; decide
      subst hc2
      left; unfold lkey; rw [l1, l2]; simp [Layout.key, exLayout, KeyLt]
  have hw8 : winner exLayout exBad exBadNaming (s9.known n) 8 = some 0 := by
    rw [winner_eq_some]
    refine ⟨?_, ?_⟩
    · simp [Cand, Live, s9, st, exBad, exTheory, exBadNaming, exNaming, exLayout]
    · intro c hc hne
      simp [Cand, Live, s9, st, exBad, exTheory, exBadNaming, exNaming, exLayout] at hc
      exact absurd hc.2 hne
  refine ⟨fun hc => hc 0 8 rfl (by simp [exBadNaming, exBad]) (by simp [exBadNaming, exNaming]),
    ?_, ?_⟩
  · rw [renamed, hw0]; simp [exBadNaming, exNaming]
  · simp [renamed, hw8]

/-! Partial revision. Group 0 declares names 0 and 1; group 1 revises 0 for name 0
only; group 2 (newer than 0, older than 1) declares name 1. -/

def pTheory : Theory Bool (Fin 3) Nat Bool where
  valid := fun _ => true
  deps := fun _ _ => false
  ancestors := fun g a => decide (g = 1 ∧ a = 0)
  member := fun d x => decide ((d = 0 ∧ x ≤ 1) ∨ (d = 1 ∧ x = 0) ∨ (d = 2 ∧ x = 1))
  revisions := fun g a x => decide (g = 1 ∧ a = 0 ∧ x = 0)
  contents := fun _ _ => false
  exportable := fun _ => true
  emptySnapshot := false

def pLayout : Layout Bool (Fin 3) Unit where
  fileOf := fun _ => ()
  anchor := fun _ => none
  ts := fun d => if d = 0 then 1 else if d = 1 then 3 else 2
  author := fun _ => false
  tie := fun b => if b then 1 else 0
  tie_inj := by decide
  key_inj := by decide
  tombstone := fun _ => false
  univ := [0, 1, 2]
  univ_complete := by decide
  univ_nodup := by decide

def pNaming : Naming pTheory where
  isTarget := fun _ => False
  declared := fun d x => pTheory.member d x = true
  env := fun _ => False
  member_declared := fun _ _ h => h
  fresh := fun x d => 2 + 3 * x + d.val + 10
  fresh_inj := by
    intro x y d e h
    have hd := d.isLt; have he := e.isLt
    have hx : x = y := by omega
    subst hx
    exact ⟨rfl, Fin.ext (by omega)⟩
  reserved := fun y => 12 ≤ y
  fresh_reserved := fun x d => by omega
  env_unreserved := fun _ h => h.elim

theorem p_assumptions : TheoryAssumptions pTheory := by
  simp only [TheoryAssumptions, Assumptions]
  refine ⟨?_, ?_, ?_⟩
  · simp only [valid_ancestry, pTheory, readFrom, instIsSubReaderOfRefl]
    refine ⟨fun g a => ?_, fun g a x _ h => ?_, fun g _ => ⟨if g = 2 then 1 else 0, ?_⟩⟩
    · simp
    · simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp
    · revert g; decide
  · simp [empty_contents, pTheory, readFrom, instIsSubReaderOfRefl]
  · simp [empty_exportable, pTheory, readFrom, instIsSubReaderOfRefl]

def pK : Fin 3 → Bool := fun _ => true

theorem p_wf : WF pLayout pTheory pK := by
  intro d _
  refine ⟨rfl, fun a ha => ?_⟩
  simp [pTheory] at ha
  obtain ⟨rfl, rfl⟩ := ha
  decide

/-- The rule before hardening: a candidate for `x` need only be unrevised *for `x`*. -/
def OldCand (K : Fin 3 → Bool) (x : Nat) (d : Fin 3) : Prop :=
  K d = true ∧ pTheory.member d x = true ∧ pLayout.tombstone d = false ∧
    ¬∃ e, K e = true ∧ pTheory.revisions e d x = true

/-- **Superseded groups hold no name** (necessity of `Live` in `Cand`). Group 0
is superseded by its partial revision 1 and is not rendered. Under the old
candidate rule 0 is still a candidate for name 1 and beats 2 (its lineage key is
older), so 2 would be renamed and no rendered declaration would carry name 1.
With `Live` in `Cand`, 2 wins name 1 and keeps it. -/
theorem partial_revision_frees_name :
    ¬Live pLayout pTheory pK 0 ∧
    OldCand pK 1 0 ∧ OldCand pK 1 2 ∧ LinLt pLayout pTheory 1 0 2 ∧
    winner pLayout pTheory pNaming pK 1 = some 2 ∧
    renamed pLayout pTheory pNaming pK 2 1 = 1 := by
  have l0 : lroot pLayout pTheory 1 0 = 0 :=
    lroot_self pLayout pTheory 1 0 (fun a => by simp [pTheory])
  have l2 : lroot pLayout pTheory 1 2 = 2 :=
    lroot_self pLayout pTheory 1 2 (fun a => by simp [pTheory])
  have hw : winner pLayout pTheory pNaming pK 1 = some 2 := by
    rw [winner_eq_some]
    refine ⟨?_, ?_⟩
    · simp [Cand, Live, pK, pTheory, pNaming, pLayout]
    · intro c hc hne
      simp [Cand, Live, pK, pTheory, pNaming, pLayout] at hc
      revert c hne hc; decide
  refine ⟨?_, ?_, ?_, ?_, hw, ?_⟩
  · rintro ⟨_, _, h⟩; exact h ⟨1, rfl, by decide⟩
  · simp [OldCand, pK, pTheory, pLayout]
  · simp [OldCand, pK, pTheory, pLayout]
  · left; unfold lkey; rw [l0, l2]; simp [Layout.key, pLayout, KeyLt]
  · simp [renamed, hw]

/-! Anchoring through an own pending group. Node A publishes 0, stages 1 after 0,
and stages 2 after 1 while 1 is still pending. -/

def oTheory : Theory Bool (Fin 3) Nat Bool where
  valid := fun _ => true
  deps := fun _ _ => false
  ancestors := fun _ _ => false
  member := fun d x => decide (x = d.val)
  revisions := fun _ _ _ => false
  contents := fun _ _ => false
  exportable := fun _ => true
  emptySnapshot := false

def oLayout : Layout Bool (Fin 3) Unit where
  fileOf := fun _ => ()
  anchor := fun d => if d = 0 then none else if d = 1 then some 0 else some 1
  ts := fun d => d.val + 1
  author := fun _ => false
  tie := fun b => if b then 1 else 0
  tie_inj := by decide
  key_inj := by decide
  tombstone := fun _ => false
  univ := [0, 1, 2]
  univ_complete := by decide
  univ_nodup := by decide

def ost (pub : Fin 3 → Bool) (kn pe : Bool → Fin 3 → Bool) (c : Nat) (rk : Fin 3 → Nat) :
    CanonicalState Bool (Fin 3) Nat Bool where
  published := pub
  known := kn
  pending := pe
  head := fun _ => false
  alive := fun _ => true
  online := fun _ => true
  stable := false
  clock := c
  rank := rk

def o0 := ost (fun _ => false) (fun _ _ => false) (fun _ _ => false) 0 (fun _ => 0)
def o1 := ost (fun _ => false) (fun _ _ => false) (fun n d => decide (n = false ∧ d = 0)) 0
  (fun _ => 0)
def o2 := ost (fun d => decide (d = 0)) (fun n d => decide (n = false ∧ d = 0))
  (fun _ _ => false) 1 (fun _ => 0)
def o3 := ost (fun d => decide (d = 0)) (fun n d => decide (n = false ∧ d = 0))
  (fun n d => decide (n = false ∧ d = 1)) 1 (fun _ => 0)
def o4 := ost (fun d => decide (d = 0)) (fun n d => decide (n = false ∧ d = 0))
  (fun n d => decide (n = false ∧ d ≠ 0)) 1 (fun _ => 0)
def o5 := ost (fun d => decide (d ≠ 2)) (fun n d => decide (n = false ∧ d ≠ 2))
  (fun n d => decide (n = false ∧ d = 2)) 2 (fun d => if d = 1 then 1 else 0)
def o6 := ost (fun _ => true) (fun n _ => decide (n = false))
  (fun _ _ => false) 3 (fun d => d.val)
/-- Publishing 2 before its anchor 1. -/
def oBad := ost (fun d => decide (d ≠ 1)) (fun n d => decide (n = false ∧ d ≠ 1))
  (fun n d => decide (n = false ∧ d = 1)) 2 (fun d => if d = 2 then 1 else 0)

theorem o_init : GroupsInit oTheory o0 := by
  dsimp [GroupsInit, Init, initializer.ext.tr, o0, ost, oTheory, getFrom, setIn,
    readFrom, Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    canonicalFieldRep, Veil.canonicalFieldRepresentation]
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

local macro "o_step" act:ident : tactic => `(tactic| (
  simp only [GroupsNext, ParaleanGroups.Next, NextAct, ParaleanGroups.prepare.ext.derived_eq,
    ParaleanGroups.publish.ext.derived_eq]
  dsimp [ParaleanGroups.prepare.ext.tr, ParaleanGroups.publish.ext.tr, o0, o1, o2, o3, o4, o5, o6,
    oBad, ost, oTheory, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep,
    Veil.canonicalFieldRepresentation]
  simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]
  try decide))

theorem ostep1 : GroupsNext oTheory o0 (.prepare false 0) o1 := by o_step prepare
theorem ostep2 : GroupsNext oTheory o1 (.publish false 0) o2 := by o_step publish
theorem ostep3 : GroupsNext oTheory o2 (.prepare false 1) o3 := by o_step prepare
theorem ostep4 : GroupsNext oTheory o3 (.prepare false 2) o4 := by o_step prepare
theorem ostep5 : GroupsNext oTheory o4 (.publish false 1) o5 := by o_step publish
theorem ostep6 : GroupsNext oTheory o5 (.publish false 2) o6 := by o_step publish
theorem ostepBad : GroupsNext oTheory o4 (.publish false 2) oBad := by o_step publish

local macro "o_unfold" : tactic => `(tactic| (
  simp [o0, o1, o2, o3, o4, o5, o6, oBad, ost, oLayout, oTheory]))

theorem o_path0 : oLayout.path 0 = [(1, 0)] := by
  rw [Layout.path_none oLayout (by decide)]; decide
theorem o_path1 : oLayout.path 1 = [(1, 0), (2, 0)] := by
  rw [Layout.path_some oLayout (a := 0) (by decide) (by decide), o_path0]; decide
theorem o_path2 : oLayout.path 2 = [(1, 0), (2, 0), (3, 0)] := by
  rw [Layout.path_some oLayout (a := 1) (by decide) (by decide), o_path1]; decide

theorem o_root (d : Fin 3) : root oLayout oTheory d = d :=
  root_fresh _ _ d (fun _ => rfl)

theorem o_pos01 : PosLt oLayout oTheory 0 1 := by
  left; rw [o_root, o_root]; simp [Layout.Prec, o_path0, o_path1, PathLt]
theorem o_pos12 : PosLt oLayout oTheory 1 2 := by
  left; rw [o_root, o_root]; simp [Layout.Prec, o_path1, o_path2, PathLt]
theorem o_pos02 : PosLt oLayout oTheory 0 2 := posLt_trans _ _ o_pos01 o_pos12

local macro "o_staged" : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals try (o_unfold; done)
  all_goals try (intro a; o_unfold; try decide)
  all_goals try decide))

theorem o_guard_stage {s t : CanonicalState Bool (Fin 3) Nat Bool} (d0 : Fin 3)
    (h : ∀ n d, t.pending n d = true → s.pending n d = false → n = false ∧ d = d0)
    (hs : Staged oLayout oTheory s false d0)
    (hp : ∀ d, t.published d = true → s.published d = true) : Guard oLayout oTheory s t := by
  refine ⟨fun n d h1 h2 => ?_, publishGuard_of_no_new_published _ _ _ hp⟩
  obtain ⟨rfl, rfl⟩ := h n d h1 h2
  exact hs

local macro "o_pub" : tactic => `(tactic| (
  refine ⟨?_, ?_⟩
  · apply stageGuard_of_no_new_pending
    intro n d; o_unfold; try (revert n d; decide)
  · unfold PublishGuard; o_unfold; try decide))

theorem o_staged0 : Staged oLayout oTheory o0 false 0 := by
  refine ⟨?_, ?_, rfl, ?_, ?_⟩ <;> (intro a; o_unfold)
theorem o_staged1 : Staged oLayout oTheory o2 false 1 := by
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · intro a ha; simp [o0, o1, o2, o3, o4, o5, o6, oBad, ost, oLayout, oTheory] at ha ⊢; subst ha; decide
  · intro e he; simp [o0, o1, o2, o3, o4, o5, o6, oBad, ost, oLayout, oTheory] at he ⊢; subst he; decide
  · intro a ha; simp [o0, o1, o2, o3, o4, o5, o6, oBad, ost, oLayout, oTheory] at ha
  · intro e he; simp [o0, o1, o2, o3, o4, o5, o6, oBad, ost, oLayout, oTheory] at he
/-- 2 is anchored at A's own pending group 1, which A does not know yet. -/
theorem o_staged2 : Staged oLayout oTheory o3 false 2 := by
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · intro a ha; simp [o0, o1, o2, o3, o4, o5, o6, oBad, ost, oLayout, oTheory] at ha ⊢; subst ha; decide
  · intro e he; simp [o0, o1, o2, o3, o4, o5, o6, oBad, ost, oLayout, oTheory] at he ⊢; rcases he with rfl | rfl <;> decide
  · intro a ha; simp [o0, o1, o2, o3, o4, o5, o6, oBad, ost, oLayout, oTheory] at ha
  · intro e he; simp [o0, o1, o2, o3, o4, o5, o6, oBad, ost, oLayout, oTheory] at he

theorem o_r1 : Reachable oLayout oTheory o1 :=
  .step (.initial o_init) ⟨⟨_, ostep1⟩,
    o_guard_stage 0 (by intro n d; o_unfold) o_staged0 (by intro d; o_unfold)⟩
theorem o_r2 : Reachable oLayout oTheory o2 := .step o_r1 ⟨⟨_, ostep2⟩, by o_pub⟩
theorem o_r3 : Reachable oLayout oTheory o3 :=
  .step o_r2 ⟨⟨_, ostep3⟩,
    o_guard_stage 1 (by intro n d; o_unfold) o_staged1 (by intro d; o_unfold)⟩
theorem o_r4 : Reachable oLayout oTheory o4 :=
  .step o_r3 ⟨⟨_, ostep4⟩,
    o_guard_stage 2 (by intro n d; o_unfold; try (revert n d; decide)) o_staged2 (by intro d; o_unfold)⟩
theorem o_r5 : Reachable oLayout oTheory o5 := .step o_r4 ⟨⟨_, ostep5⟩, by o_pub⟩
theorem o_r6 : Reachable oLayout oTheory o6 := .step o_r5 ⟨⟨_, ostep6⟩, by o_pub⟩

theorem o_assumptions : TheoryAssumptions oTheory := by
  simp only [TheoryAssumptions, Assumptions]
  refine ⟨?_, ?_, ?_⟩
  · simp only [valid_ancestry, oTheory, readFrom, instIsSubReaderOfRefl]
    refine ⟨fun g a => ?_, fun g a x _ h => ?_, fun g _ => ⟨g.val, ?_⟩⟩
    · simp
    · simp at h
    · simp
  · simp [empty_contents, oTheory, readFrom, instIsSubReaderOfRefl]
  · simp [empty_exportable, oTheory, readFrom, instIsSubReaderOfRefl]

/-- **Anchoring through an own pending group.** A stages 1 after 0 and then 2 after
1 while 1 is only pending. The staging guard before this fix (anchor known)
rejects 2's staging at `o3`, so A could only anchor 2 at 0, where the newer
sibling 2 renders above 1 (`[0, 2, 1]`). With the fix the final render is
`[0, 1, 2]`, and `intention_preserved` places 1 above 2 in every render showing
both. -/
theorem own_pending_anchor :
    o3.known false 1 = false ∧ o3.pending false 1 = true ∧
    Staged oLayout oTheory o3 false 2 ∧
    render oLayout oTheory o6.published () = [0, 1, 2] ∧
    (∀ K', 1 ∈ render oLayout oTheory K' () → 2 ∈ render oLayout oTheory K' () →
      Precedes (render oLayout oTheory K' ()) 1 2) := by
  refine ⟨rfl, rfl, o_staged2, ?_, fun K' h1 h2 => ?_⟩
  · exact (render_unique oLayout oTheory _ () _ (by simp [o_pos01, o_pos02, o_pos12])
      (fun d => by simp [Live, o6, ost, oLayout, oTheory]; revert d; decide)).symm
  · exact (intention_preserved oLayout oTheory o_assumptions o_r3 ⟨⟨_, ostep4⟩,
      o_guard_stage 2 (by intro n d; o_unfold; try (revert n d; decide)) o_staged2 (by intro d; o_unfold)⟩
      false 2 rfl rfl (fun _ => rfl) 1 (Or.inr rfl) K' h1 h2).1 ⟨1, rfl, Or.inl (o_root 1)⟩

/-- **Publication guard necessity.** From `o4` (1 and 2 both pending at A), the
registry can publish 2 before its anchor 1. That step adds no pending bit, so the
staging guard alone accepts it, but `PublishGuard` rejects it, and the published
2 would have an unpublished anchor (breaking `anchor_closed`). -/
theorem publish_guard_needed :
    Reachable oLayout oTheory o4 ∧ GroupsNext oTheory o4 (.publish false 2) oBad ∧
    StageGuard oLayout oTheory o4 oBad ∧ ¬PublishGuard oLayout o4 oBad ∧
    oBad.published 2 = true ∧ oLayout.anchor 2 = some 1 ∧ oBad.published 1 = false := by
  refine ⟨o_r4, ostepBad, ?_, ?_, rfl, rfl, rfl⟩
  · apply stageGuard_of_no_new_pending; intro n d; o_unfold; revert n d; decide
  · intro h
    have := h false 2 rfl rfl rfl 1 rfl
    simp [o4, ost] at this

/-! Reading an unknown anchor. 1 is anchored at 0; 2 is at the file start; a
node knows 1 and 2 but not 0 (Groups' `receive` is not causal). -/

def uA : Layout Bool (Fin 3) Unit :=
  { oLayout with
    anchor := fun d => if d = 1 then some 0 else none
    ts := fun d => if d = 0 then 1 else if d = 1 then 3 else 2
    key_inj := by decide }

/-- `uA` with a different key for the unknown group 0 only. -/
def uB : Layout Bool (Fin 3) Unit :=
  { uA with
    ts := fun d => if d = 0 then 2 else if d = 1 then 3 else 2
    author := fun d => decide (d = 0)
    key_inj := by decide }

def uK : Fin 3 → Bool := fun d => decide (d ≠ 0)

/-- **Records must carry the root path** (necessity for `render_carried`). `uA` and
`uB` agree on every own field (file, anchor ID, key, tombstone) of the known
groups 1 and 2 and differ only on the unknown anchor 0, yet render the known set
in opposite orders. So a record's own fields do not determine the render; the
anchor path must be carried (or delivery made causal). -/
theorem render_reads_unknown_anchor :
    (∀ d, uK d = true → uA.fileOf d = uB.fileOf d ∧ uA.anchor d = uB.anchor d ∧
      uA.key d = uB.key d ∧ uA.tombstone d = uB.tombstone d) ∧
    render uA oTheory uK () = [2, 1] ∧ render uB oTheory uK () = [1, 2] := by
  have pa1 : uA.path 1 = [(1, 0), (3, 0)] := by
    rw [Layout.path_some uA (a := 0) (by decide) (by decide),
      Layout.path_none uA (d := 0) (by decide)]; decide
  have pa2 : uA.path 2 = [(2, 0)] := by rw [Layout.path_none uA (by decide)]; decide
  have pb1 : uB.path 1 = [(2, 1), (3, 0)] := by
    rw [Layout.path_some uB (a := 0) (by decide) (by decide),
      Layout.path_none uB (d := 0) (by decide)]; decide
  have pb2 : uB.path 2 = [(2, 0)] := by rw [Layout.path_none uB (by decide)]; decide
  refine ⟨fun d hd => ?_, ?_, ?_⟩
  · simp [uK] at hd
    simp [uA, uB, oLayout, Layout.key, hd]
  · refine (render_unique uA oTheory _ () _ ?_ (fun d => ?_)).symm
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
        List.Pairwise.nil, and_true, implies_true]
      refine ⟨?_, fun _ h => h.elim⟩
      left
      rw [root_fresh uA oTheory 1 (fun _ => rfl), root_fresh uA oTheory 2 (fun _ => rfl)]
      simp [Layout.Prec, pa1, pa2, PathLt, KeyLt]
    · simp [Live, uK, uA, oLayout, oTheory]; revert d; decide
  · refine (render_unique uB oTheory _ () _ ?_ (fun d => ?_)).symm
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
        List.Pairwise.nil, and_true, implies_true]
      refine ⟨?_, fun _ h => h.elim⟩
      left
      rw [root_fresh uB oTheory 1 (fun _ => rfl), root_fresh uB oTheory 2 (fun _ => rfl)]
      simp [Layout.Prec, pb1, pb2, PathLt, KeyLt]
    · simp [Live, uK, uB, uA, oLayout, oTheory]; revert d; decide

end
end Example

#print axioms Layout.prec_strict_total_order
#print axioms posLt_strict_total_order
#print axioms revision_root
#print axioms revision_in_place
#print axioms render_function
#print axioms render_pairwise
#print axioms render_nodup
#print axioms render_mem
#print axioms render_unique
#print axioms render_order_stable
#print axioms render_sublist_live
#print axioms render_disappears
#print axioms tombstone_not_rendered
#print axioms superseded_not_rendered
#print axioms reachable_inv
#print axioms anchor_closed
#print axioms ancestors_closed
#print axioms known_anchor_published
#print axioms path_published
#print axioms reachable_wf_known
#print axioms staged_local
#print axioms guard_stutter
#print axioms reachable_groups
#print axioms staged_pos_iff
#print axioms insert_after_anchor
#print axioms intention_preserved
#print axioms deps_precede
#print axioms winner_eq_some
#print axioms winner_exists
#print axioms names_agree
#print axioms names_unique
#print axioms renamed_env
#print axioms revise_winner_keeps_name
#print axioms winner_change_explained
#print axioms rename_preserves_deps
#print axioms receive_guard
#print axioms eventually_identical
#print axioms posLt_iff_paths
#print axioms linLt_iff_keys
#print axioms live_carried
#print axioms render_carried
#print axioms renamed_carried
#print axioms view_carried
#print axioms Example.ex_reachable
#print axioms Example.final_render
#print axioms Example.final_identical
#print axioms Example.arrival_orders
#print axioms Example.arrival_render_diverges
#print axioms Example.collision_resolved
#print axioms Example.revised_winner_keeps_name
#print axioms Example.stage_follows_anchor
#print axioms Example.final_dep_precedes
#print axioms Example.dep_guard_needed
#print axioms Example.delete_frees_name
#print axioms Example.partial_revision_frees_name
#print axioms Example.own_pending_anchor
#print axioms Example.publish_guard_needed
#print axioms Example.ex_names_checked
#print axioms Example.reserved_check_needed
#print axioms fresh_not_declared
#print axioms Example.render_reads_unknown_anchor

end ParaleanWorkspaces
