import Init

theorem P5List.map_length : ∀ (α β : Type) (f : α → β) (xs : List α), (xs.map f).length = xs.length := by
  intro α β f xs
  exact List.length_map f xs

theorem P5List.reverse_map_len_1 : ∀ xs : List Nat, ((xs.reverse).map (fun n => n + 1)).length = xs.length := by
  intro xs
  exact (P5List.map_length Nat Nat (fun n => n + 1) xs.reverse).trans (List.length_reverse xs)

theorem P5List.reverse_map_len_2 : ∀ xs : List Nat, ((xs.reverse).map (fun n => n + 2)).length = xs.length := by
  intro xs
  exact (P5List.map_length Nat Nat (fun n => n + 2) xs.reverse).trans (List.length_reverse xs)

theorem P5List.reverse_map_len_3 : ∀ xs : List Nat, ((xs.reverse).map (fun n => n + 3)).length = xs.length := by
  intro xs
  exact (P5List.map_length Nat Nat (fun n => n + 3) xs.reverse).trans (List.length_reverse xs)

theorem P5List.reverse_map_len_4 : ∀ xs : List Nat, ((xs.reverse).map (fun n => n + 4)).length = xs.length := by
  intro xs
  exact (P5List.map_length Nat Nat (fun n => n + 4) xs.reverse).trans (List.length_reverse xs)

theorem P5List.reverse_map_len_5 : ∀ xs : List Nat, ((xs.reverse).map (fun n => n + 5)).length = xs.length := by
  intro xs
  exact (P5List.map_length Nat Nat (fun n => n + 5) xs.reverse).trans (List.length_reverse xs)

theorem P5List.reverse_map_len_6 : ∀ xs : List Nat, ((xs.reverse).map (fun n => n + 6)).length = xs.length := by
  intro xs
  exact (P5List.map_length Nat Nat (fun n => n + 6) xs.reverse).trans (List.length_reverse xs)

theorem P5List.reverse_map_len_7 : ∀ xs : List Nat, ((xs.reverse).map (fun n => n + 7)).length = xs.length := by
  intro xs
  exact (P5List.map_length Nat Nat (fun n => n + 7) xs.reverse).trans (List.length_reverse xs)

theorem P5List.reverse_map_len_8 : ∀ xs : List Nat, ((xs.reverse).map (fun n => n + 8)).length = xs.length := by
  intro xs
  exact (P5List.map_length Nat Nat (fun n => n + 8) xs.reverse).trans (List.length_reverse xs)

theorem P5List.reverse_map_lengths : ∀ xs : List Nat, ((xs.reverse).map (fun n => n + 1)).length = xs.length ∧ ((xs.reverse).map (fun n => n + 2)).length = xs.length ∧ ((xs.reverse).map (fun n => n + 3)).length = xs.length ∧ ((xs.reverse).map (fun n => n + 4)).length = xs.length ∧ ((xs.reverse).map (fun n => n + 5)).length = xs.length ∧ ((xs.reverse).map (fun n => n + 6)).length = xs.length ∧ ((xs.reverse).map (fun n => n + 7)).length = xs.length ∧ ((xs.reverse).map (fun n => n + 8)).length = xs.length := by
  intro xs
  exact ⟨P5List.reverse_map_len_1 xs, P5List.reverse_map_len_2 xs, P5List.reverse_map_len_3 xs, P5List.reverse_map_len_4 xs, P5List.reverse_map_len_5 xs, P5List.reverse_map_len_6 xs, P5List.reverse_map_len_7 xs, P5List.reverse_map_len_8 xs⟩
