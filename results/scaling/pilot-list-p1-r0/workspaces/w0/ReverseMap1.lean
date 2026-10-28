-- paralean: published projection of ReverseMap1.lean

-- paralean:published 39ed8029be09c87a737e44f35ce3c5d9fe2c78eb028668c6d154495ec438803a
theorem P5List.reverse_map_len_1 : ∀ xs : List Nat, ((xs.reverse).map (fun n => n + 1)).length = xs.length :=
  remote% "39ed8029be09c87a737e44f35ce3c5d9fe2c78eb028668c6d154495ec438803a"
-- paralean:end 39ed8029be09
