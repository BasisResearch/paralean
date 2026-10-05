/-! A consumer of the merged store: the two workspaces' instances of one type collide. -/
theorem InstDup.use : (default : Nat × String × Bool).2.2 = (default : Nat × String × Bool).2.2 := rfl
