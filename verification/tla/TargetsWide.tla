----------------------------- MODULE TargetsWide -----------------------------
(* Targets at a larger scope. Proof IDs are interchangeable (Prepare picks any
   unused one), and so are the workers other than the initial owner. The
   symmetry is used only with invariants. *)
EXTENDS Targets, TLC

WideSymmetry == Permutations(Proofs) \cup Permutations(Workers \ {InitialOwner})
=============================================================================
