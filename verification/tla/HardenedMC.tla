----------------------------- MODULE HardenedMC -----------------------------
(* Pruning for coverage witnesses only (scripts/check-tla-hardened.sh). A
   witness run looks for a reachable state violating a Never* property; a
   violation found under a state constraint is a behaviour of Hardened!Spec,
   so pruning can only make a witness harder to find, never fake one.
   Positive runs and mutation runs never use these constraints. *)
EXTENDS Hardened

\* No replica loss and no index erasure.
NoFailures == live = Replicas /\ erasure = 0
=============================================================================
