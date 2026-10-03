----------------------------- MODULE Revision -----------------------------
EXTENDS Registry
CaseName == [d \in {"old", "new", "proof"} |-> IF d = "proof" THEN "lemma" ELSE "value"]
CaseDeps == [d \in {"old", "new", "proof"} |-> IF d = "proof" THEN {"old"} ELSE {}]
CaseAncestors == [d \in {"old", "new", "proof"} |-> IF d = "new" THEN {"old"} ELSE {}]
CaseExportable == SUBSET {"old", "new", "proof"}
(* A new value cannot silently retarget a proof bound to the old value. *)
NoRetargeting == \A n \in Nodes : "proof" \in head[n] =>
                  "old" \in head[n] /\ "new" \notin head[n]
=============================================================================
