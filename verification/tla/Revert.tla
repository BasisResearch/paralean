------------------------------ MODULE Revert ------------------------------
EXTENDS Registry
CaseName == [d \in {"old", "new", "revert"} |-> "value"]
CaseDeps == [d \in {"old", "new", "revert"} |-> {}]
CaseAncestors == [d \in {"old", "new", "revert"} |-> CASE d = "new" -> {"old"}
                                                       [] d = "revert" -> {"old", "new"}
                                                       [] OTHER -> {}]
CaseExportable == SUBSET {"old", "new", "revert"}
(* Content may return to its old bytes; revision identity remains distinct. *)
Content == [d \in {"old", "new", "revert"} |-> IF d = "new" THEN "one" ELSE "zero"]
RevertIsNewHead == \A n \in Nodes : "revert" \in known[n] => Heads(known[n], "value") = {"revert"}
NoFalseCollision == \A n \in Nodes : ~Conflict(known[n], "value")
=============================================================================
