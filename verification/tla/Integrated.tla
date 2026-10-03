----------------------------- MODULE Integrated -----------------------------
EXTENDS Publication
CaseName == [d \in {"helper"} |-> d]
CaseDeps == [d \in {"helper"} |-> {}]
CaseAncestors == [d \in {"helper"} |-> {}]
CaseExportable == SUBSET {"helper"}
CaseWrites == {{"r1", "r2"}, {"r1", "r3"}, {"r2", "r3"}}
CaseReads == CaseWrites
CaseMeet == [p \in CaseWrites \X CaseReads |-> CHOOSE r \in p[1] \intersect p[2] : TRUE]
CasePayload == [d \in {"helper"} |-> "package"]
CaseManifest == [S \in SUBSET {"helper"} |-> IF S = {} THEN "empty" ELSE "checkpoint"]
=============================================================================
