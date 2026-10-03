---------------------------- MODULE Collision ----------------------------
EXTENDS Registry
CaseName == [d \in {"x", "y"} |-> "helper"]
CaseDeps == [d \in {"x", "y"} |-> {}]
CaseAncestors == [d \in {"x", "y"} |-> {}]
CaseExportable == SUBSET {"x", "y"}
=============================================================================
