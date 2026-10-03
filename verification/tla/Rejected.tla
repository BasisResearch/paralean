----------------------------- MODULE Rejected -----------------------------
EXTENDS Registry
CaseName == [d \in {"bad", "x", "y"} |-> d]
CaseDeps == [d \in {"bad", "x", "y"} |-> CASE d = "x" -> {"y"}
                                               [] d = "y" -> {"x"}
                                               [] OTHER -> {}]
CaseAncestors == [d \in {"bad", "x", "y"} |-> {}]
CaseExportable == SUBSET {"bad", "x", "y"}
NothingAdmitted == published = {}
=============================================================================
