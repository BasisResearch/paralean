------------------------------ MODULE Chain ------------------------------
EXTENDS Registry
CaseName == [d \in {"b", "a", "c"} |-> d]
CaseDeps == [d \in {"b", "a", "c"} |-> CASE d = "a" -> {"b"}
                                              [] d = "c" -> {"a"}
                                              [] OTHER -> {}]
CaseAncestors == [d \in {"b", "a", "c"} |-> {}]
CaseExportable == SUBSET {"b", "a", "c"}
=============================================================================
