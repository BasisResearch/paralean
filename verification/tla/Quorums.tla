----------------------------- MODULE Quorums -----------------------------
EXTENDS Durability
CaseWrites == {{"r1", "r2"}, {"r1", "r3"}, {"r2", "r3"}}
CaseReads == CaseWrites
CaseMeet == [p \in CaseWrites \X CaseReads |-> CHOOSE r \in p[1] \intersect p[2] : TRUE]
=============================================================================
