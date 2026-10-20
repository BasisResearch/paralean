----------------------------- MODULE Ingress -----------------------------
EXTENDS Naturals, FiniteSets
\* Operational boundary only; receipt/epoch safety remains in Receipts/Targets.
\* Finite abstraction of active connections, frame allocation and S3 deletion.
CONSTANT MaxConnections, MaxBytes
VARIABLES active, allocated, deleted
vars == <<active, allocated, deleted>>
ConnectionRoom == active < MaxConnections
SizeOK(n) == n <= MaxBytes
DeleteAllowed == FALSE
BackendReachable == FALSE
Init == /\ active = 0 /\ allocated = 0 /\ deleted = FALSE
Connect == /\ ConnectionRoom /\ active' = active + 1
           /\ UNCHANGED <<allocated, deleted>>
Read(n) == /\ active > 0 /\ SizeOK(n) /\ allocated' = n
           /\ UNCHANGED <<active, deleted>>
Close == /\ active > 0 /\ active' = active - 1 /\ allocated' = 0
         /\ UNCHANGED deleted
Delete == /\ (DeleteAllowed \/ BackendReachable) /\ deleted' = TRUE
          /\ UNCHANGED <<active, allocated>>
Next == Connect \/ Close \/ (\E n \in 0..(MaxBytes + 1): Read(n)) \/ Delete
Spec == Init /\ [][Next]_vars
ConnectionsBounded == active <= MaxConnections
AllocationBounded == allocated <= MaxBytes
AppendOnly == ~deleted
=============================================================================
