----------------------------- MODULE Ingress -----------------------------
EXTENDS Naturals, FiniteSets
\* Operational boundary only; receipt/epoch safety remains in Receipts/Targets.
\* Finite abstraction of active connections, frame allocation and S3 deletion.
\* W2 A-12: one anti-entropy event from a hostile peer that never completes it
\* and lists arbitrary object references. `staged` counts its parts persisted in
\* FDB, `declared` the object bytes its staged ObjectRefs name, `fetched` the
\* bytes the receiver has put into append-only S3 for it. A part that would
\* pass a per-event cap makes the event terminal in the same transaction,
\* clearing its staged parts; objects are fetched only for staged references.
CONSTANT MaxConnections, MaxBytes, MaxEventParts, MaxEventObjectBytes, MaxObject
VARIABLES active, allocated, deleted, staged, declared, fetched, terminal
vars == <<active, allocated, deleted, staged, declared, fetched, terminal>>
ae == <<staged, declared, fetched, terminal>>
ConnectionRoom == active < MaxConnections
SizeOK(n) == n <= MaxBytes
DeleteAllowed == FALSE
BackendReachable == FALSE
PartRoom == staged < MaxEventParts
RefRoom(n) == declared + n <= MaxEventObjectBytes
Init == /\ active = 0 /\ allocated = 0 /\ deleted = FALSE
        /\ staged = 0 /\ declared = 0 /\ fetched = 0 /\ terminal = FALSE
Connect == /\ ConnectionRoom /\ active' = active + 1
           /\ UNCHANGED <<allocated, deleted>> /\ UNCHANGED ae
Read(n) == /\ active > 0 /\ SizeOK(n) /\ allocated' = n
           /\ UNCHANGED <<active, deleted>> /\ UNCHANGED ae
Close == /\ active > 0 /\ active' = active - 1 /\ allocated' = 0
         /\ UNCHANGED deleted /\ UNCHANGED ae
Delete == /\ (DeleteAllowed \/ BackendReachable) /\ deleted' = TRUE
          /\ UNCHANGED <<active, allocated>> /\ UNCHANGED ae
\* ae_save_progress: a metadata part (n = 0) or an ObjectRef of n bytes.
StagePart(n) == /\ ~terminal /\ PartRoom /\ RefRoom(n)
                /\ staged' = staged + 1 /\ declared' = declared + n
                /\ UNCHANGED <<fetched, terminal>>
                /\ UNCHANGED <<active, allocated, deleted>>
OverCap(n) == /\ ~terminal /\ ~(PartRoom /\ RefRoom(n))
              /\ terminal' = TRUE /\ staged' = 0 /\ declared' = 0
              /\ UNCHANGED fetched /\ UNCHANGED <<active, allocated, deleted>>
\* Puller: fetch and put one object named by a staged reference.
Fetch(n) == /\ ~terminal /\ fetched + n <= declared /\ fetched' = fetched + n
            /\ UNCHANGED <<staged, declared, terminal>>
            /\ UNCHANGED <<active, allocated, deleted>>
Next == Connect \/ Close \/ (\E n \in 0..(MaxBytes + 1): Read(n)) \/ Delete
        \/ \E n \in 0..MaxObject : StagePart(n) \/ OverCap(n) \/ Fetch(n)
Spec == Init /\ [][Next]_vars
ConnectionsBounded == active <= MaxConnections
AllocationBounded == allocated <= MaxBytes
AppendOnly == ~deleted
EventPartsBounded == staged <= MaxEventParts
EventObjectsBounded == fetched <= MaxEventObjectBytes
\* Reachability witness: a hostile event is eventually archived.
NeverTerminal == ~terminal
=============================================================================
