-------------------------- MODULE CatalogueExchange --------------------------
EXTENDS Naturals, FiniteSets

(* Source-qualified catalogue replication, refining the existing network path.
   Each source has its own fence; transfer preserves the original proof and
   never issues a local commit certificate. Payload acknowledgement is local.
   A record's historical freshness is established at its source commit, not
   re-evaluated against later discoveries at a receiver. Cryptographic validity
   is abstracted by membership in sourceCert, never by a sender assertion. *)
Nodes == {"a", "b", "c"}
Records == {"r", "s"}
Origin(r) == "a"
Parent(r) == IF r = "s" THEN {"r"} ELSE {}
Rank(r) == IF r = "r" THEN 0 ELSE 1
VARIABLES fence, sourceCert, payload, copies, local
vars == <<fence, sourceCert, payload, copies, local>>

Init ==
  /\ fence = 0
  /\ sourceCert = {}
  /\ payload = [n \in Nodes |-> {}]
  /\ copies = [n \in Nodes |-> {}]
  /\ local = [n \in Nodes |-> {}]

Ack(n, r) ==
  /\ r \notin payload[n]
  /\ payload' = [payload EXCEPT ![n] = @ \cup {r}]
  /\ UNCHANGED <<fence, sourceCert, copies, local>>
Rotate ==
  /\ fence = 0
  /\ fence' = 1
  /\ UNCHANGED <<sourceCert, payload, copies, local>>
Commit(r) ==
  /\ r \notin sourceCert
  /\ Rank(r) = fence
  /\ r \in payload[Origin(r)]
  /\ Parent(r) \subseteq sourceCert
  /\ sourceCert' = sourceCert \cup {r}
  /\ local' = [local EXCEPT ![Origin(r)] = @ \cup {r}]
  /\ UNCHANGED <<fence, payload, copies>>

SourceProof(r) == r \in sourceCert
ParentReady(n, r) == Parent(r) \subseteq (copies[n] \cup local[n])
PayloadReady(n, r) == r \in payload[n]
(* The untrusted sender may advertise any record. Only source-proof checking
   distinguishes a forged advertisement from a certified historical commit. *)
Receive(n, r) ==
  /\ n # Origin(r)
  /\ r \notin copies[n]
  /\ SourceProof(r)
  /\ ParentReady(n, r)
  /\ PayloadReady(n, r)
  /\ copies' = [copies EXCEPT ![n] = @ \cup {r}]
  /\ local' = local
  /\ UNCHANGED <<fence, sourceCert, payload>>
Next == Rotate \/ (\E n \in Nodes, r \in Records : Ack(n, r) \/ Receive(n, r))
                  \/ (\E r \in Records : Commit(r))
Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ (\A n \in Nodes, r \in Records :
                         WF_vars(Ack(n, r)) /\ WF_vars(Receive(n, r)))
TypeOK == /\ fence \in 0..1 /\ sourceCert \subseteq Records
          /\ payload \in [Nodes -> SUBSET Records]
          /\ copies \in [Nodes -> SUBSET Records]
          /\ local \in [Nodes -> SUBSET Records]
OnlySourceCertified == \A n \in Nodes : copies[n] \subseteq sourceCert
ParentClosed == \A n \in Nodes : \A r \in copies[n] : ParentReady(n, r)
LocallyAcknowledged == \A n \in Nodes : copies[n] \subseteq payload[n]
FenceIsolation == \A n \in Nodes : local[n] \subseteq {r \in sourceCert : Origin(r) = n}
EventuallyReplicated == \A r \in Records :
  (r \in sourceCert) ~> (\A n \in Nodes : r \in copies[n] \cup local[n])
NeverRelayedChild == "s" \notin copies["c"]
=============================================================================
