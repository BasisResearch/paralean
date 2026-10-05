---------------------------- MODULE Certificates ----------------------------
(* Durable acknowledgement certificates for publication discovery. Mirrors
   verification/veil/Paralean/AckCertificates.lean. Marker bytes are physical
   but cannot distinguish an acknowledged marker from a staged one. `cert[r]`
   is the physical per-replica certificate record, erased when r is lost.
   `certReply[n][g]` is writer n's own record of the replicas that acknowledged
   its certificate writes for g; it is local to n and survives replica loss.
   Replies are collected one CertPut at a time. Atomic publication acknowledges
   the marker, so `published` is also the ghost marker acknowledgement.
   ScanReceive reads only certificates on live replicas of a fully live
   recovery quorum. Commit reads only the committer's own replies. *)
EXTENDS FiniteSets, TLC
CONSTANTS Replicas, Groups, Nodes, Writes, Reads
VARIABLES marker, live, published, cert, certReply, known, head, erased, rediscovered
vars == <<marker, live, published, cert, certReply, known, head, erased, rediscovered>>

ASSUME /\ Writes \subseteq SUBSET Replicas /\ Reads \subseteq SUBSET Replicas
       /\ \A w \in Writes, q \in Reads : w \intersect q # {}

TypeOK == /\ marker \in [Replicas -> SUBSET Groups]
          /\ live \subseteq Replicas
          /\ published \subseteq Groups
          /\ cert \in [Replicas -> SUBSET Groups]
          /\ certReply \in [Nodes -> [Groups -> SUBSET Replicas]]
          /\ known \in [Nodes -> SUBSET Groups]
          /\ head \in [Nodes -> SUBSET Groups]
          /\ erased \in BOOLEAN
          /\ rediscovered \subseteq Groups

Init == /\ marker = [r \in Replicas |-> {}]
        /\ live = Replicas
        /\ published = {}
        /\ cert = [r \in Replicas |-> {}]
        /\ certReply = [n \in Nodes |-> [g \in Groups |-> {}]]
        /\ known = [n \in Nodes |-> {}]
        /\ head = [n \in Nodes |-> {}]
        /\ erased = FALSE
        /\ rediscovered = {}

LiveQuorum(q) == q \subseteq live

(* Node n holds replies for g from a whole write quorum, collected over time. *)
CertQuorumBy(n, g) == \E w \in Writes : w \subseteq certReply[n][g]
CertQuorum(g) == \E n \in Nodes : CertQuorumBy(n, g)

(* Staging marker bytes; a crash may interrupt before acknowledgement. *)
PutMarker(r, g) == /\ r \in live
                   /\ marker' = [marker EXCEPT ![r] = @ \cup {g}]
                   /\ UNCHANGED <<live, published, cert, certReply, known, head, erased, rediscovered>>

(* Atomic marker quorum acknowledgement plus publication by writer n. *)
AckPublish(n, g, w) == /\ g \notin published
                       /\ \A r \in w : r \in live /\ g \in marker[r]
                       /\ published' = published \cup {g}
                       /\ known' = [known EXCEPT ![n] = @ \cup {g}]
                       /\ UNCHANGED <<marker, live, cert, certReply, head, erased, rediscovered>>

(* Writer n's local knowledge (not a scan) authorises a certificate write; the
   live replica stores it and n records the reply. *)
CertPut(n, r, g) == /\ r \in live
                    /\ g \in known[n]
                    /\ cert' = [cert EXCEPT ![r] = @ \cup {g}]
                    /\ certReply' = [certReply EXCEPT ![n][g] = @ \cup {r}]
                    /\ UNCHANGED <<marker, live, published, known, head, erased, rediscovered>>

(* Replica loss wipes marker bytes and certificates; a live recovery quorum remains. *)
Lose(r) == /\ r \in live
           /\ \E q \in Reads : q \subseteq live \ {r}
           /\ live' = live \ {r}
           /\ marker' = [marker EXCEPT ![r] = {}]
           /\ cert' = [cert EXCEPT ![r] = {}]
           /\ UNCHANGED <<published, certReply, known, head, erased, rediscovered>>

(* Every worker index is erased; `erased` (ghost) records erasure after a loss. *)
EraseIndexes == /\ known' = [n \in Nodes |-> {}]
                /\ erased' = (erased \/ live # Replicas)
                /\ UNCHANGED <<marker, live, published, cert, certReply, head, rediscovered>>

(* Discovery reads only physical certificates on a live quorum. *)
ScanReceive(n, g, q) == /\ q \in Reads /\ LiveQuorum(q)
                        /\ \E r \in q : g \in cert[r]
                        /\ g \notin known[n]
                        /\ known' = [known EXCEPT ![n] = @ \cup {g}]
                        /\ rediscovered' = IF erased THEN rediscovered \cup {g} ELSE rediscovered
                        /\ UNCHANGED <<marker, live, published, cert, certReply, head, erased>>

(* A checkpoint may only contain groups for which the committer itself holds a
   write quorum of certificate replies. *)
Commit(n, S) == /\ S \subseteq known[n]
                /\ \A g \in S : CertQuorumBy(n, g)
                /\ head' = [head EXCEPT ![n] = S]
                /\ UNCHANGED <<marker, live, published, cert, certReply, known, erased, rediscovered>>

Next == \/ \E r \in Replicas, g \in Groups : PutMarker(r, g)
        \/ \E n \in Nodes, r \in Replicas, g \in Groups : CertPut(n, r, g)
        \/ \E n \in Nodes, g \in Groups, w \in Writes : AckPublish(n, g, w)
        \/ \E r \in Replicas : Lose(r)
        \/ EraseIndexes
        \/ \E n \in Nodes, g \in Groups, q \in Reads : ScanReceive(n, g, q)
        \/ \E n \in Nodes, S \in SUBSET Groups : Commit(n, S)
Spec == Init /\ [][Next]_vars

ScanFinds(g) == \A q \in Reads : LiveQuorum(q) => \E r \in q : g \in cert[r]

(* Replicas, groups and nodes are interchangeable (Writes and Reads are all pairs). *)
Symmetry == Permutations(Replicas) \cup Permutations(Groups) \cup Permutations(Nodes)

FailureEnvelope == \E q \in Reads : LiveQuorum(q)
CertSound == \A r \in Replicas : cert[r] \subseteq published
CertLive == \A r \in Replicas \ live : cert[r] = {}
ReplySurvives == \A n \in Nodes, g \in Groups :
                   \A r \in certReply[n][g] : r \in live => g \in cert[r]
ScanComplete == \A g \in Groups : CertQuorum(g) => ScanFinds(g)
ScanBetween == \A q \in Reads : LiveQuorum(q) =>
                 \A g \in Groups : (CertQuorum(g) => \E r \in q : g \in cert[r]) /\
                                  ((\E r \in q : g \in cert[r]) => g \in published)
CheckpointCertified == \A n \in Nodes : \A g \in head[n] : CertQuorumBy(n, g)
CheckpointDiscoverable == \A n \in Nodes : \A g \in head[n] : ScanFinds(g)
ReceivedPublished == \A n \in Nodes : known[n] \subseteq published

(* Witness properties: expected to FAIL in the ordinary model (usefulness). *)
NeverRediscoveredAfterLoss ==
    ~(erased /\ \E m \in Nodes : head[m] # {} /\ head[m] \subseteq rediscovered)
(* A commit whose replies include a replica already lost at commit time. *)
NeverCommitWithLostReplier ==
    [][\A n \in Nodes : head'[n] # head[n] =>
         \A g \in head'[n] : certReply[n][g] \subseteq live]_vars
=============================================================================
