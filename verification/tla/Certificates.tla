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
   recovery quorum. Commit reads only the committer's own replies.

   AtomicCert selects the publication design. FALSE (original): certificates
   are written by later CertPut steps, each needing local knowledge, so a
   publisher whose index is erased before any CertPut strands its publication
   (`PublishedDiscoverable` fails). TRUE (fix): the publication transaction
   also writes the publisher's certificates on the acknowledging write quorum
   and records those replies.

   Liveness (FairSpec): certificate writes by a knowing node and scans of a
   live read quorum are weakly fair; replica loss and index erasure are not. *)
EXTENDS FiniteSets, TLC
CONSTANTS Replicas, Groups, Nodes, Writes, Reads, AtomicCert
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

(* Atomic marker quorum acknowledgement plus publication by writer n. Under
   AtomicCert the same transaction writes n's certificates on the write quorum
   w that acknowledged the marker, and n records those replies. *)
AckPublish(n, g, w) == /\ g \notin published
                       /\ \A r \in w : r \in live /\ g \in marker[r]
                       /\ published' = published \cup {g}
                       /\ known' = [known EXCEPT ![n] = @ \cup {g}]
                       /\ cert' = IF AtomicCert
                                  THEN [r \in Replicas |-> IF r \in w THEN cert[r] \cup {g} ELSE cert[r]]
                                  ELSE cert
                       /\ certReply' = IF AtomicCert
                                       THEN [certReply EXCEPT ![n][g] = @ \cup w]
                                       ELSE certReply
                       /\ UNCHANGED <<marker, live, head, erased, rediscovered>>

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
FairSpec == /\ Spec
            /\ \A n \in Nodes, r \in Replicas, g \in Groups : WF_vars(CertPut(n, r, g))
            /\ \A n \in Nodes, g \in Groups : WF_vars(\E q \in Reads : ScanReceive(n, g, q))

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

(* Under the fix every publication carries a certificate quorum. *)
PublishedCertified == AtomicCert => \A g \in published : CertQuorum(g)

(* Liveness. A group in some node's checkpoint is eventually rediscovered by
   every node, whatever indexes were erased and replicas lost (recovery is
   possible given a live read quorum). *)
CommittedDiscoverable ==
    \A n, m \in Nodes, g \in Groups : g \in head[n] ~> g \in known[m]
(* Every publication is eventually discoverable by every node. Fails with
   AtomicCert = FALSE: the stranded publication. *)
PublishedDiscoverable ==
    \A m \in Nodes, g \in Groups : g \in published ~> g \in known[m]

(* Witness properties: expected to FAIL in the ordinary model (usefulness). *)
NeverRediscoveredAfterLoss ==
    ~(erased /\ \E m \in Nodes : head[m] # {} /\ head[m] \subseteq rediscovered)
(* A commit whose replies include a replica already lost at commit time. *)
NeverCommitWithLostReplier ==
    [][\A n \in Nodes : head'[n] # head[n] =>
         \A g \in head'[n] : certReply[n][g] \subseteq live]_vars
=============================================================================
