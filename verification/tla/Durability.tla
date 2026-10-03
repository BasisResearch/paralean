---------------------------- MODULE Durability ----------------------------
EXTENDS FiniteSets, TLC

CONSTANTS Replicas, Objects, Writes, Reads, Meet
ASSUME /\ Replicas # {}
       /\ Objects # {}
       /\ Writes \subseteq SUBSET Replicas
       /\ Reads \subseteq SUBSET Replicas
       /\ Writes # {}
       /\ Reads # {}
       /\ Meet \in [Writes \X Reads -> Replicas]
       /\ \A w \in Writes, r \in Reads : Meet[<<w,r>>] \in w \intersect r

VARIABLES stored, live, acknowledged, witness
vars == <<stored, live, acknowledged, witness>>
Init == /\ stored = [r \in Replicas |-> {}]
        /\ live = Replicas
        /\ acknowledged = {}
        /\ witness = [o \in Objects |-> CHOOSE w \in Writes : TRUE]

(* Put means hash-verified bytes plus validator receipt have reached durable
   storage, not an in-flight packet or a worker's volatile buffer. *)
Put(r, o) == /\ r \in live
             /\ stored' = [stored EXCEPT ![r] = @ \cup {o}]
             /\ UNCHANGED <<live, acknowledged, witness>>
Ack(o, w) == /\ w \subseteq live
             /\ \A r \in w : o \in stored[r]
             /\ acknowledged' = acknowledged \cup {o}
             /\ witness' = [witness EXCEPT ![o] = w]
             /\ UNCHANGED <<stored, live>>

(* Failures may destroy disks permanently. The assumed failure envelope is
   existence of a surviving recovery quorum, without cardinal arithmetic. *)
Lose(r) == /\ r \in live
            /\ \E q \in Reads : q \subseteq live \ {r}
            /\ live' = live \ {r}
            /\ stored' = [stored EXCEPT ![r] = {}]
            /\ UNCHANGED <<acknowledged, witness>>
Next == (\E r \in Replicas, o \in Objects : Put(r,o))
        \/ (\E o \in Objects, w \in Writes : Ack(o,w))
        \/ (\E r \in Replicas : Lose(r))
Spec == Init /\ [][Next]_vars

TypeOK == /\ stored \in [Replicas -> SUBSET Objects]
          /\ live \subseteq Replicas
          /\ acknowledged \subseteq Objects
          /\ witness \in [Objects -> Writes]
WitnessSurvives == \A o \in acknowledged : \A r \in witness[o] \intersect live : o \in stored[r]
FailureEnvelope == \E q \in Reads : q \subseteq live
Recoverable == \A o \in acknowledged, q \in Reads : q \subseteq live =>
                 /\ Meet[<<witness[o],q>>] \in live
                 /\ o \in stored[Meet[<<witness[o],q>>]]
NoDataLoss == \A o \in acknowledged : \E r \in live : o \in stored[r]
NeverAcked == acknowledged = {}
NeverLost == live = Replicas
=============================================================================
