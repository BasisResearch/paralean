---------------------------- MODULE Publication ----------------------------
EXTENDS FiniteSets, TLC
CONSTANTS Nodes, Decls, Names, Name, Deps, Ancestors, Valid, Exportable,
          CollisionLeft, CollisionRight,
          Replicas, Objects, Writes, Reads, Meet, Payload, Manifest
VARIABLES published, known, pending, head, alive, online, stable,
          stored, live, acknowledged, witness
registryVars == <<published, known, pending, head, alive, online, stable>>
storeVars == <<stored, live, acknowledged, witness>>
vars == <<registryVars, storeVars>>
R == INSTANCE Registry
D == INSTANCE Durability
ASSUME /\ Payload \in [Decls -> Objects]
       /\ Manifest \in [SUBSET Decls -> Objects]

Init == R!Init /\ D!Init
Publish(n,d) == /\ Payload[d] \in acknowledged
                /\ R!Publish(n,d)
                /\ UNCHANGED storeVars
Commit(n,S) == /\ Manifest[S] \in acknowledged
               /\ R!Commit(n,S)
               /\ UNCHANGED storeVars
RegistryStep ==
    /\ ((\E n \in Nodes, d \in Decls : R!Prepare(n,d) \/ R!Receive(n,d))
         \/ (\E n \in Nodes : R!Crash(n) \/ R!Recover(n) \/ R!Partition(n) \/ R!Reconnect(n))
         \/ R!Heal)
    /\ UNCHANGED storeVars
StorageStep == D!Next /\ UNCHANGED registryVars
Next == \/ RegistryStep
        \/ StorageStep
        \/ \E n \in Nodes, d \in Decls : Publish(n,d)
        \/ \E n \in Nodes, S \in SUBSET Decls : Commit(n,S)
Spec == Init /\ [][Next]_vars

TypeOK == R!TypeOK /\ D!TypeOK
ComponentSafety == R!AdmissionSafety /\ R!SnapshotSafety /\ R!CollisionSafety
                   /\ D!WitnessSurvives /\ D!FailureEnvelope /\ D!Recoverable
PublicationGuard == \A d \in published : Payload[d] \in acknowledged
CheckpointGuard == \A n \in Nodes : head[n] # {} => Manifest[head[n]] \in acknowledged
PublishedRecoverable == \A d \in published : \E r \in live : Payload[d] \in stored[r]
CheckpointRecoverable == \A n \in Nodes : head[n] # {} =>
                           \E r \in live : Manifest[head[n]] \in stored[r]
NeverCommitted == \A n \in Nodes : head[n] = {}
=============================================================================
