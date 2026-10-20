-------------------------- MODULE AgentAuthority --------------------------
EXTENDS FiniteSets, Naturals

(* Controller-signed registration and the T1/T8/T10 commit guards. Registration,
   revocation, publication and deletion happen at most once per finite item. The
   model observes authorization at commit time, before a later revocation/rotation. *)
CONSTANTS Agents, Keys, Records, Tombs, TargetAuthor, ClaimedAuthor,
          SignerKey, Target, GrantFence, HasControllerGrant, IsReceive,
          HasOrigin, RegistryGuard, RevocationGuard, FenceGuard, SourceGuard
ASSUME /\ TargetAuthor \in [Records -> Agents]
       /\ ClaimedAuthor \in [Records \cup Tombs -> Agents]
       /\ SignerKey \in [Records \cup Tombs -> Keys]
       /\ Target \in [Tombs -> Records]
       /\ GrantFence \in [Tombs -> Nat]
       /\ HasControllerGrant \in [Tombs -> BOOLEAN]
       /\ HasOrigin \in [Tombs -> BOOLEAN]
       /\ IsReceive \in [Tombs -> BOOLEAN]
       /\ RegistryGuard \in BOOLEAN /\ RevocationGuard \in BOOLEAN
       /\ FenceGuard \in BOOLEAN /\ SourceGuard \in BOOLEAN

CaseTargetAuthor == [r \in Records |-> "a"]
CaseClaimedAuthor == [x \in Records \cup Tombs |-> IF x = "r2" \/ x = "t1" \/ x = "t2" THEN "b" ELSE "a"]
CaseSignerKey == [x \in Records \cup Tombs |-> IF x = "t1" \/ x = "t2" THEN "kb" ELSE "ka"]
CaseTarget == [t \in Tombs |-> "r1"]
CaseGrantFence == [t \in Tombs |-> 0]
CaseHasControllerGrant == [t \in Tombs |-> TRUE]
CaseHasOrigin == [t \in Tombs |-> t = "t1"]
CaseIsReceive == [t \in Tombs |-> t = "t1"]

VARIABLES registered, revoked, fence, published, deleted, pubEvidence, delEvidence
vars == <<registered, revoked, fence, published, deleted, pubEvidence, delEvidence>>

ActualActive(a, k) == <<a, k>> \in registered /\ k \notin revoked
Active(a, k) == (\neg RegistryGuard \/ <<a, k>> \in registered)
                /\ (\neg RevocationGuard \/ k \notin revoked)
ActualController(t) == HasControllerGrant[t] /\ HasOrigin[t] /\ GrantFence[t] = fence
Controller(t) == HasControllerGrant[t] /\ (\neg SourceGuard \/ HasOrigin[t])
                 /\ (\neg FenceGuard \/ GrantFence[t] = fence)
ActualDelete(t) == (ClaimedAuthor[t] = TargetAuthor[Target[t]]
                    /\ ActualActive(ClaimedAuthor[t], SignerKey[t]))
                    \/ ActualController(t)
DeleteOk(t) == (ClaimedAuthor[t] = TargetAuthor[Target[t]]
                /\ Active(ClaimedAuthor[t], SignerKey[t]))
               \/ Controller(t)

Init == /\ registered = {} /\ revoked = {} /\ fence = 0
        /\ published = {} /\ deleted = {}
        /\ pubEvidence = [r \in Records |-> FALSE]
        /\ delEvidence = [t \in Tombs |-> FALSE]
Register(a, k) == /\ a \in Agents /\ k \in Keys
                  /\ <<a, k>> \notin registered /\ k \notin revoked
                  /\ registered' = registered \cup {<<a, k>>}
                  /\ UNCHANGED <<revoked, fence, published, deleted, pubEvidence, delEvidence>>
Revoke(k) == /\ k \in Keys /\ k \notin revoked
             /\ revoked' = revoked \cup {k}
             /\ UNCHANGED <<registered, fence, published, deleted, pubEvidence, delEvidence>>
RotateFence == /\ fence = 0 /\ fence' = 1
               /\ UNCHANGED <<registered, revoked, published, deleted, pubEvidence, delEvidence>>
Publish(r) == /\ r \in Records /\ r \notin published
              /\ Active(ClaimedAuthor[r], SignerKey[r])
              /\ published' = published \cup {r}
              /\ pubEvidence' = [pubEvidence EXCEPT ![r] = ActualActive(ClaimedAuthor[r], SignerKey[r])]
              /\ UNCHANGED <<registered, revoked, fence, deleted, delEvidence>>
Delete(t) == /\ t \in Tombs /\ t \notin deleted
             /\ Target[t] \in published /\ DeleteOk(t)
             /\ deleted' = deleted \cup {t}
             /\ delEvidence' = [delEvidence EXCEPT ![t] = ActualDelete(t)]
             /\ UNCHANGED <<registered, revoked, fence, published, pubEvidence>>
Next == \/ \E a \in Agents, k \in Keys : Register(a, k)
        \/ \E k \in Keys : Revoke(k)
        \/ RotateFence
        \/ \E r \in Records : Publish(r)
        \/ \E t \in Tombs : Delete(t)
Spec == Init /\ [][Next]_vars

TypeOk == /\ registered \subseteq Agents \X Keys /\ revoked \subseteq Keys
          /\ fence \in 0..1 /\ published \subseteq Records /\ deleted \subseteq Tombs
PublishedAuthorized == \A r \in published : pubEvidence[r]
DeletedAuthorized == \A t \in deleted : delEvidence[t]
=============================================================================
