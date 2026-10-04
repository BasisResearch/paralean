-------------------------- MODULE CheckpointReuse --------------------------
EXTENDS Integrated

(* This is a restricted execution of existing component actions. The stage
   records their order and introduces no new publication or recovery action.
   The registry retains head across Crash, so this witnesses use by a known
   checkpoint identity, not manifest enumeration or recovery of a lost hash. *)
VARIABLE stage
useVars == <<vars, stage>>

Selected == {"helper"}
SurvivingSelected ==
    /\ \E r \in live : Manifest[Selected] \in stored[r]
    /\ \A d \in Selected : \E r \in live : Payload[d] \in stored[r]

UseInit == Init /\ stage = "building"
UseNext ==
    \/ /\ stage = "building"
       /\ Next
       /\ live' = live
       /\ head'["A"] = {}
       /\ UNCHANGED stage
    \/ /\ stage = "building"
       /\ Commit("A", Selected)
       /\ stage' = "committed"
    \/ /\ stage = "committed"
       /\ \E r \in Replicas :
             /\ r \in witness[Manifest[Selected]]
             /\ \A d \in Selected : r \in witness[Payload[d]]
             /\ Manifest[Selected] \in stored[r]
             /\ \A d \in Selected : Payload[d] \in stored[r]
             /\ D!Lose(r)
       /\ UNCHANGED registryVars
       /\ stage' = "disk_lost"
    \/ /\ stage = "disk_lost"
       /\ R!Crash("A")
       /\ UNCHANGED storeVars
       /\ stage' = "worker_crashed"
    \/ /\ stage = "worker_crashed"
       /\ R!Recover("A")
       /\ UNCHANGED storeVars
       /\ stage' = "worker_recovered"
    \/ /\ stage = "worker_recovered"
       /\ SurvivingSelected
       /\ R!Receive("A", "helper")
       /\ UNCHANGED storeVars
       /\ stage' = "received"
    \/ /\ stage = "received"
       /\ SurvivingSelected
       /\ Commit("A", Selected)
       /\ stage' = "reused"

UseSpec == UseInit /\ [][UseNext]_useVars
UseTypeOK == TypeOK /\ stage \in {"building", "committed", "disk_lost",
    "worker_crashed", "worker_recovered", "received", "reused"}
ReuseSafety == stage = "reused" =>
    /\ head["A"] = Selected
    /\ live # Replicas
    /\ "A" \in alive \intersect online
    /\ Selected \subseteq known["A"]
    /\ Manifest[Selected] \in acknowledged
    /\ SurvivingSelected

(* Coverage invariant: expect failure only after the entire sequence above. *)
NeverReusedAfterLoss == stage # "reused"
=============================================================================
