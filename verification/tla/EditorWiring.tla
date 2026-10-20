----------------------------- MODULE EditorWiring -----------------------------
EXTENDS Naturals, FiniteSets
CONSTANT Mode
VARIABLES version, policy, generation, captured, receipt, authorized, published,
          sessionPolicy, sessionLive, prepared, complete, validPlans, renamed,
          replayVerified, capsuleMatches, overlay
vars == <<version, policy, generation, captured, receipt, authorized, published,
          sessionPolicy, sessionLive, prepared, complete, validPlans, renamed,
          replayVerified, capsuleMatches, overlay>>
Stamp == <<version, policy, generation>>
Workspaces == {"a", "b"}
Init ==
  /\ version = 0 /\ policy = 0 /\ generation = 0
  /\ captured = <<2, 2, 2>> /\ receipt = FALSE /\ authorized = FALSE
  /\ published = {} /\ sessionPolicy = 0 /\ sessionLive = TRUE
  /\ prepared = {} /\ complete = FALSE /\ validPlans = FALSE /\ renamed = {}
  /\ replayVerified = FALSE /\ capsuleMatches = FALSE /\ overlay = FALSE

Edit ==
  /\ version = 0 /\ version' = 1
  /\ UNCHANGED <<policy, generation, captured, receipt, authorized, published,
       sessionPolicy, sessionLive, prepared, complete, validPlans, renamed,
       replayVerified, capsuleMatches, overlay>>
Restart ==
  /\ generation = 0 /\ generation' = 1
  /\ UNCHANGED <<version, policy, captured, receipt, authorized, published,
       sessionPolicy, sessionLive, prepared, complete, validPlans, renamed,
       replayVerified, capsuleMatches, overlay>>
FenceSession == FALSE
PushPolicy ==
  /\ policy = 0 /\ policy' = 1 /\ sessionLive' = FenceSession
  /\ UNCHANGED <<version, generation, captured, receipt, authorized, published,
       sessionPolicy, prepared, complete, validPlans, renamed,
       replayVerified, capsuleMatches, overlay>>
Capture ==
  /\ captured' = Stamp /\ receipt' = FALSE
  /\ UNCHANGED <<version, policy, generation, authorized, published,
       sessionPolicy, sessionLive, prepared, complete, validPlans, renamed,
       replayVerified, capsuleMatches, overlay>>
Validate ==
  /\ captured = Stamp /\ receipt' = TRUE
  /\ UNCHANGED <<version, policy, generation, captured, authorized, published,
       sessionPolicy, sessionLive, prepared, complete, validPlans, renamed,
       replayVerified, capsuleMatches, overlay>>
Authorize ==
  /\ authorized' = TRUE
  /\ UNCHANGED <<version, policy, generation, captured, receipt, published,
       sessionPolicy, sessionLive, prepared, complete, validPlans, renamed,
       replayVerified, capsuleMatches, overlay>>
ReceiptOK == receipt
ActionOK == authorized
FreshOK == captured = Stamp
Publish ==
  /\ ReceiptOK /\ ActionOK /\ FreshOK
  /\ published' = published \cup {<<receipt, authorized, captured = Stamp>>}
  /\ UNCHANGED <<version, policy, generation, captured, receipt, authorized,
       sessionPolicy, sessionLive, prepared, complete, validPlans, renamed,
       replayVerified, capsuleMatches, overlay>>
Prepare ==
  /\ prepared' \in SUBSET Workspaces
  /\ complete' \in BOOLEAN /\ validPlans' \in BOOLEAN
  /\ captured' = Stamp
  /\ UNCHANGED <<version, policy, generation, receipt, authorized, published,
       sessionPolicy, sessionLive, renamed, replayVerified, capsuleMatches, overlay>>
AllPrepared == prepared = Workspaces
InventoryOK == complete
PlansOK == validPlans
RenameSet == Workspaces
CommitRename ==
  /\ AllPrepared /\ InventoryOK /\ PlansOK /\ FreshOK
  /\ renamed' = RenameSet
  /\ published' = published \cup {<<prepared = Workspaces, complete,
                                    validPlans, captured = Stamp>>}
  /\ UNCHANGED <<version, policy, generation, captured, receipt, authorized,
       sessionPolicy, sessionLive, prepared, complete, validPlans,
       replayVerified, capsuleMatches, overlay>>
Replay ==
  /\ replayVerified' \in BOOLEAN /\ capsuleMatches' \in BOOLEAN
  /\ overlay = FALSE
  /\ UNCHANGED <<version, policy, generation, captured, receipt, authorized, published,
       sessionPolicy, sessionLive, prepared, complete, validPlans, renamed, overlay>>
ReplayOK == replayVerified
IdentityOK == capsuleMatches
AcceptOverlay ==
  /\ ReplayOK /\ IdentityOK /\ overlay' = TRUE
  /\ UNCHANGED <<version, policy, generation, captured, receipt, authorized, published,
       sessionPolicy, sessionLive, prepared, complete, validPlans, renamed,
       replayVerified, capsuleMatches>>
Next ==
  CASE Mode = "publication" -> Edit \/ Restart \/ PushPolicy \/ Capture \/ Validate \/ Authorize \/ Publish
    [] Mode = "rename" -> Edit \/ Restart \/ PushPolicy \/ Prepare \/ CommitRename
    [] Mode = "replay" -> Replay \/ AcceptOverlay
Spec == Init /\ [][Next]_vars
PublicationSafe == Mode # "publication" \/ published \subseteq {<<TRUE, TRUE, TRUE>>}
SessionFenced == sessionLive => sessionPolicy = policy
RenameSafe == Mode # "rename" \/ published \subseteq {<<TRUE, TRUE, TRUE, TRUE>>}
RenameAtomic == renamed = {} \/ renamed = Workspaces
OverlaySafe == overlay => replayVerified /\ capsuleMatches
NeverPublished == published = {}
NeverRenamed == renamed = {}
NeverOverlay == ~overlay
=============================================================================
