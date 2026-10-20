---------------------------- MODULE W4History ----------------------------
(* Bounded history retirement for one controller shard. A single FDB action
   writes immutable replay rows and prunes the current snapshot atomically.
   Old snapshot chunks and replay rows are retained. Poll rows store the first
   selection, not a frozen Work response: replay checks current assignment. *)
EXTENDS Naturals

CONSTANTS Workers, Payloads, MaxTick, Grace
VARIABLES tick, holder, term, expiry, begun, status, payload, order,
          workReplay, replayPayload, workEffects, identitySafe, replaySafe,
          pollSnapshot, pollReplay, pollWorker, pollFirst, pollEpoch,
          pollEffects, pollSafe, wrongWorkerAccepted, owner, epoch,
          lastPollWork, compactFenced, pendingLost, oldSnapshotLive,
          workFinishedTick, pollStableTick, lateWorkReplay, latePollReplay,
          gcEnabled, replayOffSeen, graceSafe, cancelled,
          cancelOverlaySafe, postCompactCancelReplay
vars == <<tick, holder, term, expiry, begun, status, payload, order,
          workReplay, replayPayload, workEffects, identitySafe, replaySafe,
          pollSnapshot, pollReplay, pollWorker, pollFirst, pollEpoch,
          pollEffects, pollSafe, wrongWorkerAccepted, owner, epoch,
          lastPollWork, compactFenced, pendingLost, oldSnapshotLive,
          workFinishedTick, pollStableTick, lateWorkReplay, latePollReplay,
          gcEnabled, replayOffSeen, graceSafe, cancelled, cancelOverlaySafe, postCompactCancelReplay>>

None == "none"
LeaseOK(w) == holder = w /\ tick < expiry
FenceOK(w) == LeaseOK(w) /\ begun[w] = term
TerminalOK == status = "done"
WorkKnown == status # "absent" \/ workReplay
PollKnown == pollSnapshot \/ pollReplay
DuplicateResult == IF cancelled THEN "cancelled" ELSE "done"
StoredPayload == IF status # "absent" THEN payload ELSE replayPayload
FirstSelection(w) == IF status = "pending" /\ owner = w THEN "r" ELSE None
ReplaySelection(w) == IF pollFirst = "r" /\ status = "pending"
                         /\ owner = w /\ epoch = pollEpoch
                      THEN "r" ELSE None

Init ==
  /\ tick = 1
  /\ holder = None
  /\ term = 0
  /\ expiry = 0
  /\ begun = [w \in Workers |-> 0]
  /\ status = "absent"
  /\ payload = None
  /\ order = {}
  /\ workReplay = FALSE
  /\ replayPayload = None
  /\ workEffects = 0
  /\ identitySafe = TRUE
  /\ replaySafe = TRUE
  /\ pollSnapshot = FALSE
  /\ pollReplay = FALSE
  /\ pollWorker = None
  /\ pollFirst = None
  /\ pollEpoch = 0
  /\ pollEffects = 0
  /\ pollSafe = TRUE
  /\ wrongWorkerAccepted = FALSE
  /\ owner = None
  /\ epoch = 0
  /\ lastPollWork = None
  /\ compactFenced = TRUE
  /\ pendingLost = FALSE
  /\ oldSnapshotLive = TRUE
  /\ workFinishedTick = 0
  /\ pollStableTick = 0
  /\ lateWorkReplay = FALSE
  /\ latePollReplay = FALSE
  /\ gcEnabled = TRUE
  /\ replayOffSeen = FALSE
  /\ graceSafe = TRUE
  /\ cancelled = FALSE
  /\ cancelOverlaySafe = TRUE
  /\ postCompactCancelReplay = FALSE

Advance ==
  /\ tick < MaxTick
  /\ tick' = tick + 1
  /\ UNCHANGED <<holder, term, expiry, begun, status, payload, order,
                 workReplay, replayPayload, workEffects, identitySafe,
                 replaySafe, pollSnapshot, pollReplay, pollWorker, pollFirst,
                 pollEpoch, pollEffects, pollSafe, wrongWorkerAccepted, owner,
                 epoch, lastPollWork, compactFenced, pendingLost,
                 oldSnapshotLive, workFinishedTick, pollStableTick,
                 lateWorkReplay, latePollReplay, gcEnabled, replayOffSeen, graceSafe, cancelled, cancelOverlaySafe, postCompactCancelReplay>>

Acquire(w) ==
  /\ expiry <= tick
  /\ holder' = w
  /\ term' = term + 1
  /\ expiry' = tick + 1
  /\ UNCHANGED <<tick, begun, status, payload, order, workReplay,
                 replayPayload, workEffects, identitySafe, replaySafe,
                 pollSnapshot, pollReplay, pollWorker, pollFirst, pollEpoch,
                 pollEffects, pollSafe, wrongWorkerAccepted, owner, epoch,
                 lastPollWork, compactFenced, pendingLost, oldSnapshotLive,
                 workFinishedTick, pollStableTick, lateWorkReplay,
                 latePollReplay, gcEnabled, replayOffSeen, graceSafe, cancelled, cancelOverlaySafe, postCompactCancelReplay>>

Begin(w) ==
  /\ LeaseOK(w)
  /\ begun' = [begun EXCEPT ![w] = term]
  /\ UNCHANGED <<tick, holder, term, expiry, status, payload, order,
                 workReplay, replayPayload, workEffects, identitySafe,
                 replaySafe, pollSnapshot, pollReplay, pollWorker, pollFirst,
                 pollEpoch, pollEffects, pollSafe, wrongWorkerAccepted, owner,
                 epoch, lastPollWork, compactFenced, pendingLost,
                 oldSnapshotLive, workFinishedTick, pollStableTick,
                 lateWorkReplay, latePollReplay, gcEnabled, replayOffSeen, graceSafe, cancelled, cancelOverlaySafe, postCompactCancelReplay>>

Submit(w, p) ==
  /\ LeaseOK(w)
  /\ p \in Payloads
  /\ (~WorkKnown \/ p = StoredPayload)
  /\ status' = IF WorkKnown THEN status ELSE "pending"
  /\ payload' = IF WorkKnown THEN payload ELSE p
  /\ order' = IF WorkKnown THEN order ELSE {"r"}
  /\ owner' = IF WorkKnown THEN owner ELSE w
  /\ epoch' = IF WorkKnown THEN epoch ELSE 1
  /\ workEffects' = IF WorkKnown THEN workEffects ELSE workEffects + 1
  /\ identitySafe' = (identitySafe /\ (~WorkKnown \/ p = StoredPayload))
  /\ replaySafe' = (replaySafe /\ (~workReplay \/ WorkKnown))
  /\ lateWorkReplay' = (lateWorkReplay \/ workReplay)
  /\ replayOffSeen' = (replayOffSeen \/ (workReplay /\ ~gcEnabled))
  /\ cancelOverlaySafe' = (cancelOverlaySafe
      /\ (~(WorkKnown /\ cancelled) \/ DuplicateResult = "cancelled"))
  /\ postCompactCancelReplay' = (postCompactCancelReplay
                                   \/ (workReplay /\ cancelled))
  /\ UNCHANGED <<tick, holder, term, expiry, begun, workReplay,
                 replayPayload, pollSnapshot, pollReplay, pollWorker, pollFirst,
                 pollEpoch, pollEffects, pollSafe, wrongWorkerAccepted,
                 lastPollWork, compactFenced, pendingLost, oldSnapshotLive,
                 workFinishedTick, pollStableTick, latePollReplay,
                 gcEnabled, graceSafe, cancelled>>

Finish(w) ==
  /\ LeaseOK(w)
  /\ status = "pending"
  /\ status' = "done"
  /\ owner' = None
  /\ workFinishedTick' = tick
  /\ UNCHANGED <<tick, holder, term, expiry, begun, payload, order,
                 workReplay, replayPayload, workEffects, identitySafe,
                 replaySafe, pollSnapshot, pollReplay, pollWorker, pollFirst,
                 pollEpoch, pollEffects, pollSafe, wrongWorkerAccepted, epoch,
                 lastPollWork, compactFenced, pendingLost, oldSnapshotLive,
                 pollStableTick, lateWorkReplay, latePollReplay, gcEnabled, replayOffSeen, graceSafe, cancelled, cancelOverlaySafe, postCompactCancelReplay>>

Poll(w) ==
  /\ LeaseOK(w)
  /\ (~PollKnown \/ pollWorker = w)
  /\ pollSnapshot' = IF PollKnown THEN pollSnapshot ELSE TRUE
  /\ pollWorker' = IF PollKnown THEN pollWorker ELSE w
  /\ pollFirst' = IF PollKnown THEN pollFirst ELSE FirstSelection(w)
  /\ pollEpoch' = IF PollKnown THEN pollEpoch ELSE epoch
  /\ pollEffects' = IF PollKnown THEN pollEffects ELSE pollEffects + 1
  /\ pollStableTick' = IF PollKnown THEN pollStableTick
                        ELSE IF FirstSelection(w) = None THEN tick ELSE 0
  /\ lastPollWork' = IF PollKnown THEN ReplaySelection(w)
                       ELSE FirstSelection(w)
  /\ pollSafe' = (pollSafe /\ (~PollKnown \/ pollWorker = w))
  /\ wrongWorkerAccepted' = (wrongWorkerAccepted
                              \/ (PollKnown /\ pollWorker # w))
  /\ latePollReplay' = (latePollReplay \/ pollReplay)
  /\ replayOffSeen' = (replayOffSeen \/ (pollReplay /\ ~gcEnabled))
  /\ UNCHANGED <<tick, holder, term, expiry, begun, status, payload,
                 order, workReplay, replayPayload, workEffects, identitySafe,
                 replaySafe, pollReplay, owner, epoch, compactFenced,
                 pendingLost, oldSnapshotLive, workFinishedTick,
                 lateWorkReplay, gcEnabled, graceSafe, cancelled,
                 cancelOverlaySafe, postCompactCancelReplay>>

(* J3 cancellation overlays the immutable original terminal result. *)
CancelAfterCompact(w) ==
  /\ LeaseOK(w)
  /\ workReplay
  /\ ~cancelled
  /\ cancelled' = TRUE
  /\ UNCHANGED <<tick, holder, term, expiry, begun, status, payload, order,
                 workReplay, replayPayload, workEffects, identitySafe,
                 replaySafe, pollSnapshot, pollReplay, pollWorker, pollFirst,
                 pollEpoch, pollEffects, pollSafe, wrongWorkerAccepted, owner,
                 epoch, lastPollWork, compactFenced, pendingLost,
                 oldSnapshotLive, workFinishedTick, pollStableTick,
                 lateWorkReplay, latePollReplay, gcEnabled, replayOffSeen,
                 graceSafe, cancelOverlaySafe, postCompactCancelReplay>>

(* For a terminal job, this one transaction writes the exact work replay row,
   moves any poll marker, then removes only that terminal work/order entry. *)
Compact(w) ==
  /\ gcEnabled
  /\ FenceOK(w)
  /\ TerminalOK
  /\ tick >= workFinishedTick + Grace
  /\ (~pollSnapshot \/ pollFirst = "r"
       \/ tick >= pollStableTick + Grace)
  /\ ~workReplay
  /\ workReplay' = TRUE
  /\ replayPayload' = payload
  /\ status' = "absent"
  /\ order' = order \ {"r"}
  /\ pollReplay' = (pollReplay \/ pollSnapshot)
  /\ pollSnapshot' = FALSE
  /\ compactFenced' = (compactFenced /\ holder = w
                         /\ tick < expiry /\ begun[w] = term)
  /\ pendingLost' = (pendingLost \/ status = "pending")
  /\ graceSafe' = (graceSafe /\ tick >= workFinishedTick + Grace)
  /\ UNCHANGED <<tick, holder, term, expiry, begun, payload,
                 workEffects, identitySafe, replaySafe, pollWorker,
                 pollFirst, pollEpoch, pollEffects, pollSafe,
                 wrongWorkerAccepted, owner, epoch, lastPollWork,
                 oldSnapshotLive, workFinishedTick, pollStableTick,
                 lateWorkReplay, latePollReplay, gcEnabled, replayOffSeen, cancelled, cancelOverlaySafe, postCompactCancelReplay>>

(* A first NoWork token can be archived even before a job exists. *)
CompactNoWorkPoll(w) ==
  /\ gcEnabled
  /\ FenceOK(w)
  /\ pollSnapshot
  /\ pollFirst = None
  /\ tick >= pollStableTick + Grace
  /\ pollReplay' = TRUE
  /\ pollSnapshot' = FALSE
  /\ compactFenced' = (compactFenced /\ holder = w
                         /\ tick < expiry /\ begun[w] = term)
  /\ graceSafe' = (graceSafe /\ tick >= pollStableTick + Grace)
  /\ UNCHANGED <<tick, holder, term, expiry, begun, status, payload,
                 order, workReplay, replayPayload, workEffects, identitySafe,
                 replaySafe, pollWorker, pollFirst, pollEpoch, pollEffects,
                 pollSafe, wrongWorkerAccepted, owner, epoch, lastPollWork,
                 pendingLost, oldSnapshotLive, workFinishedTick,
                 pollStableTick, lateWorkReplay, latePollReplay,
                 gcEnabled, replayOffSeen, cancelled, cancelOverlaySafe, postCompactCancelReplay>>

DisableGc ==
  /\ gcEnabled
  /\ gcEnabled' = FALSE
  /\ UNCHANGED <<tick, holder, term, expiry, begun, status, payload, order,
                 workReplay, replayPayload, workEffects, identitySafe,
                 replaySafe, pollSnapshot, pollReplay, pollWorker, pollFirst,
                 pollEpoch, pollEffects, pollSafe, wrongWorkerAccepted, owner,
                 epoch, lastPollWork, compactFenced, pendingLost,
                 oldSnapshotLive, workFinishedTick, pollStableTick,
                 lateWorkReplay, latePollReplay, replayOffSeen, graceSafe, cancelled, cancelOverlaySafe, postCompactCancelReplay>>

Crash(w) ==
  /\ begun[w] # 0
  /\ begun' = [begun EXCEPT ![w] = 0]
  /\ UNCHANGED <<tick, holder, term, expiry, status, payload, order,
                 workReplay, replayPayload, workEffects, identitySafe,
                 replaySafe, pollSnapshot, pollReplay, pollWorker, pollFirst,
                 pollEpoch, pollEffects, pollSafe, wrongWorkerAccepted, owner,
                 epoch, lastPollWork, compactFenced, pendingLost,
                 oldSnapshotLive, workFinishedTick, pollStableTick,
                 lateWorkReplay, latePollReplay, gcEnabled, replayOffSeen, graceSafe, cancelled, cancelOverlaySafe, postCompactCancelReplay>>

Next == Advance \/ DisableGc
  \/ (\E w \in Workers : Acquire(w) \/ Begin(w) \/ Finish(w)
                           \/ Poll(w) \/ Compact(w) \/ CompactNoWorkPoll(w)
                           \/ CancelAfterCompact(w) \/ Crash(w))
  \/ (\E w \in Workers, p \in Payloads : Submit(w, p))
Spec == Init /\ [][Next]_vars

ReplayCovered == workEffects > 0 /\ status = "absent" => workReplay
PollCovered == pollEffects > 0 /\ ~pollSnapshot => pollReplay
NoDuplicateWork == workEffects <= 1
NoDuplicatePoll == pollEffects <= 1
ExactIdentity == identitySafe
ReplayRead == replaySafe
NoWrongWorker == ~wrongWorkerAccepted
PendingKept == ~pendingLost
FencedCompact == compactFenced
OldSnapshotRetained == oldSnapshotLive
OrderSound == (status = "absent" => order = {})
LogicalGrace == graceSafe
CancelOverlay == cancelOverlaySafe

NeverCompacted == ~workReplay
NeverPollCompacted == ~pollReplay
NeverReplayedAfterCompact == ~lateWorkReplay
NeverLatePoll == ~latePollReplay
NeverHandover == term <= 1
NeverReplayWithGcOff == ~replayOffSeen
NeverCancelledReplay == ~postCompactCancelReplay
=============================================================================
