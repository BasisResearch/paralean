--------------------------- MODULE ShardHandover ---------------------------
(* W4-rest Design 2: dynamic shard topology and the three-step bucket move
   (docs/w4-rest-log.md). Every named action is one serializable FDB
   transaction unless it says otherwise.

   A shard operation runs under the process's operation lock: Load records the
   lease term; one commit action then mutates the snapshot and saves it under
   the lease (holder and term) and the head-generation CAS. The generation
   counter is abstracted to what the CAS reads: whether the head was saved
   since this process loaded it (headChanged). The in-memory copy is not
   stored: LoadedCurrent checks that every process able to pass the lease
   fence loaded the current head, so its copy equals the durable snapshot
   (this is also why the CAS is redundant). A mutation that removes a lease
   fence therefore commits fresh data, and is caught by the OwnerOnlyWrites
   observer at that commit.
   The bucket-keyed fence of the operation (work-route reservation, T4 claim)
   is read in the commit transaction. In the implementation the reservation or
   T4 transaction precedes the save in the same operation; a Begin between them
   is equivalent to a Begin just after the commit, because Export needs this
   process's operation lock or a newer term.

   Routing is adversarial: a request for any bucket may reach any shard's
   leader, which subsumes every stale bucket map a client may hold. A request
   that cannot be decided is answered with a retryable error, modelled by Abort
   (no durable effect). The per-shard logical clock and lease expiry are
   abstracted: a lease may lapse at any time and is then immediately acquired
   (Takeover, possibly by the same process) with term + 1, so a superseded
   process fails the holder/term fence; W4Scale checks the expiry fence. A
   validation runs outside the operation lock after its admission; J1 issue and
   J2 receipt are separate fenced transactions. *)
EXTENDS Naturals, FiniteSets

CONSTANTS Shards, InitialShards, MaxTerm, MaxMoves

None == "none"
NoHolder == <<"none", 0>>
Sentinel == <<"sentinel", 0>>
Absent == "absent"
Jobs == {"j1", "j2"}
(* Clients and the worker act on j1. j2 is already queued in b2 at B: it
   travels with any move of b2 and must survive a merge into B. *)
ClientJobs == {"j1"}
InitialSnap == [s \in Shards |-> [j \in Jobs |->
                  IF j = "j2" /\ s = "B" THEN "Q" ELSE Absent]]
Buckets == {"b1", "b2"}
BucketOf == [j \in Jobs |-> IF j = "j1" THEN "b1" ELSE "b2"]
VBucket == "b1"
InitialOwner == [b \in Buckets |-> IF b = "b1" THEN "A" ELSE "B"]
Moves == 1..MaxMoves
Procs == (InitialShards \X {1, 2}) \cup ((Shards \ InitialShards) \X {1})
S(p) == p[1]
Empty == [j \in Jobs |-> Absent]

VARIABLES members, holder, term, bucket,
          moveState, moveBucket, moveSrc, moveDst,
          snap, handoff,
          busy, headChanged, opTerm,
          vrun, vterm, j1, j1Index, receipt, receiptWrites,
          holds, ack, admitted,
          writesOK, retiredWrite, srcKilled, dstKilled, movedRunning,
          finishedAfterMove, receiptWhileMoving

lease == <<members, holder, term>>
topo == <<bucket, moveState, moveBucket, moveSrc, moveDst>>
durable == <<snap, handoff>>
proc == <<busy, headChanged, opTerm>>
valid == <<vrun, vterm, j1, j1Index, receipt, receiptWrites>>
client == <<holds, ack, admitted>>
ghost == <<writesOK, retiredWrite, srcKilled, dstKilled, movedRunning,
           finishedAfterMove, receiptWhileMoving>>
vars == <<lease, topo, durable, proc, valid, client, ghost>>

(* --- Guards. Each is named so a mutation can remove exactly one. --- *)
LeaseFence(p) == holder[S(p)] = p /\ term[S(p)] = opTerm[p]
SaveFence(p) == LeaseFence(p)
ExportFence(p) == LeaseFence(p)
CasOK(p) == ~headChanged[p]
(* The shard-epoch fence on bucket-keyed writes and on definite answers. *)
ReserveOK(s, b) == bucket[b].shard = s /\ bucket[b].moving = 0
T4OK(s, b) == bucket[b].shard = s /\ bucket[b].moving = 0
AnswerOK(s, b) == bucket[b].shard = s /\ bucket[b].moving = 0
AdmitOK(s, b) == bucket[b].shard = s /\ bucket[b].moving = 0
J1OK(s, b) == bucket[b].shard = s /\ bucket[b].moving = 0
(* J2 may land while the move is still Prepared: that is the drain. *)
ReceiptOK(s, b) == bucket[b].shard = s
Drained(p, b) == ~(vrun[p] \in {"admitted", "issued"} /\ VBucket = b)
HandoffOK(m) == moveState[m] = "Exported"
RemoveOwnsNothing(s) == \A b \in Buckets : bucket[b].shard # s
RemoveNoMove(s) == \A m \in Moves :
  moveState[m] \in {"Prepared", "Exported"} => s \notin {moveSrc[m], moveDst[m]}

(* --- Independent observer for OwnerOnlyWrites (not reused by any guard). --- *)
CurrentLeader(p, t) == holder[S(p)] = p /\ term[S(p)] = t
WriterOK(p, t, b) == bucket[b].shard = S(p) /\ CurrentLeader(p, t)
Changed(s, new) == {j \in Jobs : snap[s][j] # new[j]}

Init ==
  /\ members = [s \in Shards |-> IF s \in InitialShards THEN "Active" ELSE "Absent"]
  /\ holder = [s \in Shards |-> IF s \in InitialShards THEN <<s, 1>> ELSE NoHolder]
  /\ term = [s \in Shards |-> IF s \in InitialShards THEN 1 ELSE 0]
  /\ bucket = [b \in Buckets |-> [shard |-> InitialOwner[b], epoch |-> 0, moving |-> 0]]
  /\ moveState = [m \in Moves |-> "none"]
  /\ moveBucket = [m \in Moves |-> None]
  /\ moveSrc = [m \in Moves |-> None]
  /\ moveDst = [m \in Moves |-> None]
  /\ snap = InitialSnap
  /\ handoff = [m \in Moves |-> Empty]
  /\ busy = [p \in Procs |-> FALSE]
  /\ headChanged = [p \in Procs |-> FALSE]
  /\ opTerm = [p \in Procs |-> 0]
  /\ vrun = [p \in Procs |-> "idle"]
  /\ vterm = [p \in Procs |-> 0]
  /\ j1 = FALSE
  /\ j1Index = None
  /\ receipt = FALSE
  /\ receiptWrites = 0
  /\ holds = [j \in Jobs |-> FALSE]
  /\ ack = [j \in Jobs |-> "none"]
  /\ admitted = [j \in Jobs |-> IF j = "j2" THEN 1 ELSE 0]
  /\ writesOK = TRUE
  /\ retiredWrite = FALSE
  /\ srcKilled = [m \in Moves |-> FALSE]
  /\ dstKilled = [m \in Moves |-> FALSE]
  /\ movedRunning = [j \in Jobs |-> FALSE]
  /\ finishedAfterMove = FALSE
  /\ receiptWhileMoving = FALSE

(* --- Leases. --- *)
Takeover(p) ==
  LET s == S(p) IN
  /\ members[s] = "Active"
  /\ holder[s] # Sentinel
  /\ term[s] < MaxTerm
  /\ holder' = [holder EXCEPT ![s] = p]
  /\ term' = [term EXCEPT ![s] = @ + 1]
  /\ UNCHANGED <<members, topo, durable, proc, valid, client, ghost>>

(* A process dies: its operation and its in-flight validation vanish. *)
Kill(p) ==
  LET s == S(p) IN
  /\ busy[p] \/ vrun[p] # "idle" \/ holder[s] = p
  /\ busy' = [busy EXCEPT ![p] = FALSE]
  /\ headChanged' = [headChanged EXCEPT ![p] = FALSE]
  /\ opTerm' = [opTerm EXCEPT ![p] = 0]
  /\ vrun' = [vrun EXCEPT ![p] = "idle"]
  /\ vterm' = [vterm EXCEPT ![p] = 0]
  /\ srcKilled' = [m \in Moves |-> srcKilled[m]
                    \/ (holder[s] = p /\ moveState[m] = "Prepared" /\ moveSrc[m] = s)]
  /\ dstKilled' = [m \in Moves |-> dstKilled[m]
                    \/ (holder[s] = p /\ moveState[m] = "Exported" /\ moveDst[m] = s)]
  /\ UNCHANGED <<lease, topo, durable, j1, j1Index, receipt, receiptWrites,
                 client, writesOK, retiredWrite, movedRunning,
                 finishedAfterMove, receiptWhileMoving>>

(* --- Operations under the operation lock. --- *)
Load(p) ==
  LET s == S(p) IN
  /\ ~busy[p]
  /\ members[s] = "Active"
  /\ holder[s] = p
  /\ busy' = [busy EXCEPT ![p] = TRUE]
  /\ headChanged' = [headChanged EXCEPT ![p] = FALSE]
  /\ opTerm' = [opTerm EXCEPT ![p] = term[s]]
  /\ UNCHANGED <<lease, topo, durable, valid, client, ghost>>

EndOp(p) ==
  /\ busy' = [busy EXCEPT ![p] = FALSE]
  /\ headChanged' = [headChanged EXCEPT ![p] = FALSE]
  /\ opTerm' = [opTerm EXCEPT ![p] = 0]

(* Retryable answer, a failed fence or a lost commit: nothing durable. *)
Abort(p) ==
  /\ busy[p]
  /\ EndOp(p)
  /\ UNCHANGED <<lease, topo, durable, valid, client, ghost>>

(* Save a changed snapshot; the observer checks every changed job. *)
Save(p, new) ==
  /\ snap' = [snap EXCEPT ![S(p)] = new]
  /\ writesOK' = (writesOK /\ \A j \in Changed(S(p), new) :
                                 WriterOK(p, opTerm[p], BucketOf[j]))
  /\ retiredWrite' = (retiredWrite \/ members[S(p)] = "Retired")
  /\ busy' = [busy EXCEPT ![p] = FALSE]
  /\ opTerm' = [opTerm EXCEPT ![p] = 0]
  /\ headChanged' = [q \in Procs |-> IF q = p THEN FALSE
                                      ELSE headChanged[q] \/ S(q) = S(p)]

Submit(p, j) ==
  /\ busy[p]
  /\ snap[S(p)][j] = Absent
  /\ admitted[j] < 2
  /\ ReserveOK(S(p), BucketOf[j])
  /\ SaveFence(p)
  /\ CasOK(p)
  /\ Save(p, [snap[S(p)] EXCEPT ![j] = "Q"])
  /\ admitted' = [admitted EXCEPT ![j] = @ + 1]
  /\ UNCHANGED <<lease, topo, handoff, valid, holds, ack, srcKilled,
                 dstKilled, movedRunning, finishedAfterMove,
                 receiptWhileMoving>>

(* Poll: the T4 claim and the assignment commit together. *)
Assign(p, j) ==
  /\ busy[p]
  /\ snap[S(p)][j] = "Q"
  /\ ~holds[j]
  /\ ack[j] = "none"
  /\ T4OK(S(p), BucketOf[j])
  /\ SaveFence(p)
  /\ CasOK(p)
  /\ Save(p, [snap[S(p)] EXCEPT ![j] = "R"])
  /\ holds' = [holds EXCEPT ![j] = TRUE]
  /\ UNCHANGED <<lease, topo, handoff, valid, ack, admitted, srcKilled,
                 dstKilled, movedRunning, finishedAfterMove,
                 receiptWhileMoving>>

Finish(p, j) ==
  /\ busy[p]
  /\ holds[j]
  /\ ack[j] = "none"
  /\ snap[S(p)][j] = "R"
  /\ SaveFence(p)
  /\ CasOK(p)
  /\ Save(p, [snap[S(p)] EXCEPT ![j] = "D"])
  /\ holds' = [holds EXCEPT ![j] = FALSE]
  /\ ack' = [ack EXCEPT ![j] = "ok"]
  /\ finishedAfterMove' = (finishedAfterMove \/ movedRunning[j])
  /\ UNCHANGED <<lease, topo, handoff, valid, admitted, srcKilled, dstKilled,
                 movedRunning, receiptWhileMoving>>

(* A definite "unknown work request" answer. The response is returned only
   after the operation's save commits, so it is fenced like a save. *)
RefuseFinish(p, j) ==
  /\ busy[p]
  /\ holds[j]
  /\ ack[j] = "none"
  /\ snap[S(p)][j] # "R"
  /\ AnswerOK(S(p), BucketOf[j])
  /\ SaveFence(p)
  /\ CasOK(p)
  /\ holds' = [holds EXCEPT ![j] = FALSE]
  /\ ack' = [ack EXCEPT ![j] = "refused"]
  /\ retiredWrite' = (retiredWrite \/ members[S(p)] = "Retired")
  /\ EndOp(p)
  /\ UNCHANGED <<lease, topo, durable, valid, admitted, writesOK, srcKilled,
                 dstKilled, movedRunning, finishedAfterMove,
                 receiptWhileMoving>>

(* A bucket-free shard-local write (worker registration, a NoWork poll token). *)
Touch(p) ==
  /\ busy[p]
  /\ SaveFence(p)
  /\ CasOK(p)
  /\ retiredWrite' = (retiredWrite \/ members[S(p)] = "Retired")
  /\ EndOp(p)
  /\ UNCHANGED <<lease, topo, durable, valid, client, writesOK, srcKilled,
                 dstKilled, movedRunning, finishedAfterMove,
                 receiptWhileMoving>>

(* --- Move protocol. --- *)
Begin(m, b, dst) ==
  /\ moveState[m] = "none"
  /\ \A n \in Moves : n < m => moveState[n] = "Done"
  /\ bucket[b].moving = 0
  /\ members[dst] = "Active"
  /\ bucket[b].shard # dst
  /\ members[bucket[b].shard] = "Active"
  /\ moveState' = [moveState EXCEPT ![m] = "Prepared"]
  /\ moveBucket' = [moveBucket EXCEPT ![m] = b]
  /\ moveSrc' = [moveSrc EXCEPT ![m] = bucket[b].shard]
  /\ moveDst' = [moveDst EXCEPT ![m] = dst]
  /\ bucket' = [bucket EXCEPT ![b].moving = m]
  /\ UNCHANGED <<lease, durable, proc, valid, client, ghost>>

Export(p, m) ==
  LET s == S(p)
      b == moveBucket[m]
      kept == [j \in Jobs |-> IF BucketOf[j] = b THEN Absent ELSE snap[S(p)][j]]
      out == [j \in Jobs |-> IF BucketOf[j] = b THEN snap[S(p)][j] ELSE Absent]
  IN
  /\ busy[p]
  /\ moveState[m] = "Prepared"
  /\ moveSrc[m] = s
  /\ Drained(p, b)
  /\ ExportFence(p)
  /\ CasOK(p)
  /\ Save(p, kept)
  /\ handoff' = [handoff EXCEPT ![m] = out]
  /\ bucket' = [bucket EXCEPT ![b] = [shard |-> moveDst[m],
                                      epoch |-> @.epoch + 1, moving |-> m]]
  /\ j1Index' = IF VBucket = b /\ j1Index = s THEN moveDst[m] ELSE j1Index
  /\ moveState' = [moveState EXCEPT ![m] = "Exported"]
  /\ movedRunning' = [j \in Jobs |-> movedRunning[j] \/ out[j] = "R"]
  /\ UNCHANGED <<lease, moveBucket, moveSrc, moveDst, vrun, vterm, j1,
                 receipt, receiptWrites, client, srcKilled, dstKilled,
                 finishedAfterMove, receiptWhileMoving>>

Import(p, m) ==
  LET s == S(p)
      b == moveBucket[m]
      merged == [j \in Jobs |-> IF handoff[m][j] # Absent
                                  THEN handoff[m][j] ELSE snap[S(p)][j]]
  IN
  /\ busy[p]
  /\ HandoffOK(m)
  /\ moveDst[m] = s
  /\ SaveFence(p)
  /\ CasOK(p)
  /\ Save(p, merged)
  /\ handoff' = [handoff EXCEPT ![m] = Empty]
  /\ bucket' = [bucket EXCEPT ![b].moving = 0]
  /\ moveState' = [moveState EXCEPT ![m] = "Done"]
  /\ UNCHANGED <<lease, moveBucket, moveSrc, moveDst, valid, client,
                 srcKilled, dstKilled, movedRunning, finishedAfterMove,
                 receiptWhileMoving>>

(* --- Topology changes by the authority. --- *)
AddShard(s) ==
  /\ members[s] = "Absent"
  /\ members' = [members EXCEPT ![s] = "Active"]
  /\ UNCHANGED <<holder, term, topo, durable, proc, valid, client, ghost>>

RemoveShard(s) ==
  /\ members[s] = "Active"
  /\ RemoveOwnsNothing(s)
  /\ RemoveNoMove(s)
  /\ members' = [members EXCEPT ![s] = "Retired"]
  /\ holder' = [holder EXCEPT ![s] = Sentinel]
  /\ UNCHANGED <<term, topo, durable, proc, valid, client, ghost>>

(* --- Validation: admitted under the operation lock, then outside it. --- *)
ValAdmit(p) ==
  LET s == S(p) IN
  /\ ~busy[p]
  /\ members[s] = "Active"
  /\ holder[s] = p
  /\ vrun[p] = "idle"
  /\ ~receipt
  /\ AdmitOK(s, VBucket)
  /\ vrun' = [vrun EXCEPT ![p] = "admitted"]
  /\ vterm' = [vterm EXCEPT ![p] = term[s]]
  /\ UNCHANGED <<lease, topo, durable, proc, j1, j1Index, receipt,
                 receiptWrites, client, ghost>>

IssueJ1(p) ==
  LET s == S(p) IN
  /\ vrun[p] = "admitted"
  /\ holder[s] = p /\ term[s] = vterm[p]
  /\ J1OK(s, VBucket)
  /\ vrun' = [vrun EXCEPT ![p] = "issued"]
  /\ j1' = TRUE
  /\ j1Index' = s
  /\ writesOK' = (writesOK /\ WriterOK(p, vterm[p], VBucket))
  /\ retiredWrite' = (retiredWrite \/ members[s] = "Retired")
  /\ UNCHANGED <<lease, topo, durable, proc, vterm, receipt, receiptWrites,
                 client, srcKilled, dstKilled, movedRunning,
                 finishedAfterMove, receiptWhileMoving>>

(* J2 is write-once: a second dispatch reads back the first receipt. *)
RecordJ2(p) ==
  LET s == S(p) IN
  /\ vrun[p] = "issued"
  /\ holder[s] = p /\ term[s] = vterm[p]
  /\ ReceiptOK(s, VBucket)
  /\ vrun' = [vrun EXCEPT ![p] = "idle"]
  /\ vterm' = [vterm EXCEPT ![p] = 0]
  /\ receipt' = TRUE
  /\ receiptWrites' = IF receipt THEN receiptWrites ELSE receiptWrites + 1
  /\ writesOK' = (writesOK /\ (receipt \/ WriterOK(p, vterm[p], VBucket)))
  /\ retiredWrite' = (retiredWrite \/ members[s] = "Retired")
  /\ receiptWhileMoving' = (receiptWhileMoving
                             \/ (~receipt /\ bucket[VBucket].moving # 0))
  /\ UNCHANGED <<lease, topo, durable, proc, j1, j1Index, client, srcKilled,
                 dstKilled, movedRunning, finishedAfterMove>>

(* A fence refused J1 or J2, the validator failed, or the client gave up. *)
ValFail(p) ==
  /\ vrun[p] # "idle"
  /\ vrun' = [vrun EXCEPT ![p] = "idle"]
  /\ vterm' = [vterm EXCEPT ![p] = 0]
  /\ UNCHANGED <<lease, topo, durable, proc, j1, j1Index, receipt,
                 receiptWrites, client, ghost>>

Next ==
  \/ \E s \in Shards : AddShard(s) \/ RemoveShard(s)
  \/ \E p \in Procs : Takeover(p) \/ Kill(p) \/ Load(p) \/ Abort(p) \/ Touch(p)
                      \/ ValAdmit(p) \/ IssueJ1(p) \/ RecordJ2(p) \/ ValFail(p)
  \/ \E p \in Procs, j \in ClientJobs : Submit(p, j) \/ Assign(p, j) \/ Finish(p, j)
                                  \/ RefuseFinish(p, j)
  \/ \E p \in Procs, m \in Moves : Export(p, m) \/ Import(p, m)
  \/ \E m \in Moves, b \in Buckets, s \in Shards : Begin(m, b, s)
Spec == Init /\ [][Next]_vars

(* --- Safety. --- *)
SnapLocs(j) == {s \in Shards : snap[s][j] # Absent}
HandoffLocs(j) == {m \in Moves : handoff[m][j] # Absent}
LocCount(j) == Cardinality(SnapLocs(j)) + Cardinality(HandoffLocs(j))
StatesOf(j) == {snap[s][j] : s \in SnapLocs(j)} \cup {handoff[m][j] : m \in HandoffLocs(j)}

NoLoss == \A j \in Jobs : admitted[j] > 0 => LocCount(j) >= 1
NoDup == \A j \in Jobs : LocCount(j) <= 1 /\ admitted[j] <= 1
(* Where a bucket's jobs may live at each move state. *)
Placement ==
  /\ \A j \in Jobs, s \in Shards :
       snap[s][j] # Absent =>
         /\ bucket[BucketOf[j]].shard = s
         /\ \/ bucket[BucketOf[j]].moving = 0
            \/ moveState[bucket[BucketOf[j]].moving] = "Prepared"
  /\ \A j \in Jobs, m \in Moves :
       handoff[m][j] # Absent =>
         /\ moveState[m] = "Exported"
         /\ bucket[BucketOf[j]].shard = moveDst[m]
         /\ bucket[BucketOf[j]].moving = m
  /\ j1 => j1Index = bucket[VBucket].shard
OwnerOnlyWrites == writesOK
FinishApplies == \A j \in Jobs :
  /\ ack[j] = "refused" => "R" \notin StatesOf(j)
  /\ ack[j] = "ok" => StatesOf(j) = {"D"}
ReceiptOnce == receiptWrites <= 1
(* A live in-flight validation past J1 runs at the bucket's owner. *)
NoOrphanValidation == \A p \in Procs :
  (vrun[p] = "issued" /\ CurrentLeader(p, vterm[p]))
    => bucket[VBucket].shard = S(p)
(* Whoever can still pass the lease fence loaded the current head. *)
LoadedCurrent == \A p \in Procs :
  busy[p] /\ CurrentLeader(p, opTerm[p]) => ~headChanged[p]
RemovedShardInert ==
  /\ ~retiredWrite
  /\ \A s \in Shards : members[s] = "Retired" =>
       /\ \A b \in Buckets : bucket[b].shard # s
       /\ snap[s] = Empty
       /\ \A m \in Moves : moveState[m] \in {"Prepared", "Exported"}
                             => moveDst[m] # s

(* --- Reachability witnesses: each must be violated. --- *)
NeverMoveDone == \A m \in Moves : moveState[m] # "Done"
NeverSrcKilledMoveDone == \A m \in Moves : ~(srcKilled[m] /\ moveState[m] = "Done")
NeverDstKilledMoveDone == \A m \in Moves : ~(dstKilled[m] /\ moveState[m] = "Done")
NeverFinishAfterMove == ~finishedAfterMove
NeverMovedToAdded == \A m \in Moves :
  ~(moveDst[m] \in Shards \ InitialShards /\ moveState[m] = "Done")
NeverRemoved == \A s \in InitialShards : members[s] # "Retired"
NeverReceiptWhileMoving == ~receiptWhileMoving
=============================================================================
