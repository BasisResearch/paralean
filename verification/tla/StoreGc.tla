------------------------------ MODULE StoreGc ------------------------------
(* W4-rest design 1, physical P2/S3 object collection for one deployment, as
   built. Every named action is one serializable FDB transaction, except the
   S3 operations (Put, GarageExec), which act on the object store only. An S3
   object is present or absent. gcobj is `gcobj/<o>`: none, Sighted{t},
   Doomed, Deleting{n} or Gone{t, n}; gcref the reverse index; ocert the T6
   certificate. What metadata names an object (markers, move variants,
   tombstones, imports, catalogue records, pending jobs, pending anti-entropy
   events) is kept apart from the index, so a transaction that forgets its
   gcref entry is still checked against what it named.

   As built (deviations from the design text):
   - every referencing transaction (T1, T11, T8/T10, J1, T5s, T5, the
     anti-entropy import) refuses Doomed, Deleting and Gone ("Collected");
   - revival is its own transaction: read Gone{t, n}, re-PUT (or GET-verify
     presence), then clear gcobj only if it is still that exact Gone;
   - a sweep pass reads clock c0 and lists S3; it moves Gone{t} to Sighted
     when t < c0 and the object is in this pass's listing;
   - s3-guard admits a GC-key DELETE of a Doomed or Deleting key and writes
     Deleting{fresh nonce}; a forged GC-key request moves the state but
     Garage rejects its signature;
   - aepending references never abort: they clear Sighted only; receivers
     PUT through put_live, which refuses while Doomed/Deleting and revives
     after Gone.

   Fix found by the model (see TLA-GUARDS.md): s3-guard writes Gone only when
   no forwarded DELETE of that key can still execute (GoneQuiescent). With a
   retry after an unknown outcome, the earlier DELETE may run after Gone and
   a revival, deleting the revived bytes (`storegc_gone_with_inflight`).
   RequestDies abstracts the guard's request deadline.

   Atomic multi-group batches (BatchMode, StoreGcBatch.cfg): a controller-
   signed intent names the members (here both objects, as Publish members, in
   a chosen order). Each member's payload is PUT by the coordinator, its
   bound job envelope is recorded at J1 (a job referrer), J2 follows and the
   collector may release the job reference. T12 is one transaction: every
   member's unchanged T1 body (refusing Doomed/Deleting/Gone, writing its own
   referrer) plus `batch/<id>`, which references every member; a collected
   member aborts the whole batch, and the coordinator re-PUTs, revives the
   exact Gone and retries. On the receiver, the batch event's parts are
   staged under its aepending referrer, each member is fetched through
   put_live, and T13 imports all members in one transaction. *)
EXTENDS Integers, TLC

CONSTANTS Objects, Writers, CatIds, Grace, MaxClock, MaxFence, MaxPuts,
          MaxNonce, BatchMode

NoObj == "noobj"
NoCat == "nocat"
Principals == {"gc", "forged", "writer"}
AeEvent == "e"
Perm == "perm"

VARIABLES present, gcobj, gcref, ocert, clock, fence, puts,
          nonce, inflight, executed, passClock, listing,
          named, published, ancestors,
          wst, wobj, wtok, wcat,
          jobSt, jobObj,
          catSt, catRank, catSnap, catPred, retired,
          aeSt, aeObj,
          lost,
          everDeleted, everRetired, everCommitted, sweepDoomed, retriedObjs,
          markedOk, nonGcDelete, graceOk, peerMissing, reimported,
          revived, recoveredAfterGc, aeImportAfterGc, ancestorAfterGc,
          resighted, retryGone,
          bSt, bOrder, btok, bJob, bBodies, aeB, aeBFetched

storeVars == <<present, gcobj, gcref, ocert, clock, fence, puts>>
guardVars == <<nonce, inflight, executed, passClock, listing>>
metaVars == <<named, published, ancestors>>
writerVars == <<wst, wobj, wtok, wcat>>
jobVars == <<jobSt, jobObj>>
catVars == <<catSt, catRank, catSnap, catPred, retired>>
aeVars == <<aeSt, aeObj>>
ghostVars == <<lost, everDeleted, everRetired, everCommitted, sweepDoomed,
               retriedObjs, markedOk, nonGcDelete, graceOk, peerMissing,
               reimported, revived, recoveredAfterGc, aeImportAfterGc,
               ancestorAfterGc, resighted, retryGone>>
batchVars == <<bSt, bOrder, btok, bJob, bBodies, aeB, aeBFetched>>
vars == <<storeVars, guardVars, metaVars, writerVars, jobVars, catVars,
          aeVars, ghostVars, batchVars>>

St(s, t, n) == [st |-> s, t |-> t, n |-> n]
NoState == St("none", 0, 0)
Unput == St("unput", 0, 0)
Collected(o) == gcobj[o].st \in {"doomed", "deleting", "gone"}
LiveState(o) == gcobj[o].st \in {"none", "sighted"}
Usable(o) == present[o] /\ LiveState(o)

(* Referrer kinds whose transactions write a gcref entry. *)
RootKinds == {"marker", "move", "tomb", "cat", "job", "ae", "import"}
AddRef(refs, r) == IF r[1] \in RootKinds THEN refs \cup {r} ELSE refs

(* ---- Guards ---------------------------------------------------------- *)
(* s3-guard and put_live: a content PUT of a Doomed or Deleting key is
   refused. *)
PutOK(o) == gcobj[o].st \notin {"doomed", "deleting"}
(* Referencing transaction: Doomed, Deleting and Gone all abort. *)
DoomedRefOK == FALSE
GoneRefOK == FALSE
RefAllowed(o) ==
  CASE gcobj[o].st \in {"doomed", "deleting"} -> DoomedRefOK
    [] gcobj[o].st = "gone" -> GoneRefOK
    [] OTHER -> TRUE
RefState(o) == IF gcobj[o].st = "sighted" THEN NoState ELSE gcobj[o]
(* gc_revive: clear only the exact Gone read before the re-PUT. *)
ReviveOK(w, o) == gcobj[o] = wtok[w]
(* gc_revive by GET-verification: the object is present. *)
VerifyOK(o) == present[o]
(* A protective aepending reference never aborts; it clears Sighted only. *)
AeState(o) == IF gcobj[o].st = "sighted" THEN NoState ELSE gcobj[o]
(* T6 refuses a doomed, deleting or gone object. *)
CertOK(o) == gcobj[o].st \notin {"doomed", "deleting", "gone"}
(* T5 re-reads the snapshot certificate inside its transaction. *)
SnapCertOK(o) == ocert[o]
(* Sweep. *)
SightUnreferenced(o) == gcref[o] = {}
DoomUnreferenced(o) == gcref[o] = {}
GraceOK(o) == clock - gcobj[o].t >= Grace
ResightOld(o) == gcobj[o].t < passClock
ResightListed(o) == o \in listing
(* s3-guard DELETE: the GC access key (an identity selector; Garage checks
   the signature), a Doomed or Deleting key, a fresh nonce. *)
KeyOK(p) == p \in {"gc", "forged"}
DeleteStateOK(o) == gcobj[o].st \in {"doomed", "deleting"}
(* Fix: Gone only when no forwarded DELETE of the key can still execute. *)
GoneQuiescent(o) == \A r \in inflight : r[1] # o
(* T12 runs each member's T1 body, which refuses a collected object. *)
MemberRefOK(m) == RefAllowed(m)
(* T12 is all or nothing: every member must pass. *)
BatchAllOK(ok) == ok = Objects
(* T12/T13 reference every member: `batch/<id>` and the member body's own
   referrer. *)
BatchRefs(id) == {<<"batch", id>>, <<"marker", Perm>>}
(* Batch parts are staged under the event's aepending referrer. *)
AeBatchPendingRefs == {<<"ae", "batch">>}
(* Job release reads J2/J3. *)
ReleaseOK(w) == jobSt[w] = "done"
(* Dead-record retirement: uncommitted and token rank below the fence. *)
RetireUncommitted(c) == catSt[c] = "staged"
RetireDead(c) == catRank[c] < fence
(* Catalogue exchange refuses retired IDs. *)
ExportOK(c) == c \notin retired
ImportOK(c) == c \notin retired
(* The object endpoint answers Retired for a collected object. *)
ServeAnswer(o) == IF Collected(o) THEN "retired"
                  ELSE IF present[o] THEN "bytes" ELSE "missing"

Init ==
  /\ present = [o \in Objects |-> FALSE]
  /\ gcobj = [o \in Objects |-> NoState]
  /\ gcref = [o \in Objects |-> {}]
  /\ ocert = [o \in Objects |-> FALSE]
  /\ clock = 0
  /\ fence = 0
  /\ puts = 0
  /\ nonce = [o \in Objects |-> 0]
  /\ inflight = {}
  /\ executed = [o \in Objects |-> {}]
  /\ passClock = 0
  /\ listing = {}
  /\ named = {}
  /\ published = {}
  /\ ancestors = {}
  /\ wst = [w \in Writers |-> "idle"]
  /\ wobj = [w \in Writers |-> NoObj]
  /\ wtok = [w \in Writers |-> NoState]
  /\ wcat = [w \in Writers |-> NoCat]
  /\ jobSt = [w \in Writers |-> "none"]
  /\ jobObj = [w \in Writers |-> NoObj]
  /\ catSt = [c \in CatIds |-> "none"]
  /\ catRank = [c \in CatIds |-> 0]
  /\ catSnap = [c \in CatIds |-> NoObj]
  /\ catPred = [c \in CatIds |-> NoCat]
  /\ retired = {}
  /\ aeSt = "none"
  /\ aeObj = NoObj
  /\ lost = {}
  /\ everDeleted = {}
  /\ everRetired = {}
  /\ everCommitted = {}
  /\ sweepDoomed = {}
  /\ retriedObjs = {}
  /\ markedOk = TRUE
  /\ nonGcDelete = FALSE
  /\ graceOk = TRUE
  /\ peerMissing = FALSE
  /\ reimported = FALSE
  /\ revived = FALSE
  /\ recoveredAfterGc = FALSE
  /\ aeImportAfterGc = FALSE
  /\ ancestorAfterGc = FALSE
  /\ resighted = FALSE
  /\ retryGone = FALSE
  /\ bSt = "none"
  /\ bOrder = <<>>
  /\ btok = [o \in Objects |-> Unput]
  /\ bJob = [o \in Objects |-> "none"]
  /\ bBodies = {}
  /\ aeB = "none"
  /\ aeBFetched = {}

ResetWriter(w) ==
  /\ wst' = [wst EXCEPT ![w] = "idle"]
  /\ wobj' = [wobj EXCEPT ![w] = NoObj]
  /\ wtok' = [wtok EXCEPT ![w] = NoState]
  /\ wcat' = [wcat EXCEPT ![w] = NoCat]

(* ---- Writers --------------------------------------------------------- *)
(* Read gcobj, then PUT the payload through s3-guard. *)
Put(w, o) ==
  /\ wst[w] = "idle"
  /\ puts < MaxPuts
  /\ PutOK(o)
  /\ puts' = puts + 1
  /\ present' = [present EXCEPT ![o] = TRUE]
  /\ wst' = [wst EXCEPT ![w] = "put"]
  /\ wobj' = [wobj EXCEPT ![w] = o]
  /\ wtok' = [wtok EXCEPT ![w] = gcobj[o]]
  /\ UNCHANGED <<batchVars, gcobj, gcref, ocert, clock, fence, guardVars, metaVars, wcat,
                 jobVars, catVars, aeVars, ghostVars>>

(* gc_revive after the writer's re-PUT: the exact Gone it read before the
   PUT must still be there. The writer then retries its reference. *)
Revive(w) ==
  LET o == wobj[w] IN
  /\ wst[w] = "put"
  /\ wtok[w].st = "gone"
  /\ gcobj[o].st = "gone"
  /\ ReviveOK(w, o)
  /\ gcobj' = [gcobj EXCEPT ![o] = NoState]
  /\ wtok' = [wtok EXCEPT ![w] = NoState]
  /\ revived' = TRUE
  /\ UNCHANGED <<batchVars, present, gcref, ocert, clock, fence, puts, guardVars,
                 metaVars, wst, wobj, wcat, jobVars, catVars, aeVars, lost,
                 everDeleted, everRetired, everCommitted, sweepDoomed,
                 retriedObjs, markedOk, nonGcDelete, graceOk, peerMissing,
                 reimported, recoveredAfterGc, aeImportAfterGc,
                 ancestorAfterGc, resighted, retryGone>>

(* gc_revive by GET-verification (read Gone, GET, compare-and-clear). *)
VerifyRevive(o) ==
  /\ gcobj[o].st = "gone"
  /\ VerifyOK(o)
  /\ gcobj' = [gcobj EXCEPT ![o] = NoState]
  /\ revived' = TRUE
  /\ UNCHANGED <<batchVars, present, gcref, ocert, clock, fence, puts, guardVars,
                 metaVars, writerVars, jobVars, catVars, aeVars, lost,
                 everDeleted, everRetired, everCommitted, sweepDoomed,
                 retriedObjs, markedOk, nonGcDelete, graceOk, peerMissing,
                 reimported, recoveredAfterGc, aeImportAfterGc,
                 ancestorAfterGc, resighted, retryGone>>

(* T1 (marker, optionally a revision of a published parent), T11 move (a
   marker variant of published group g, staged marker object) and T8/T10
   tombstone (staged tombstone object; g joins tombstone lineage). *)
Reference(w, k, g) ==
  LET o == wobj[w] IN
  /\ wst[w] = "put"
  /\ IF k = "marker" THEN g \in published \cup {NoObj} ELSE g \in published
  /\ RefAllowed(o)
  /\ gcobj' = [gcobj EXCEPT ![o] = RefState(o)]
  /\ gcref' = [gcref EXCEPT ![o] = AddRef(@, <<k, Perm>>)]
  /\ named' = named \cup {o}
  /\ published' = IF k = "marker" THEN published \cup {o} ELSE published
  /\ ancestors' = IF g = NoObj THEN ancestors ELSE ancestors \cup {g}
  /\ ancestorAfterGc' = (ancestorAfterGc \/ (g # NoObj /\ everDeleted # {}))
  /\ ResetWriter(w)
  /\ UNCHANGED <<batchVars, present, ocert, clock, fence, puts, guardVars, jobVars,
                 catVars, aeVars, lost, everDeleted, everRetired,
                 everCommitted, sweepDoomed, retriedObjs, markedOk,
                 nonGcDelete, graceOk, peerMissing, reimported, revived,
                 recoveredAfterGc, aeImportAfterGc, resighted, retryGone>>

(* J1 issue: the job names its payload until the collector releases it. *)
IssueJob(w) ==
  LET o == wobj[w] IN
  /\ wst[w] = "put"
  /\ jobSt[w] = "none"
  /\ RefAllowed(o)
  /\ gcobj' = [gcobj EXCEPT ![o] = RefState(o)]
  /\ gcref' = [gcref EXCEPT ![o] = AddRef(@, <<"job", w>>)]
  /\ jobSt' = [jobSt EXCEPT ![w] = "pending"]
  /\ jobObj' = [jobObj EXCEPT ![w] = o]
  /\ ResetWriter(w)
  /\ UNCHANGED <<batchVars, present, ocert, clock, fence, puts, guardVars, metaVars,
                 catVars, aeVars, ghostVars>>

(* J2 or J3. *)
JobFinish(w) ==
  /\ jobSt[w] = "pending"
  /\ jobSt' = [jobSt EXCEPT ![w] = "done"]
  /\ UNCHANGED <<batchVars, storeVars, guardVars, metaVars, writerVars, jobObj, catVars,
                 aeVars, ghostVars>>

(* T5s: stage catalogue record c naming snapshot o, with the writer's token
   rank (the fence it holds) and an optional committed predecessor. *)
StageCat(w, c, p) ==
  LET o == wobj[w] IN
  /\ wst[w] = "put"
  /\ catSt[c] = "none"
  /\ p \in {NoCat} \cup {x \in CatIds : catSt[x] = "committed"}
  /\ RefAllowed(o)
  /\ gcobj' = [gcobj EXCEPT ![o] = RefState(o)]
  /\ gcref' = [gcref EXCEPT ![o] = AddRef(@, <<"cat", c>>)]
  /\ catSt' = [catSt EXCEPT ![c] = "staged"]
  /\ catRank' = [catRank EXCEPT ![c] = fence]
  /\ catSnap' = [catSnap EXCEPT ![c] = o]
  /\ catPred' = [catPred EXCEPT ![c] = p]
  /\ wst' = [wst EXCEPT ![w] = "staged"]
  /\ wcat' = [wcat EXCEPT ![w] = c]
  /\ UNCHANGED <<batchVars, present, ocert, clock, fence, puts, guardVars, metaVars,
                 wobj, wtok, jobVars, retired, aeVars, ghostVars>>

(* T5: token rank equals the fence, the record is staged, the snapshot's
   ocert is re-read, and the snapshot reference is re-checked. *)
CommitCat(w) ==
  LET c == wcat[w]
      o == catSnap[wcat[w]] IN
  /\ wst[w] = "staged"
  /\ catSt[c] = "staged"
  /\ catRank[c] = fence
  /\ SnapCertOK(o)
  /\ RefAllowed(o)
  /\ gcobj' = [gcobj EXCEPT ![o] = RefState(o)]
  /\ gcref' = [gcref EXCEPT ![o] = AddRef(@, <<"cat", c>>)]
  /\ catSt' = [catSt EXCEPT ![c] = "committed"]
  /\ everCommitted' = everCommitted \cup {c}
  /\ ResetWriter(w)
  /\ UNCHANGED <<batchVars, present, ocert, clock, fence, puts, guardVars, metaVars,
                 jobVars, catRank, catSnap, catPred, retired, aeVars, lost,
                 everDeleted, everRetired, sweepDoomed, retriedObjs,
                 markedOk, nonGcDelete, graceOk, peerMissing, reimported,
                 revived, recoveredAfterGc, aeImportAfterGc, ancestorAfterGc,
                 resighted, retryGone>>

(* An aborted or abandoned transaction leaves staging garbage (and possibly
   a staged record that a later fence rotation makes dead). *)
Abandon(w) ==
  /\ wst[w] # "idle"
  /\ ResetWriter(w)
  /\ UNCHANGED <<batchVars, storeVars, guardVars, metaVars, jobVars, catVars, aeVars,
                 ghostVars>>

(* T6: the store acknowledges a present object. *)
Certify(o) ==
  /\ present[o]
  /\ ~ocert[o]
  /\ CertOK(o)
  /\ ocert' = [ocert EXCEPT ![o] = TRUE]
  /\ UNCHANGED <<batchVars, present, gcobj, gcref, clock, fence, puts, guardVars,
                 metaVars, writerVars, jobVars, catVars, aeVars, ghostVars>>

(* A new writer token (for example after desktop loss) raises the fence. *)
RotateFence ==
  /\ fence < MaxFence
  /\ fence' = fence + 1
  /\ UNCHANGED <<batchVars, present, gcobj, gcref, ocert, clock, puts, guardVars,
                 metaVars, writerVars, jobVars, catVars, aeVars, ghostVars>>

DesktopLoss(w) ==
  /\ w \notin lost
  /\ lost' = lost \cup {w}
  /\ ResetWriter(w)
  /\ UNCHANGED <<batchVars, storeVars, guardVars, metaVars, jobVars, catVars, aeVars,
                 everDeleted, everRetired, everCommitted, sweepDoomed,
                 retriedObjs, markedOk, nonGcDelete, graceOk, peerMissing,
                 reimported, revived, recoveredAfterGc, aeImportAfterGc,
                 ancestorAfterGc, resighted, retryGone>>

(* Recovery reads cert/, catalog/, rcert/ and ocert/; RecoveryComplete states
   what it needs. The flag records a recovery after a collection with a
   committed record to adopt. *)
Recover(w) ==
  /\ w \in lost
  /\ lost' = lost \ {w}
  /\ recoveredAfterGc' = (recoveredAfterGc
                           \/ (everDeleted # {} /\ everCommitted # {}))
  /\ UNCHANGED <<batchVars, storeVars, guardVars, metaVars, writerVars, jobVars, catVars,
                 aeVars, everDeleted, everRetired, everCommitted, sweepDoomed,
                 retriedObjs, markedOk, nonGcDelete, graceOk, peerMissing,
                 reimported, revived, aeImportAfterGc, ancestorAfterGc,
                 resighted, retryGone>>

(* ---- Collector -------------------------------------------------------- *)
Tick ==
  /\ clock < MaxClock
  /\ clock' = clock + 1
  /\ UNCHANGED <<batchVars, present, gcobj, gcref, ocert, fence, puts, guardVars,
                 metaVars, writerVars, jobVars, catVars, aeVars, ghostVars>>

(* A sweep pass reads c0 = clock and then lists S3. Only the listing entries
   of collected objects are recorded: a Gone{t} with t < c0 was already
   collected when the pass started, and a Doomed or Deleting entry is the
   stale case the clock check exists for. Entries of objects in none or
   Sighted cannot affect the Gone-to-Sighted step. *)
PassStart ==
  /\ passClock' = clock
  /\ listing' = {o \in Objects : present[o] /\ Collected(o)}
  /\ UNCHANGED <<batchVars, storeVars, nonce, inflight, executed, metaVars, writerVars,
                 jobVars, catVars, aeVars, ghostVars>>

(* Per-object sweep transactions read the gcref range and gcobj. Sighting
   and doom use a fresh listing entry (abstracted as present). *)
SweepClear(o) ==
  /\ present[o]
  /\ gcref[o] # {}
  /\ gcobj[o].st = "sighted"
  /\ gcobj' = [gcobj EXCEPT ![o] = NoState]
  /\ UNCHANGED <<batchVars, present, gcref, ocert, clock, fence, puts, guardVars,
                 metaVars, writerVars, jobVars, catVars, aeVars, ghostVars>>

SweepSight(o) ==
  /\ present[o]
  /\ SightUnreferenced(o)
  /\ gcobj[o].st = "none"
  /\ gcobj' = [gcobj EXCEPT ![o] = St("sighted", clock, 0)]
  /\ UNCHANGED <<batchVars, present, gcref, ocert, clock, fence, puts, guardVars,
                 metaVars, writerVars, jobVars, catVars, aeVars, ghostVars>>

SweepDoom(o) ==
  /\ present[o]
  /\ DoomUnreferenced(o)
  /\ gcobj[o].st = "sighted"
  /\ GraceOK(o)
  /\ gcobj' = [gcobj EXCEPT ![o] = St("doomed", 0, 0)]
  /\ ocert' = [ocert EXCEPT ![o] = FALSE]
  /\ sweepDoomed' = sweepDoomed \cup {o}
  /\ graceOk' = (graceOk /\ clock - gcobj[o].t >= Grace)
  /\ UNCHANGED <<batchVars, present, gcref, clock, fence, puts, guardVars, metaVars,
                 writerVars, jobVars, catVars, aeVars, lost, everDeleted,
                 everRetired, everCommitted, retriedObjs, markedOk,
                 nonGcDelete, peerMissing, reimported, revived,
                 recoveredAfterGc, aeImportAfterGc, ancestorAfterGc,
                 resighted, retryGone>>

(* A revived but never-referenced object: Gone{t} with t < c0 that appears
   in this pass's listing was re-uploaded after its deletion. *)
SweepResight(o) ==
  /\ gcobj[o].st = "gone"
  /\ ResightOld(o)
  /\ ResightListed(o)
  /\ gcobj' = [gcobj EXCEPT ![o] = St("sighted", clock, 0)]
  /\ resighted' = TRUE
  /\ UNCHANGED <<batchVars, present, gcref, ocert, clock, fence, puts, guardVars,
                 metaVars, writerVars, jobVars, catVars, aeVars, lost,
                 everDeleted, everRetired, everCommitted, sweepDoomed,
                 retriedObjs, markedOk, nonGcDelete, graceOk, peerMissing,
                 reimported, revived, recoveredAfterGc, aeImportAfterGc,
                 ancestorAfterGc, retryGone>>

(* Collector job-release step: a job that reached J2 or J3. The step only
   drops the reference; a job that has not finished stays pending. *)
JobRelease(w) ==
  /\ jobSt[w] # "none"
  /\ ReleaseOK(w)
  /\ gcref' = [gcref EXCEPT ![jobObj[w]] = @ \ {<<"job", w>>}]
  /\ jobSt' = [jobSt EXCEPT ![w] = IF @ = "done" THEN "none" ELSE @]
  /\ jobObj' = [jobObj EXCEPT ![w] = IF jobSt[w] = "done" THEN NoObj ELSE @]
  /\ UNCHANGED <<batchVars, present, gcobj, ocert, clock, fence, puts, guardVars,
                 metaVars, writerVars, catVars, aeVars, ghostVars>>

(* Retire a dead catalogue record: clear the record and its references, and
   record the retired ID. *)
Retire(c) ==
  /\ RetireUncommitted(c)
  /\ RetireDead(c)
  /\ catSt' = [catSt EXCEPT ![c] = "retired"]
  /\ gcref' = [gcref EXCEPT ![catSnap[c]] = @ \ {<<"cat", c>>}]
  /\ retired' = retired \cup {c}
  /\ everRetired' = everRetired \cup {c}
  /\ UNCHANGED <<batchVars, present, gcobj, ocert, clock, fence, puts, guardVars,
                 metaVars, writerVars, jobVars, catRank, catSnap, catPred,
                 aeVars, lost, everDeleted, everCommitted, sweepDoomed,
                 retriedObjs, markedOk, nonGcDelete, graceOk, peerMissing,
                 reimported, revived, recoveredAfterGc, aeImportAfterGc,
                 ancestorAfterGc, resighted, retryGone>>

(* ---- s3-guard and Garage ------------------------------------------------ *)
(* Any principal may send a DELETE of any content key. The guard matches the
   access key, moves Doomed or Deleting to Deleting{fresh nonce} and
   forwards; Garage accepts only a valid signature, so a forged request is
   rejected and leaves nothing in flight. *)
DeleteRequest(p, o) ==
  /\ KeyOK(p)
  /\ DeleteStateOK(o)
  /\ nonce[o] < MaxNonce
  /\ nonce' = [nonce EXCEPT ![o] = @ + 1]
  /\ gcobj' = [gcobj EXCEPT ![o] = St("deleting", 0, nonce[o] + 1)]
  /\ inflight' = IF p = "forged" THEN inflight
                 ELSE inflight \cup {<<o, nonce[o] + 1, p>>}
  /\ retriedObjs' = IF gcobj[o].st = "deleting" THEN retriedObjs \cup {o}
                    ELSE retriedObjs
  /\ UNCHANGED <<batchVars, present, gcref, ocert, clock, fence, puts, executed,
                 passClock, listing, metaVars, writerVars, jobVars, catVars,
                 aeVars, lost, everDeleted, everRetired, everCommitted,
                 sweepDoomed, markedOk, nonGcDelete, graceOk, peerMissing,
                 reimported, revived, recoveredAfterGc, aeImportAfterGc,
                 ancestorAfterGc, resighted, retryGone>>

(* Garage executes a forwarded DELETE, possibly long after it was sent. *)
GarageExec(r) ==
  LET o == r[1] IN
  /\ r \in inflight
  /\ inflight' = inflight \ {r}
  /\ present' = [present EXCEPT ![o] = FALSE]
  /\ executed' = [executed EXCEPT ![o] = @ \cup {r[2]}]
  /\ markedOk' = (markedOk /\ o \in sweepDoomed)
  /\ nonGcDelete' = (nonGcDelete \/ r[3] # "gc")
  /\ UNCHANGED <<batchVars, gcobj, gcref, ocert, clock, fence, puts, nonce, passClock,
                 listing, metaVars, writerVars, jobVars, catVars, aeVars,
                 lost, everDeleted, everRetired, everCommitted, sweepDoomed,
                 retriedObjs, graceOk, peerMissing, reimported, revived,
                 recoveredAfterGc, aeImportAfterGc, ancestorAfterGc,
                 resighted, retryGone>>

(* The request's deadline passed without execution; it can no longer run. *)
RequestDies(r) ==
  /\ r \in inflight
  /\ inflight' = inflight \ {r}
  /\ UNCHANGED <<batchVars, storeVars, nonce, executed, passClock, listing, metaVars,
                 writerVars, jobVars, catVars, aeVars, ghostVars>>

(* Garage's success for the current nonce: Deleting{n} -> Gone{clock, n}. *)
DeleteDone(o) ==
  /\ gcobj[o].st = "deleting"
  /\ gcobj[o].n \in executed[o]
  /\ GoneQuiescent(o)
  /\ gcobj' = [gcobj EXCEPT ![o] = St("gone", clock, gcobj[o].n)]
  /\ everDeleted' = everDeleted \cup {o}
  /\ sweepDoomed' = sweepDoomed \ {o}
  /\ retriedObjs' = retriedObjs \ {o}
  /\ retryGone' = (retryGone \/ o \in retriedObjs)
  /\ UNCHANGED <<batchVars, present, gcref, ocert, clock, fence, puts, guardVars,
                 metaVars, writerVars, jobVars, catVars, aeVars, lost,
                 everRetired, everCommitted, markedOk, nonGcDelete, graceOk,
                 peerMissing, reimported, revived, recoveredAfterGc,
                 aeImportAfterGc, ancestorAfterGc, resighted>>

(* ---- Anti-entropy ------------------------------------------------------ *)
(* Source half: a peer fetches an object it knows of. *)
PeerFetch(o) ==
  /\ present[o] \/ o \in everDeleted
  /\ peerMissing' = (peerMissing \/ ServeAnswer(o) = "missing")
  /\ UNCHANGED <<batchVars, storeVars, guardVars, metaVars, writerVars, jobVars, catVars,
                 aeVars, lost, everDeleted, everRetired, everCommitted,
                 sweepDoomed, retriedObjs, markedOk, nonGcDelete, graceOk,
                 reimported, revived, recoveredAfterGc, aeImportAfterGc,
                 ancestorAfterGc, resighted, retryGone>>

ExportCat(c) ==
  /\ catSt[c] = "committed"
  /\ ExportOK(c)
  /\ reimported' = (reimported \/ c \in everRetired)
  /\ UNCHANGED <<batchVars, storeVars, guardVars, metaVars, writerVars, jobVars, catVars,
                 aeVars, lost, everDeleted, everRetired, everCommitted,
                 sweepDoomed, retriedObjs, markedOk, nonGcDelete, graceOk,
                 peerMissing, revived, recoveredAfterGc, aeImportAfterGc,
                 ancestorAfterGc, resighted, retryGone>>

(* A peer offers any catalogue ID it has seen, including stale ones. *)
ImportCat(c) ==
  /\ catSt[c] # "none"
  /\ ImportOK(c)
  /\ reimported' = (reimported \/ c \in everRetired)
  /\ UNCHANGED <<batchVars, storeVars, guardVars, metaVars, writerVars, jobVars, catVars,
                 aeVars, lost, everDeleted, everRetired, everCommitted,
                 sweepDoomed, retriedObjs, markedOk, nonGcDelete, graceOk,
                 peerMissing, revived, recoveredAfterGc, aeImportAfterGc,
                 ancestorAfterGc, resighted, retryGone>>

(* Receiver half: part persistence writes the protective aepending
   referrer; it never aborts. The batch instance exercises the batch event
   instead of a single one. *)
AeArrive(o) ==
  /\ ~BatchMode
  /\ aeSt = "none"
  /\ gcobj' = [gcobj EXCEPT ![o] = AeState(o)]
  /\ gcref' = [gcref EXCEPT ![o] = AddRef(@, <<"ae", AeEvent>>)]
  /\ aeSt' = "pending"
  /\ aeObj' = o
  /\ UNCHANGED <<batchVars, present, ocert, clock, fence, puts, guardVars, metaVars,
                 writerVars, jobVars, catVars, ghostVars>>

(* put_live: refused while Doomed or Deleting; after Gone, the PUT is
   followed by the exact-Gone revival. *)
AeFetch ==
  /\ aeSt = "pending"
  /\ PutOK(aeObj)
  /\ present' = [present EXCEPT ![aeObj] = TRUE]
  /\ gcobj' = [gcobj EXCEPT ![aeObj] = IF @.st = "gone" THEN NoState ELSE @]
  /\ revived' = (revived \/ gcobj[aeObj].st = "gone")
  /\ aeSt' = "fetched"
  /\ UNCHANGED <<batchVars, gcref, ocert, clock, fence, puts, guardVars, metaVars,
                 writerVars, jobVars, catVars, aeObj, lost, everDeleted,
                 everRetired, everCommitted, sweepDoomed, retriedObjs,
                 markedOk, nonGcDelete, graceOk, peerMissing, reimported,
                 recoveredAfterGc, aeImportAfterGc, ancestorAfterGc,
                 resighted, retryGone>>

(* Import: acknowledgement re-check, reference check, new permanent
   reference and release of the aepending referrer, in one transaction. *)
AeImport ==
  LET o == aeObj IN
  /\ aeSt = "fetched"
  /\ present[o]
  /\ RefAllowed(o)
  /\ gcobj' = [gcobj EXCEPT ![o] = RefState(o)]
  /\ gcref' = [gcref EXCEPT ![o] = AddRef(@ \ {<<"ae", AeEvent>>},
                                          <<"import", AeEvent>>)]
  /\ named' = named \cup {o}
  /\ aeSt' = "done"
  /\ aeImportAfterGc' = (aeImportAfterGc \/ o \in everDeleted)
  /\ UNCHANGED <<batchVars, present, ocert, clock, fence, puts, guardVars, published,
                 ancestors, writerVars, jobVars, catVars, aeObj, lost,
                 everDeleted, everRetired, everCommitted, sweepDoomed,
                 retriedObjs, markedOk, nonGcDelete, graceOk, peerMissing,
                 reimported, revived, recoveredAfterGc, ancestorAfterGc,
                 resighted, retryGone>>

(* The source answered Retired: archive the event and release it. *)
AeArchive ==
  /\ aeSt \in {"pending", "fetched"}
  /\ gcref' = [gcref EXCEPT ![aeObj] = @ \ {<<"ae", AeEvent>>}]
  /\ aeSt' = "done"
  /\ UNCHANGED <<batchVars, present, gcobj, ocert, clock, fence, puts, guardVars,
                 metaVars, writerVars, jobVars, catVars, aeObj, ghostVars>>

(* ---- Atomic multi-group batches ---------------------------------------- *)
(* The controller signs an intent naming the members in commit order. *)
BatchIntent(x, y) ==
  /\ BatchMode
  /\ bSt = "none"
  /\ x # y
  /\ bSt' = "intent"
  /\ bOrder' = <<x, y>>
  /\ UNCHANGED <<storeVars, guardVars, metaVars, writerVars, jobVars, catVars,
                 aeVars, ghostVars, btok, bJob, bBodies, aeB, aeBFetched>>

(* The coordinator PUTs a member's payload and staged marker, reading gcobj
   first; after a collection it re-PUTs. *)
BatchPut(m) ==
  /\ bSt = "intent"
  /\ btok[m] = Unput \/ (gcobj[m].st = "gone" /\ btok[m] # gcobj[m])
  /\ PutOK(m)
  /\ present' = [present EXCEPT ![m] = TRUE]
  /\ btok' = [btok EXCEPT ![m] = gcobj[m]]
  /\ UNCHANGED <<gcobj, gcref, ocert, clock, fence, puts, guardVars,
                 metaVars, writerVars, jobVars, catVars, aeVars, ghostVars,
                 bSt, bOrder, bJob, bBodies, aeB, aeBFetched>>

(* publish_batch revives the exact Gone it read before its re-PUT. *)
BatchRevive(m) ==
  /\ btok[m].st = "gone"
  /\ gcobj[m] = btok[m]
  /\ gcobj' = [gcobj EXCEPT ![m] = NoState]
  /\ btok' = [btok EXCEPT ![m] = NoState]
  /\ revived' = TRUE
  /\ UNCHANGED <<present, gcref, ocert, clock, fence, puts, guardVars,
                 metaVars, writerVars, jobVars, catVars, aeVars, lost,
                 everDeleted, everRetired, everCommitted, sweepDoomed,
                 retriedObjs, markedOk, nonGcDelete, graceOk, peerMissing,
                 reimported, recoveredAfterGc, aeImportAfterGc,
                 ancestorAfterGc, resighted, retryGone,
                 bSt, bOrder, bJob, bBodies, aeB, aeBFetched>>

(* J1 records the member's bound job envelope: a job referrer. *)
BatchJ1(m) ==
  /\ bSt = "intent"
  /\ bJob[m] = "none"
  /\ btok[m] # Unput
  /\ RefAllowed(m)
  /\ gcobj' = [gcobj EXCEPT ![m] = RefState(m)]
  /\ gcref' = [gcref EXCEPT ![m] = AddRef(@, <<"job", m>>)]
  /\ bJob' = [bJob EXCEPT ![m] = "pending"]
  /\ UNCHANGED <<present, ocert, clock, fence, puts, guardVars, metaVars,
                 writerVars, jobVars, catVars, aeVars, ghostVars,
                 bSt, bOrder, btok, bBodies, aeB, aeBFetched>>

BatchJ2(m) ==
  /\ bJob[m] = "pending"
  /\ bJob' = [bJob EXCEPT ![m] = "done"]
  /\ UNCHANGED <<storeVars, guardVars, metaVars, writerVars, jobVars,
                 catVars, aeVars, ghostVars, bSt, bOrder, btok, bBodies, aeB,
                 aeBFetched>>

(* The collector's job-release step, after J2. *)
BatchJobRelease(m) ==
  /\ bJob[m] = "done"
  /\ gcref' = [gcref EXCEPT ![m] = @ \ {<<"job", m>>}]
  /\ bJob' = [bJob EXCEPT ![m] = "released"]
  /\ UNCHANGED <<present, gcobj, ocert, clock, fence, puts, guardVars,
                 metaVars, writerVars, jobVars, catVars, aeVars, ghostVars,
                 bSt, bOrder, btok, bBodies, aeB, aeBFetched>>

(* T12: one FDB transaction runs every member's T1 body and writes
   `batch/<id>`; any refusal aborts the whole batch. *)
BatchCommit ==
  LET ok == {m \in Objects : MemberRefOK(m)} IN
  /\ bSt = "intent"
  /\ \A m \in Objects : bJob[m] \in {"done", "released"} /\ btok[m] # Unput
  /\ BatchAllOK(ok)
  /\ gcobj' = [o \in Objects |-> IF o \in ok THEN RefState(o) ELSE gcobj[o]]
  /\ gcref' = [o \in Objects |-> IF o \in ok THEN gcref[o] \cup BatchRefs("b")
                                 ELSE gcref[o]]
  /\ named' = named \cup ok
  /\ published' = published \cup ok
  /\ bBodies' = ok
  /\ bSt' = "committed"
  /\ UNCHANGED <<present, ocert, clock, fence, puts, guardVars, ancestors,
                 writerVars, jobVars, catVars, aeVars, ghostVars, bOrder,
                 btok, bJob, aeB, aeBFetched>>

(* Receiver: the batch event's parts are staged under its aepending
   referrer, which never aborts and clears Sighted only. *)
AeBatchArrive ==
  /\ BatchMode
  /\ aeB = "none"
  /\ gcobj' = [o \in Objects |-> AeState(o)]
  /\ gcref' = [o \in Objects |-> gcref[o] \cup AeBatchPendingRefs]
  /\ aeB' = "pending"
  /\ UNCHANGED <<present, ocert, clock, fence, puts, guardVars, metaVars,
                 writerVars, jobVars, catVars, aeVars, ghostVars, bSt,
                 bOrder, btok, bJob, bBodies, aeBFetched>>

(* put_live of one member. *)
AeBatchFetch(m) ==
  /\ aeB = "pending"
  /\ m \notin aeBFetched
  /\ PutOK(m)
  /\ present' = [present EXCEPT ![m] = TRUE]
  /\ gcobj' = [gcobj EXCEPT ![m] = IF @.st = "gone" THEN NoState ELSE @]
  /\ revived' = (revived \/ gcobj[m].st = "gone")
  /\ aeBFetched' = aeBFetched \cup {m}
  /\ UNCHANGED <<gcref, ocert, clock, fence, puts, guardVars, metaVars,
                 writerVars, jobVars, catVars, aeVars, lost, everDeleted,
                 everRetired, everCommitted, sweepDoomed, retriedObjs,
                 markedOk, nonGcDelete, graceOk, peerMissing, reimported,
                 recoveredAfterGc, aeImportAfterGc, ancestorAfterGc,
                 resighted, retryGone, bSt, bOrder, btok, bJob, bBodies, aeB>>

(* T13: every member's T9 body, the receiver's `batch/<id>` and the release
   of the aepending referrer, in one transaction. *)
AeBatchImport ==
  /\ aeB = "pending"
  /\ aeBFetched = Objects
  /\ \A m \in Objects : present[m] /\ RefAllowed(m)
  /\ gcobj' = [o \in Objects |-> RefState(o)]
  /\ gcref' = [o \in Objects |-> (gcref[o] \ {<<"ae", "batch">>})
                                 \cup BatchRefs("rb")]
  /\ named' = named \cup Objects
  /\ aeB' = "imported"
  /\ UNCHANGED <<present, ocert, clock, fence, puts, guardVars, published,
                 ancestors, writerVars, jobVars, catVars, aeVars, ghostVars,
                 bSt, bOrder, btok, bJob, bBodies, aeBFetched>>

AeBatchArchive ==
  /\ aeB = "pending"
  /\ gcref' = [o \in Objects |-> gcref[o] \ {<<"ae", "batch">>}]
  /\ aeB' = "archived"
  /\ aeBFetched' = {}
  /\ UNCHANGED <<present, gcobj, ocert, clock, fence, puts, guardVars,
                 metaVars, writerVars, jobVars, catVars, aeVars, ghostVars,
                 bSt, bOrder, btok, bJob, bBodies>>

Next ==
  \/ Tick \/ RotateFence \/ PassStart \/ AeFetch \/ AeImport \/ AeArchive
  \/ \E r \in inflight : GarageExec(r) \/ RequestDies(r)
  \/ \E w \in Writers :
       \/ Revive(w) \/ IssueJob(w) \/ JobFinish(w) \/ JobRelease(w)
       \/ CommitCat(w) \/ Abandon(w) \/ DesktopLoss(w) \/ Recover(w)
       \/ \E o \in Objects : Put(w, o)
       \/ \E k \in {"marker", "move", "tomb"}, g \in Objects \cup {NoObj} :
            Reference(w, k, g)
       \/ \E c \in CatIds, p \in CatIds \cup {NoCat} : StageCat(w, c, p)
  \/ \E o \in Objects :
       \/ Certify(o) \/ VerifyRevive(o) \/ SweepClear(o) \/ SweepSight(o)
       \/ SweepDoom(o) \/ SweepResight(o) \/ DeleteDone(o) \/ PeerFetch(o)
       \/ AeArrive(o)
       \/ \E p \in Principals : DeleteRequest(p, o)
  \/ \E c \in CatIds : Retire(c) \/ ExportCat(c) \/ ImportCat(c)
  \/ BatchCommit \/ AeBatchArrive \/ AeBatchImport \/ AeBatchArchive
  \/ \E x \in Objects, y \in Objects : BatchIntent(x, y)
  \/ \E m \in Objects :
       BatchPut(m) \/ BatchRevive(m) \/ BatchJ1(m) \/ BatchJ2(m)
       \/ BatchJobRelease(m) \/ AeBatchFetch(m)

Spec == Init /\ [][Next]_vars

Sym == Permutations(Objects) \cup Permutations(Writers) \cup Permutations(CatIds)

(* ---- Properties -------------------------------------------------------- *)
PendingJobObjs == {jobObj[w] : w \in {x \in Writers : jobSt[x] = "pending"}}
                  \cup {m \in Objects : bJob[m] = "pending"}
RecordObjs == {catSnap[c] : c \in {x \in CatIds : catSt[x] \in {"staged", "committed"}}}

(* Committed metadata (markers, variants, tombstones, imports, catalogue
   records), staged records, pending jobs and fetched anti-entropy objects
   name only present, uncollected objects. *)
NoDanglingRef ==
  /\ \A o \in named \cup PendingJobObjs \cup RecordObjs : Usable(o)
  /\ aeSt = "fetched" => Usable(aeObj)
  /\ aeB = "pending" => \A m \in aeBFetched : Usable(m)

(* Every executed DELETE was of an object the sweep had doomed and that is
   not yet Gone. *)
OnlyMarkedDeleted == markedOk
NonGcDeleteDenied == ~nonGcDelete
GraceKept == graceOk

(* Every committed record stays committed and adoptable: its snapshot is
   present and certified, and its predecessor is committed. Published
   markers are present. *)
RecoveryComplete ==
  /\ \A c \in everCommitted :
       /\ catSt[c] = "committed"
       /\ Usable(catSnap[c])
       /\ ocert[catSnap[c]]
       /\ (catPred[c] = NoCat \/ catSt[catPred[c]] = "committed")
  /\ \A o \in published : Usable(o)

(* The implementation's invariant: whenever gcobj is none or Sighted, an
   object that was ever acknowledged is present. (An object never deleted
   stays present once PUT, so only collected incarnations need checking.) *)
NoResurrection == \A o \in everDeleted : LiveState(o) => present[o]
NoRetiredReimport == ~reimported
RetiredDead == \A c \in everRetired : catRank[c] < fence /\ c \notin everCommitted
AncestorsLive == \A g \in ancestors : Usable(g)
OcertSound == \A o \in Objects : ocert[o] => Usable(o)
RetiredAnswered == ~peerMissing

(* No member object of a recorded batch is ever collected (here: it stays
   present and live), on the publisher and on the receiver. *)
BatchMembersLive ==
  /\ bSt = "committed" => \A m \in Objects : Usable(m)
  /\ aeB = "imported" => \A m \in Objects : Usable(m)
(* No partial batch: the member bodies T12 wrote are all members or none,
   and the record exists exactly when all were written. *)
NoPartialBatch ==
  /\ bBodies \in {{}, Objects}
  /\ (bSt = "committed") = (bBodies = Objects)

(* Reachability witnesses: each must be violated. *)
NeverCollected == everDeleted = {}
NeverRevived == ~revived
NeverRecoveredAfterGc == ~recoveredAfterGc
NeverAeImportAfterGc == ~aeImportAfterGc
NeverRetired == everRetired = {}
NeverAncestorAfterGc == ~ancestorAfterGc
NeverResighted == ~resighted
NeverRetryCollected == ~retryGone
NeverBatchCommitted == bSt # "committed"
NeverBatchCommittedAfterGc == ~(bSt = "committed" /\ everDeleted # {})
NeverBatchReceived == aeB # "imported"
=============================================================================
