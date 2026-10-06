------------------------------ MODULE Hardened ------------------------------
(* All hardened guards acting on ONE shared store.

   The separate models Receipts, Targets, Certificates and Fencing each check
   one guard against its own abstract store. Here one store (replicas with
   write and read quorums, plus a linearizable metadata store holding the
   target record and the catalogue fence) is shared by:

   1. receipt-gated staging (no worker evaluates validity);
   2. the atomic publish point (Targets/Certificates with AtomicCert = TRUE):
      after the preparer's marker is acknowledged by a live write quorum, one
      conditional write makes the group published, writes the publisher's
      own certificates to the live replicas (the writer logs the replies)
      and, for a target proof, is conditional on the target record's epoch
      and sets the recorded head;
   3. publication certificates written by any other worker only after it
      knows the group published, with that writer's reply log; discovery from
      certificates of a fully live read quorum; checkpoint commit on the
      committer's own reply quorum;
   4. the catalogue, aligned with Fencing: records name a parent; fenced
      first writes; repair from a named live source; unfenced acknowledgement
      from the writer's own replies; fenced commit certificates after that
      acknowledgement and only once the parent is committed; unfenced
      certificate repair; unfenced object certificates (manifest and payload)
      for the snapshot; fence rotation and re-acquisition; recovery readiness
      computed from certificates on fully live write quorums;
   5. completion on the worker's own committed catalogue record for the
      exact snapshot it committed.

   Observability. Every guard reads only: the acting worker's local state
   (pending, known groups, checkpoint, local copy of the target record,
   tokens it was issued, its reply logs); signed receipts it fetches from
   the store; the metadata item a conditional write is conditional on
   (epoch, fence), evaluated by the store atomically with the write; the
   target record when it reads it; or bytes and certificates on live
   replicas it contacts (LiveWrites # {} stands for replies from a live write
   quorum). `used` is id bookkeeping (ids are fresh), `Valid` is read only
   by the validator, and `done` is the single task's completion record.
   Variables under GHOST are read only by invariants and witnesses.

   The local copy `rec[w]` of the target record is taken by ReadRecord and may
   lag the store arbitrarily: preparation reads the copy, not the store.
   Publication is conditional on the store's epoch, so a proof prepared from
   a stale copy (old owner, old epoch) cannot publish. A successful publish
   tells the writer the value it wrote, which becomes its copy.

   Granularity. Catalogue record bytes are written and repaired one replica
   at a time. A commit certificate write goes to a chosen live write quorum
   in one step and is then repaired one replica at a time. Publication and
   object certificate writes go to every live replica in one step. Each
   certificate write happens once per writer and object. See HARDENED-TLA.md
   for this and the other abstractions. *)
EXTENDS FiniteSets, Naturals, TLC

CONSTANTS Replicas, Workers, Proofs, Bad, InitialOwner, InitialHolder,
          MaxEpoch, MaxFence,
          ByzProbe   \* enables RefuseBad, a step that changes only a ghost

None == "none"
NoTuple == <<>>                      \* "absent" for rec[w], done and parentOf[c]
Groups == Proofs \cup {Bad}
Valid == Proofs                      \* read only by the trusted validator
Quorums == {Q \in SUBSET Replicas : 2 * Cardinality(Q) > Cardinality(Replicas)}
Writes == Quorums
Reads == Quorums
Ranks == 1..MaxFence
Recs == Ranks \X Proofs              \* catalogue record <<token rank, snapshot>>
Tok(c) == c[1]
Snap(c) == c[2]

ASSUME \A W \in Writes, Q \in Reads : W \cap Q # {}

VARIABLES
  \* staging (worker-local unless noted)
  issued,      \* receipts the validator signed (store objects)
  used,        \* group ids already prepared (ids are fresh)
  pending,     \* staged, unpublished groups per worker
  revises,     \* revision set inside each proof (content)
  stamp,       \* epoch each proof was prepared under (content)
  \* metadata store (linearizable)
  published,   \* groups made published by the conditional publish write
  owner, epoch, recHead,   \* the target record
  fence,       \* catalogue fence register
  holder,      \* token rank -> worker it was issued to
  \* worker-local
  rec,         \* local copy of the target record: NoTuple or <<owner, epoch, head>>
  known,       \* groups the worker knows published (own publish or a scan)
  head,        \* the worker's committed checkpoint (its one proof) or None
  \* replicas and writers' persisted reply logs
  live,
  cert,        \* per-replica publication certificates
  certReply,   \* certReply[w][g]: replicas that acked w's certificate write for g
  catStored,   \* per-replica catalogue record bytes
  catReply,    \* catReply[c]: replicas that acked the writer's puts/repairs of c
  parentOf,    \* the parent a record names (content, fixed at its first put)
  rcert,       \* per-replica commit certificates
  rcReply,     \* rcReply[c]: replicas that acked the writer's commit certificate write
  ocert,       \* per-replica object certificates (manifest + payload) of a snapshot
  done,        \* the completed task's catalogue record, or NoTuple
  \* GHOST
  writtenAt,   \* fence at the first write of a record's bytes (0 = no copy)
  certFence,   \* fence at a record's commit certificate write (0 = none)
  lateAck,     \* records whose writer completed its reply quorum after rotation
  byzRejected, \* a staging write without a receipt was refused
  \* bound
  erasure      \* 0: no index erasure yet; 1: erased, all replicas live;
               \* 2: erased after a replica loss; 3: erased after a replica
               \* loss and after completion (at most one erasure)

stageVars == <<issued, used, pending, revises, stamp>>
metaVars == <<published, owner, epoch, recHead, fence, holder>>
localVars == <<rec, known, head>>
pubCertVars == <<cert, certReply>>
catVars == <<catStored, catReply, parentOf, rcert, rcReply, ocert, done>>
\* GHOST variables and the erasure bound.
auxVars == <<writtenAt, certFence, lateAck, byzRejected, erasure>>
vars == <<stageVars, metaVars, localVars, live, pubCertVars, catVars, auxVars>>

-----------------------------------------------------------------------------
(* Derived views. *)

TokensOf(w) == {k \in Ranks : holder[k] = w}
Current(w) == IF TokensOf(w) = {} THEN 0
              ELSE CHOOSE k \in TokensOf(w) : \A j \in TokensOf(w) : j <= k

QuorumIn(S) == \E W \in Writes : W \subseteq S
LiveWrites == {W \in Writes : W \subseteq live}

Heads(w) == {p \in known[w] \cap Proofs :
               ~\E q \in known[w] \cap Proofs : p \in revises[q]}
Closed(R) == \A q \in R : revises[q] \subseteq R

\* As Fencing: every member of some fully live write quorum holds it. A lone
\* surviving holder of a quorum that lost a member does not count until
\* certificate repair restores a full quorum.
CertDurable(X, o) == \E W \in LiveWrites : \A r \in W : o \in X[r]

ScanSees(Q, g) == \E r \in Q : g \in cert[r]
ScanFinds(g) == \A Q \in Reads : Q \subseteq live => ScanSees(Q, g)

\* A record and its ancestors (ranks strictly decrease along parents).
RECURSIVE Chain(_)
Chain(c) == {c} \cup (IF parentOf[c] = NoTuple THEN {} ELSE Chain(parentOf[c]))

\* Scheduling restriction: a worker does task work (discovery, certificate
\* writes, checkpoint commits) only while its own record copy names it the
\* target's owner. A stale copy keeps a zombie active. Not a safety guard.
Active(w) == rec[w] # NoTuple /\ rec[w][1] = w

\* Proof ids are fresh and interchangeable: the next id is chosen canonically.
Fresh == CHOOSE p \in Proofs \ used : TRUE

\* The publisher's own certificates, written by the publish write itself.
AtomicCerts(g) == [r \in Replicas |-> IF r \in live THEN cert[r] \cup {g} ELSE cert[r]]

-----------------------------------------------------------------------------
(* Guards. Each mutation in check-tla-hardened.sh rewrites one of these lines
   (or one line of an action). *)

\* The worker presents a validator-signed receipt for exactly g.
ReceiptOK(w, g) == g \in issued
OwnerOK(w) == rec[w][1] = w
EpochOK(p) == stamp[p] = epoch
HeadAfter(p) == p
LearnOwnWrite(w, g) == IF g \in Proofs THEN [rec EXCEPT ![w] = <<w, stamp[g], g>>] ELSE rec
ReadHead(w) == rec[w][3]
CertAfterPublish(w, g) == g \in known[w]
OwnQuorum(w, p) == QuorumIn(certReply[w][p])
AckedOK(c) == QuorumIn(catReply[c])
CommitFenceOK(c) == fence = Tok(c)
PutFenceOK(w) == fence = Current(w)
RepairSourceOK(c, src) == src \in live /\ c \in catStored[src]
CertRepairSourceOK(c, src) == src \in live /\ c \in rcert[src]
ParentsCommittedOK(c) == parentOf[c] = NoTuple \/ CertDurable(rcert, parentOf[c])
ReadyOne(Q, c) == (\E r \in Q : c \in catStored[r]) /\ CertDurable(rcert, c) /\ CertDurable(ocert, Snap(c))
Ready(Q, c) == \A d \in Chain(c) : ReadyOne(Q, d)
CatalogueCommitted(w, c) == QuorumIn(rcReply[c])

\* A record a writer may name as parent at its first put: a lower-rank record
\* it acknowledged itself, or one it reads as ready from a fully live read
\* quorum; no parent only when it reads no ready record.
Visible(d) == \E Q \in Reads : Q \subseteq live /\ Ready(Q, d)
ParentChoices(w) ==
  {d \in Recs : /\ Tok(d) < Current(w)
                /\ \/ Tok(d) \in TokensOf(w) /\ QuorumIn(catReply[d])
                   \/ Visible(d)}
  \cup (IF \E d \in Recs : Visible(d) THEN {} ELSE {NoTuple})

-----------------------------------------------------------------------------
Init ==
  /\ issued = {}
  /\ used = {}
  /\ pending = [w \in Workers |-> {}]
  /\ revises = [g \in Groups |-> {}]
  /\ stamp = [g \in Groups |-> 0]
  /\ published = {}
  /\ owner = InitialOwner
  /\ epoch = 0
  /\ recHead = None
  /\ fence = 1
  /\ holder = [k \in Ranks |-> IF k = 1 THEN InitialHolder ELSE None]
  /\ rec = [w \in Workers |-> NoTuple]
  /\ known = [w \in Workers |-> {}]
  /\ head = [w \in Workers |-> None]
  /\ live = Replicas
  /\ cert = [r \in Replicas |-> {}]
  /\ certReply = [w \in Workers |-> [g \in Groups |-> {}]]
  /\ catStored = [r \in Replicas |-> {}]
  /\ catReply = [c \in Recs |-> {}]
  /\ parentOf = [c \in Recs |-> NoTuple]
  /\ rcert = [r \in Replicas |-> {}]
  /\ rcReply = [c \in Recs |-> {}]
  /\ ocert = [r \in Replicas |-> {}]
  /\ done = NoTuple
  /\ writtenAt = [c \in Recs |-> 0]
  /\ certFence = [c \in Recs |-> 0]
  /\ lateAck = {}
  /\ byzRejected = FALSE
  /\ erasure = 0

-----------------------------------------------------------------------------
(* 1. Receipts and staging. *)

(* Trusted validator, the only place validity is evaluated. A receipt is a
   signed object in the store; any worker can fetch and present it. The
   validator signs the next fresh proof id (ids are interchangeable). *)
Issue(g) ==
  /\ g \in Valid
  /\ Proofs \ used # {} /\ g = Fresh
  /\ g \notin issued
  /\ issued' = issued \cup {g}
  /\ UNCHANGED <<used, pending, revises, stamp>>
  /\ UNCHANGED <<metaVars, localVars, live, pubCertVars, catVars, auxVars>>

(* Staging a target proof; no validity check. Receipt guard, plus the target
   guard on the local record copy: it names w owner, R revises the copy's
   head, w has no other pending proof. The proof is stamped with the copy's
   epoch. *)
PrepareProof(w, p, R) ==
  /\ p \notin used
  /\ p = Fresh
  /\ ReceiptOK(w, p)
  /\ rec[w] # NoTuple
  /\ OwnerOK(w)
  /\ ReadHead(w) = None \/ ReadHead(w) \in R
  /\ pending[w] \cap Proofs = {}
  /\ R \subseteq known[w] \cap Proofs
  /\ Closed(R)
  /\ used' = used \cup {p}
  /\ revises' = [revises EXCEPT ![p] = R]
  /\ stamp' = [stamp EXCEPT ![p] = rec[w][2]]
  /\ pending' = [pending EXCEPT ![w] = @ \cup {p}]
  /\ UNCHANGED issued
  /\ UNCHANGED <<metaVars, localVars, live, pubCertVars, catVars, auxVars>>

(* Staging the invalid non-target group Bad: the receipt guard is its only check. *)
PrepareBad(w) ==
  /\ Bad \notin used
  /\ ReceiptOK(w, Bad)
  /\ used' = used \cup {Bad}
  /\ pending' = [pending EXCEPT ![w] = @ \cup {Bad}]
  /\ UNCHANGED <<issued, revises, stamp>>
  /\ UNCHANGED <<metaVars, localVars, live, pubCertVars, catVars, auxVars>>

(* A Byzantine worker presents no receipt for Bad; the staging write is refused. *)
RefuseBad(w) ==
  /\ Bad \notin used
  /\ ~ReceiptOK(w, Bad)
  /\ ByzProbe
  /\ ~byzRejected
  /\ byzRejected' = TRUE
  /\ UNCHANGED <<stageVars, metaVars, localVars, live, pubCertVars, catVars>>
  /\ UNCHANGED <<writtenAt, certFence, lateAck, erasure>>

-----------------------------------------------------------------------------
(* 2. The atomic publish point. The preparer's marker writes are acked by a
   live write quorum (LiveWrites # {}; always obtainable here, since at most
   one replica is ever lost, so it is a precondition rather than a step).
   Then ONE conditional write: it makes g published, writes the publisher's
   certificates on the live replicas (the publisher logs the replies) and,
   for a target proof, is conditional on the record's epoch and sets the
   recorded head. *)
Publish(w, g) ==
  /\ g \in pending[w]
  /\ LiveWrites # {}
  /\ g \in Proofs => EpochOK(g)
  /\ published' = published \cup {g}
  /\ cert' = AtomicCerts(g)
  /\ certReply' = [certReply EXCEPT ![w][g] = live]
  /\ recHead' = IF g \in Proofs THEN HeadAfter(g) ELSE recHead
  /\ rec' = LearnOwnWrite(w, g)
  /\ known' = [known EXCEPT ![w] = @ \cup {g}]
  /\ pending' = [pending EXCEPT ![w] = @ \ {g}]
  /\ UNCHANGED <<issued, used, revises, stamp>>
  /\ UNCHANGED <<owner, epoch, fence, holder, head, live, catVars, auxVars>>

(* The conditional write fails (the epoch moved on); nothing is written. The
   writer drops the proof and its stale copy of the record. *)
PublishRefused(w, p) ==
  /\ p \in pending[w] \cap Proofs
  /\ LiveWrites # {}
  /\ ~EpochOK(p)
  /\ pending' = [pending EXCEPT ![w] = @ \ {p}]
  /\ rec' = [rec EXCEPT ![w] = NoTuple]
  /\ UNCHANGED <<issued, used, revises, stamp>>
  /\ UNCHANGED <<metaVars, known, head, live, pubCertVars, catVars>>
  /\ UNCHANGED auxVars

(* One atomic read of owner, epoch and head into the local copy.
   Scheduling restriction (ReadUseful): a worker keeps a copy only when the
   record names it owner; a copy naming another worker enables none of its
   actions while the owner check (OwnerOK) is in place. The owner-check
   mutation removes this restriction too. *)
ReadUseful(w) == owner = w
ReadRecord(w) ==
  /\ ReadUseful(w)
  /\ rec[w] # <<owner, epoch, recHead>>
  /\ rec' = [rec EXCEPT ![w] = <<owner, epoch, recHead>>]
  /\ UNCHANGED <<stageVars, metaVars, known, head, live, pubCertVars, catVars, auxVars>>

(* Controller reassignment to another worker, without the old owner's
   cooperation. (Re-granting to the same owner is not modelled.) *)
Reassign(w) ==
  /\ epoch < MaxEpoch
  /\ w # owner
  /\ owner' = w
  /\ epoch' = epoch + 1
  /\ UNCHANGED <<published, recHead, fence, holder>>
  /\ UNCHANGED <<stageVars, localVars, live, pubCertVars, catVars, auxVars>>

-----------------------------------------------------------------------------
(* 3. Publication certificates and discovery. *)

(* A worker other than the publisher writes its own certificates for g once
   it knows g published (e.g. after a scan), to every live replica, and logs
   the replies; it needs them for its own checkpoint commit. *)
CertPut(w, g) ==
  /\ Active(w)
  /\ CertAfterPublish(w, g)
  /\ certReply[w][g] = {}
  /\ cert' = [r \in Replicas |-> IF r \in live THEN cert[r] \cup {g} ELSE cert[r]]
  /\ certReply' = [certReply EXCEPT ![w][g] = live]
  /\ UNCHANGED <<stageVars, metaVars, localVars, live, catVars, auxVars>>

(* Discovery reads certificates of a fully live read quorum only. *)
ScanReceive(w, g, Q) ==
  /\ Active(w)
  /\ Q \subseteq live
  /\ g \notin known[w]
  /\ ScanSees(Q, g)
  /\ known' = [known EXCEPT ![w] = @ \cup {g}]
  /\ UNCHANGED <<stageVars, metaVars, rec, head, live, pubCertVars, catVars>>
  /\ UNCHANGED auxVars

(* Checkpoint commit of snapshot {p}: p is the unique known head of the
   target name, and the committer holds its own certificate reply quorum.
   The same step writes the snapshot's object certificates (manifest and
   payload; unfenced) to every live replica; the committer thereby knows
   them durable, so no separate reply log is kept for them. *)
CommitCheckpoint(w, p) ==
  /\ Active(w)
  /\ head[w] # p
  /\ p \in known[w]
  /\ Heads(w) = {p}
  /\ OwnQuorum(w, p)
  /\ head' = [head EXCEPT ![w] = p]
  /\ ocert' = [r \in Replicas |-> IF r \in live THEN ocert[r] \cup {p} ELSE ocert[r]]
  /\ UNCHANGED <<catStored, catReply, parentOf, rcert, rcReply, done>>
  /\ UNCHANGED <<stageVars, metaVars, rec, known, live, pubCertVars, auxVars>>

-----------------------------------------------------------------------------
(* 4. The catalogue. *)

(* Linearizable fence rotation: w, not the current holder, is issued the
   next rank. A writer re-acquires the fence after another writer held it. *)
RotateFence(w) ==
  /\ fence < MaxFence
  /\ holder[fence] # w
  /\ fence' = fence + 1
  /\ holder' = [holder EXCEPT ![fence + 1] = w]
  /\ UNCHANGED <<published, owner, epoch, recHead>>
  /\ UNCHANGED <<stageVars, localVars, live, pubCertVars, catVars, auxVars>>

(* First write of w's record for its checkpoint to one live replica,
   conditional on the fence (the store compares the token with it). The
   parent is chosen at the writer's first put and is part of the record. *)
CatPut(w, r, par) ==
  LET c == <<Current(w), head[w]>> IN
  /\ head[w] # None
  /\ Current(w) # 0
  \* Restriction: one record per token rank.
  /\ \A q \in Proofs : q # head[w] => catReply[<<Current(w), q>>] = {}
  /\ IF catReply[c] = {} THEN par \in ParentChoices(w) ELSE par = parentOf[c]
  /\ PutFenceOK(w)
  /\ r \in live
  /\ c \notin catStored[r]
  /\ catStored' = [catStored EXCEPT ![r] = @ \cup {c}]
  /\ catReply' = [catReply EXCEPT ![c] = @ \cup {r}]
  /\ parentOf' = [parentOf EXCEPT ![c] = par]
  /\ writtenAt' = IF writtenAt[c] = 0 THEN [writtenAt EXCEPT ![c] = fence] ELSE writtenAt
  /\ UNCHANGED <<rcert, rcReply, ocert, done>>
  /\ UNCHANGED <<stageVars, metaVars, localVars, live, pubCertVars>>
  /\ UNCHANGED <<certFence, lateAck, byzRejected, erasure>>

(* Repair by the record's writer: copy bytes read from live replica src.
   Unconditional. Completing the reply quorum after rotation is a late ack. *)
CatRepair(w, c, src, r) ==
  /\ Tok(c) \in TokensOf(w)
  /\ RepairSourceOK(c, src)
  /\ r \in live
  /\ c \notin catStored[r]
  /\ catStored' = [catStored EXCEPT ![r] = @ \cup {c}]
  /\ catReply' = [catReply EXCEPT ![c] = @ \cup {r}]
  /\ lateAck' = IF Tok(c) < fence /\ ~QuorumIn(catReply[c]) /\ QuorumIn(catReply'[c])
                THEN lateAck \cup {c} ELSE lateAck
  /\ UNCHANGED <<parentOf, rcert, rcReply, ocert, done>>
  /\ UNCHANGED <<stageVars, metaVars, localVars, live, pubCertVars>>
  /\ UNCHANGED <<writtenAt, certFence, byzRejected, erasure>>

(* Commit certificate write to a live write quorum W (one transaction,
   conditional on the fence), after the writer's own ack of the record bytes
   and once the parent is committed (the writer reads its certificates). *)
CommitCert(w, c, W) ==
  /\ Tok(c) \in TokensOf(w)
  /\ AckedOK(c)
  /\ CommitFenceOK(c)
  /\ ParentsCommittedOK(c)
  /\ rcReply[c] = {}
  /\ W \in LiveWrites
  /\ rcert' = [r \in Replicas |-> IF r \in W THEN rcert[r] \cup {c} ELSE rcert[r]]
  /\ rcReply' = [rcReply EXCEPT ![c] = W]
  /\ certFence' = [certFence EXCEPT ![c] = fence]
  /\ UNCHANGED <<catStored, catReply, parentOf, ocert, done>>
  /\ UNCHANGED <<stageVars, metaVars, localVars, live, pubCertVars>>
  /\ UNCHANGED <<writtenAt, lateAck, byzRejected, erasure>>

(* Certificate repair (any process): copy an existing commit certificate
   from live replica src to live replica r. Unconditional; it commits nothing
   new. Scheduling restriction: only after a replica loss (before one, a
   commit certificate already sits on a fully live write quorum). *)
CertRepair(c, src, r) ==
  /\ live # Replicas
  /\ CertRepairSourceOK(c, src)
  /\ r \in live
  /\ c \notin rcert[r]
  /\ rcert' = [rcert EXCEPT ![r] = @ \cup {c}]
  /\ UNCHANGED <<catStored, catReply, parentOf, rcReply, ocert, done>>
  /\ UNCHANGED <<stageVars, metaVars, localVars, live, pubCertVars, auxVars>>

-----------------------------------------------------------------------------
(* 5. Completion on w's own committed record for the snapshot it committed. *)
Complete(w, c) ==
  /\ done = NoTuple
  /\ Tok(c) \in TokensOf(w)
  /\ Snap(c) = head[w]
  /\ CatalogueCommitted(w, c)
  /\ done' = c
  /\ UNCHANGED <<catStored, catReply, parentOf, rcert, rcReply, ocert>>
  /\ UNCHANGED <<stageVars, metaVars, localVars, live, pubCertVars, auxVars>>

-----------------------------------------------------------------------------
(* Failures. *)

(* Permanent replica loss: bytes and certificates go; a read quorum survives. *)
LoseReplica(r) ==
  /\ r \in live
  /\ \E Q \in Reads : Q \subseteq live \ {r}
  /\ live' = live \ {r}
  /\ cert' = [cert EXCEPT ![r] = {}]
  /\ catStored' = [catStored EXCEPT ![r] = {}]
  /\ rcert' = [rcert EXCEPT ![r] = {}]
  /\ ocert' = [ocert EXCEPT ![r] = {}]
  \* GHOST: a record whose last copy is gone may be first-written again.
  /\ writtenAt' = [c \in Recs |->
                     IF \E x \in Replicas : c \in catStored'[x] THEN writtenAt[c] ELSE 0]
  /\ UNCHANGED <<certReply, catReply, parentOf, rcReply, done>>
  /\ UNCHANGED <<stageVars, metaVars, localVars>>
  /\ UNCHANGED <<certFence, lateAck, byzRejected, erasure>>

(* Index erasure: every worker crashes at once and loses pending work, known
   groups, checkpoint id and record copy. Issued tokens and persisted reply
   logs survive. Restrictions: workers crash together (as in Certificates'
   EraseIndexes), and at most once in a run; a worker that keeps running
   while the other is reassigned is the zombie case and needs no crash. *)
EraseIndexes ==
  /\ erasure = 0
  /\ pending' = [w \in Workers |-> {}]
  /\ known' = [w \in Workers |-> {}]
  /\ head' = [w \in Workers |-> None]
  /\ rec' = [w \in Workers |-> NoTuple]
  /\ erasure' = IF live = Replicas THEN 1 ELSE IF done = NoTuple THEN 2 ELSE 3
  /\ UNCHANGED <<issued, used, revises, stamp>>
  /\ UNCHANGED <<metaVars, live, pubCertVars, catVars>>
  /\ UNCHANGED <<writtenAt, certFence, lateAck, byzRejected>>

-----------------------------------------------------------------------------
Next ==
  \/ \E g \in Groups : Issue(g)
  \/ \E w \in Workers, g \in Groups : Publish(w, g)
  \/ \E w \in Workers, p \in Proofs, R \in SUBSET Proofs : PrepareProof(w, p, R)
  \/ \E w \in Workers : PrepareBad(w) \/ RefuseBad(w)
  \/ \E w \in Workers, p \in Proofs : PublishRefused(w, p) \/ CommitCheckpoint(w, p)
  \/ \E w \in Workers : ReadRecord(w) \/ Reassign(w) \/ RotateFence(w)
  \/ EraseIndexes
  \/ \E w \in Workers, g \in Groups : CertPut(w, g)
  \/ \E w \in Workers, g \in Groups, Q \in Reads : ScanReceive(w, g, Q)
  \/ \E w \in Workers, r \in Replicas, par \in Recs \cup {NoTuple} : CatPut(w, r, par)
  \/ \E w \in Workers, c \in Recs, src, r \in Replicas : CatRepair(w, c, src, r)
  \/ \E w \in Workers, c \in Recs, W \in Writes : CommitCert(w, c, W)
  \/ \E c \in Recs, src, r \in Replicas : CertRepair(c, src, r)
  \/ \E w \in Workers, c \in Recs : Complete(w, c)
  \/ \E r \in Replicas : LoseReplica(r)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Replicas are interchangeable; used only for invariant-only runs. *)
ReplicaSymmetry == Permutations(Replicas)

TypeOK ==
  /\ issued \subseteq Valid
  /\ used \subseteq Groups
  /\ pending \in [Workers -> SUBSET Groups]
  /\ revises \in [Groups -> SUBSET Proofs]
  /\ stamp \in [Groups -> 0..MaxEpoch]
  /\ published \subseteq used
  /\ owner \in Workers /\ epoch \in 0..MaxEpoch
  /\ recHead \in Proofs \cup {None}
  /\ fence \in Ranks
  /\ holder \in [Ranks -> Workers \cup {None}]
  /\ rec \in [Workers -> {NoTuple} \cup (Workers \X (0..MaxEpoch) \X (Proofs \cup {None}))]
  /\ known \in [Workers -> SUBSET Groups]
  /\ head \in [Workers -> Proofs \cup {None}]
  /\ live \subseteq Replicas
  /\ cert \in [Replicas -> SUBSET Groups]
  /\ certReply \in [Workers -> [Groups -> SUBSET Replicas]]
  /\ catStored \in [Replicas -> SUBSET Recs]
  /\ catReply \in [Recs -> SUBSET Replicas]
  /\ parentOf \in [Recs -> Recs \cup {NoTuple}]
  /\ \A c \in Recs : parentOf[c] # NoTuple => Tok(parentOf[c]) < Tok(c)
  /\ rcert \in [Replicas -> SUBSET Recs]
  /\ rcReply \in [Recs -> SUBSET Replicas]
  /\ ocert \in [Replicas -> SUBSET Proofs]
  /\ done \in Recs \cup {NoTuple}
  /\ writtenAt \in [Recs -> 0..MaxFence]
  /\ certFence \in [Recs -> 0..MaxFence]

-----------------------------------------------------------------------------
(* Safety invariants. *)

FailureEnvelope == \E Q \in Reads : Q \subseteq live

\* (1) Staged and published groups are valid and receipted.
StagedValid == \A w \in Workers : pending[w] \subseteq Valid
StagedReceipted == \A w \in Workers : pending[w] \subseteq issued
PublishedValid == published \subseteq Valid
PublishedReceipted == published \subseteq issued

\* (2) Published proofs of the target form a chain; each worker sees at most
\* one head; the recorded head tops the chain, across handovers.
TargetChain ==
  \A g, h \in published \cap Proofs : g = h \/ g \in revises[h] \/ h \in revises[g]
HeadUnique == \A w \in Workers : Cardinality(Heads(w)) <= 1
RecordTopsChain ==
  published \cap Proofs # {} =>
    /\ recHead \in published
    /\ \A g \in (published \cap Proofs) \ {recHead} : g \in revises[recHead]

\* (3) Certificates only for published groups; discovery yields only published
\* groups; every published group (in particular the recorded head a new owner
\* must revise) and every checkpoint's proof is found by every fully live scan.
CertSound == \A r \in Replicas : cert[r] \subseteq published
ReceivedPublished == \A w \in Workers : known[w] \subseteq published
PublishedDiscoverable == \A g \in published : ScanFinds(g)
CheckpointDiscoverable ==
  \A w \in Workers : head[w] # None => head[w] \in published /\ ScanFinds(head[w])

\* (4) Catalogue bytes and commit certificates only under the fence.
StaleNeverStored ==
  \A c \in Recs : (\E r \in Replicas : c \in catStored[r]) =>
     writtenAt[c] = Tok(c) /\ Tok(c) <= fence
CertFenced ==
  \A c \in Recs : (\E r \in Replicas : c \in rcert[r]) => certFence[c] = Tok(c)
\* Any record recovery would adopt from any fully live read quorum (with its
\* whole parent chain) was committed while its token was the fence and is not
\* a stale record acknowledged after rotation ...
ReadyCommitFenced ==
  \A Q \in Reads : Q \subseteq live =>
    \A c \in Recs : Ready(Q, c) => certFence[c] = Tok(c) /\ c \notin lateAck
\* ... and its surviving bytes were first written while its token was the fence.
ReadyFirstWriteFenced ==
  \A Q \in Reads : Q \subseteq live =>
    \A c \in Recs : Ready(Q, c) => writtenAt[c] = Tok(c)
\* Its snapshot's proof is published, found by every fully live certificate
\* scan, and on the target chain: the current recorded head or revised by it.
ReadySnapshotSound ==
  \A Q \in Reads : Q \subseteq live =>
    \A c \in Recs : Ready(Q, c) =>
       /\ Snap(c) \in published
       /\ ScanFinds(Snap(c))
       /\ recHead \in Proofs
       /\ (Snap(c) = recHead \/ Snap(c) \in revises[recHead])

\* (5) The completed record and every ancestor are recoverable from every
\* fully live read quorum: the bytes are found there, the commit certificate
\* (fenced) survives on a live replica so certificate repair can restore a
\* full live quorum of it, and the object certificate is durable. Nothing
\* here reads an index, so it holds after any erasure.
CompletedRecoverable ==
  done # NoTuple =>
    /\ Snap(done) \in published
    /\ ScanFinds(Snap(done))
    /\ \A d \in Chain(done) :
         /\ certFence[d] = Tok(d)
         /\ \E r \in live : d \in rcert[r]
         /\ CertDurable(ocert, Snap(d))
         /\ \A Q \in Reads : Q \subseteq live => \E r \in Q : d \in catStored[r]

-----------------------------------------------------------------------------
(* Coverage witnesses: each must be VIOLATED in the ordinary model. *)

\* Completion on a proof prepared by the new owner after a handover, which
\* revises a proof the old owner published under the earlier epoch.
NeverCompletedAfterHandover ==
  ~(done # NoTuple /\ \E q \in revises[Snap(done)] : stamp[q] < stamp[Snap(done)])

\* The task completed; then, after a replica loss, every index was erased; a
\* worker has rediscovered the completed proof by a certificate scan (known
\* is empty after erasure and the proof was published before), and the
\* record is ready on a fully live read quorum.
NeverRecoveredAfterLossAndErasure ==
  ~(/\ done # NoTuple
    /\ live # Replicas
    /\ erasure = 3
    /\ \E w \in Workers : Snap(done) \in known[w]
    /\ \E Q \in Reads : Q \subseteq live /\ Ready(Q, done))

\* After a replica loss the completed record is not ready on a fully live
\* quorum: one commit certificate holder was lost (CertRepair is needed).
NeverCompletedUnreadyAfterLoss ==
  ~(done # NoTuple /\ \E Q \in Reads : Q \subseteq live /\ ~Ready(Q, done))

\* (Action property.) A proof prepared from a stale record copy was refused.
NeverStalePrepareRefused == [][~\E w \in Workers, p \in Proofs : PublishRefused(w, p)]_vars

\* A stale catalogue writer acknowledged its old-token record after rotation.
NeverStaleCatalogueWriter == lateAck = {}

\* A staging write of Bad without a receipt was refused, in a run where an
\* unchecked worker's receipted proof was published.
NeverByzantineAttempt == ~(byzRejected /\ published \cap Proofs # {})

\* The completed record carries a token its writer re-acquired after another
\* writer held the fence, and names a parent.
NeverReacquiredCompleted ==
  ~(done # NoTuple /\ parentOf[done] # NoTuple
                   /\ \E k, j \in Ranks : /\ k < j /\ j < Tok(done)
                                          /\ holder[k] = holder[Tok(done)]
                                          /\ holder[j] # holder[Tok(done)])

\* The completed proof is not (or no longer) the recorded head.
NeverCompletedSuperseded == ~(done # NoTuple /\ recHead # Snap(done))
=============================================================================
