---------------------------- MODULE AtomicBatch ----------------------------
EXTENDS FiniteSets, Naturals, Sequences

(* Atomic multi-group publication (docs/atomic-pub-log.md; store.md T12/T13).

   One batch B renames published declarations across two workspaces. It
   publishes bar (g1, a proof of target name x, workspace a), deletes foo (t0,
   a position tombstone of g0, workspace a) and publishes use' (u1, workspace
   b), which revises use (u0) and depends on bar (inside the batch) and on g2
   (outside it). h1 is an ordinary competing proof of x. Members commit in the
   order of Members; each member passes the guards of a single publication
   (T1 or T8) in the state left by the members before it.

   Staged = FALSE: the batch is one store transaction (T12), all or nothing.
   Staged = TRUE: members are written as staged rows, invisible to readers, in
   any number of transactions. One intent record committed last makes them
   visible after every non-monotone guard is re-checked in that commit.
   Readers resolve staged rows through the intent record.

   Readers: a paginated discovery scan (recovery runs the same scan), an
   anti-entropy peer that stages an event's parts and imports them, a working
   copy cache filled one record at a time by `plr pull`, and checkpoint
   commits. Every reader view must hold all of the batch or none of it.

   Guards are named operators so the negative suite can remove each one.
   Violation tags are computed from the raw state at each commit, never from
   the guard operators. *)

CONSTANTS Staged, Readers

None == "none"
Coord == "c"
B == "B"
Members == <<"g1", "t0", "u1">>
N == Len(Members)
BatchItems == {Members[k] : k \in 1..N}
Singles == {"g0", "u0", "g2", "h1"}
Items == Singles \cup BatchItems
Tombs == {"t0"}
Proofs == {"h1", "g1"}
Writers == {"a", "b"}
Writer == [i \in Items |-> IF i \in {"g0", "h1", "g1", "t0"} THEN "a" ELSE "b"]
Deps == [i \in Items |-> IF i = "u0" THEN {"g0"} ELSE IF i = "u1" THEN {"g1", "g2"} ELSE {}]
TargetOf == [t \in Tombs |-> "g0"]
(* The old versions the batch replaces: use is revised and foo is deleted. *)
Replaced == {"u0", "g0"}
Bound == [i \in Items |-> IF i \in BatchItems THEN B ELSE None]
(* Key order of the paginated scan: batch members fall between other keys. *)
Order == <<"u1", "g0", "t0", "h1", "g1", "u0", "g2">>
MaxEpoch == 2
Heads == {None} \cup Proofs
Phases == {"idle", "prepared", "unknown", "done", "failed"}

ASSUME Staged \in BOOLEAN /\ Readers \subseteq {"scan", "peer", "cache", "ckpt"}

VARIABLES
  pub,                \* items visible through a committed T1/T8 or T12
  owner, epoch, head, \* target record of x
  prepEpoch, prepHead,\* the preparer's single read of the record, per proof
  prepared,           \* items with a prepared publication
  rcpt,               \* items holding a receipt for exactly that group and envelope
  certBy,             \* signer of each item's publisher certificate
  cphase,             \* the batch coordinator's knowledge of its commit
  staged, status, stageOK,  \* Staged mode: rows, intent record, stage-time check
  scanning, scanPos, scanSet, sview,
  peer, parts,
  cache, cfile,
  viol, staleRejected, ckptBad

vars == <<pub, owner, epoch, head, prepEpoch, prepHead, prepared, rcpt, certBy,
          cphase, staged, status, stageOK, scanning, scanPos, scanSet, sview,
          peer, parts, cache, cfile, viol, staleRejected, ckptBad>>

---------------------------------------------------------------------------
(* What is committed, and what a reader computes from the rows it reads. *)

Committed == IF Staged THEN status = "committed" ELSE BatchItems \subseteq pub
Published == IF Staged /\ status = "committed" THEN pub \cup staged ELSE pub
StatusOK == status = "committed"
ReaderVisible == pub \cup {m \in staged : StatusOK}

Partial(V) == V \cap BatchItems # {} /\ ~(BatchItems \subseteq V)

(* Supersession: a revision, a deletion, or a newer proof of the target. *)
Superseded(g, S) ==
  \/ g = "u0" /\ "u1" \in S
  \/ g = "g0" /\ "t0" \in S
  \/ g \in Proofs /\ \E p \in Proofs \cap S : prepHead[p] = g

---------------------------------------------------------------------------
(* Per-member guards: those of T1 (publication) and T8 (tombstone). *)

ReceiptOK(i) == IF i \in Tombs THEN TRUE ELSE i \in rcpt
CertOK(i) == certBy[i] = Writer[i]
OwnerOK(i) == IF i \in Proofs THEN owner = Writer[i] ELSE TRUE
EpochOK(i) == IF i \in Proofs THEN prepEpoch[i] = epoch ELSE TRUE
HeadOK(i, h) == IF i \in Proofs THEN prepHead[i] = h ELSE TRUE
DepsOK(i, S) == Deps[i] \subseteq S
TombOK(i, S) == IF i \in Tombs THEN TargetOf[i] \in S /\ TargetOf[i] \notin Proofs ELSE TRUE
FreshOK(i, S) == i \notin S
(* T1/T8 refuse a job envelope or tombstone bound to a batch; only T12 takes it. *)
UnboundOK(i) == Bound[i] = None

MemberOK(i, S, h) ==
  /\ i \in prepared
  /\ ReceiptOK(i) /\ CertOK(i) /\ OwnerOK(i) /\ EpochOK(i) /\ HeadOK(i, h)
  /\ DepsOK(i, S) /\ TombOK(i, S) /\ FreshOK(i, S)

NextHead(i, h) == IF i \in Proofs THEN i ELSE h
Prefix(n) == {Members[k] : k \in 1..n}

(* Members k..n pass in sequence from visible set S and head h. *)
RECURSIVE SeqOK(_, _, _, _)
SeqOK(k, n, S, h) ==
  IF k > n THEN TRUE
  ELSE MemberOK(Members[k], S, h) /\
       SeqOK(k + 1, n, S \cup {Members[k]}, NextHead(Members[k], h))

RECURSIVE SeqHead(_, _, _)
SeqHead(k, n, h) == IF k > n THEN h ELSE SeqHead(k + 1, n, NextHead(Members[k], h))

(* Violations of single-publication safety, from the raw state. *)
Tags(i, S, h, path) ==
  {t \in {"receipt", "cert", "stale", "fork", "deps", "tomb", "bound", "dup"} :
     \/ t = "receipt" /\ i \notin Tombs /\ i \notin rcpt
     \/ t = "cert" /\ certBy[i] # Writer[i]
     \/ t = "stale" /\ i \in Proofs /\ (owner # Writer[i] \/ prepEpoch[i] # epoch)
     \/ t = "fork" /\ i \in Proofs /\ prepHead[i] # h
     \/ t = "deps" /\ ~(Deps[i] \subseteq S)
     \/ t = "tomb" /\ i \in Tombs /\ TargetOf[i] \notin S
     \/ t = "bound" /\ path # Bound[i]
     \/ t = "dup" /\ i \in S}

RECURSIVE SeqTags(_, _, _, _)
SeqTags(k, n, S, h) ==
  IF k > n THEN {}
  ELSE Tags(Members[k], S, h, B) \cup
       SeqTags(k + 1, n, S \cup {Members[k]}, NextHead(Members[k], h))

(* The commit is all or nothing: it never stops at a failing member. *)
AllOrNothing == TRUE
(* Staged mode: every row is present before the intent commits. *)
AllStaged == staged = BatchItems
(* Staged mode: the commit re-checks the guards; stage-time checks go stale. *)
RecheckAtCommit == TRUE
(* Unknown outcome: the coordinator re-runs the idempotent body. *)
ResolveReads == TRUE

---------------------------------------------------------------------------
Init ==
  /\ pub = {}
  /\ owner = "a" /\ epoch = 0 /\ head = None
  /\ prepEpoch = [p \in Proofs |-> 0] /\ prepHead = [p \in Proofs |-> None]
  /\ prepared = {}
  /\ rcpt = {"g0", "u0", "g2"}
  /\ certBy = [i \in Items |-> Writer[i]]
  /\ cphase = "idle"
  /\ staged = {} /\ status = "pending" /\ stageOK = FALSE
  /\ scanning = FALSE /\ scanPos = 0 /\ scanSet = {} /\ sview = {}
  /\ peer = {} /\ parts = {}
  /\ cache = {} /\ cfile = FALSE
  /\ viol = {} /\ staleRejected = FALSE /\ ckptBad = {}

Readerless == <<scanning, scanPos, scanSet, sview, peer, parts, cache, cfile, ckptBad>>
Coordless == <<cphase, staged, status, stageOK, staleRejected>>

(* The validator answers a job for exactly one group and envelope. *)
Validate(i) ==
  /\ i \in {"g1", "u1", "h1"} \ rcpt
  /\ rcpt' = rcpt \cup {i}
  /\ UNCHANGED <<pub, owner, epoch, head, prepEpoch, prepHead, prepared, certBy,
                 Coordless, Readerless, viol>>

(* The controller reassigns x (T4); the head is kept. *)
Reassign(w) ==
  /\ epoch < MaxEpoch
  /\ owner' = w /\ epoch' = epoch + 1
  /\ UNCHANGED <<pub, head, prepEpoch, prepHead, prepared, rcpt, certBy,
                 Coordless, Readerless, viol>>

(* A workspace prepares its own single publication; a proof reads the record. *)
PrepareSingle(i) ==
  /\ i \in Singles \ (prepared \cup Published)
  /\ prepared' = prepared \cup {i}
  /\ prepEpoch' = IF i \in Proofs THEN [prepEpoch EXCEPT ![i] = epoch] ELSE prepEpoch
  /\ prepHead' = IF i \in Proofs THEN [prepHead EXCEPT ![i] = head] ELSE prepHead
  /\ UNCHANGED <<pub, owner, epoch, head, rcpt, certBy, Coordless, Readerless, viol>>

(* T1/T8 for one item: any prepared item, including a batch member whose
   artifacts the coordinator holds. *)
SinglePublish(i) ==
  /\ UnboundOK(i)
  /\ MemberOK(i, ReaderVisible, head)
  /\ pub' = pub \cup {i}
  /\ head' = NextHead(i, head)
  /\ viol' = viol \cup Tags(i, Published, head, None)
  /\ UNCHANGED <<owner, epoch, prepEpoch, prepHead, prepared, rcpt, certBy,
                 Coordless, Readerless>>

(* The coordinator prepares the batch: it reads the target record once and
   collects each member's certificate. It is not trusted: it may attach a
   certificate it signed itself (in the single-transaction configurations; the
   certificate guard is the same in staged mode). Published items keep their
   history. *)
PrepareBatch ==
  /\ cphase \in {"idle", "failed"}
  /\ cphase' = "prepared"
  /\ prepared' = prepared \cup BatchItems
  /\ prepEpoch' = IF "g1" \in Published THEN prepEpoch ELSE [prepEpoch EXCEPT !["g1"] = epoch]
  /\ prepHead' = IF "g1" \in Published THEN prepHead ELSE [prepHead EXCEPT !["g1"] = head]
  /\ \E forged \in (IF Staged THEN {None} ELSE {None} \cup BatchItems) :
       certBy' = [i \in Items |-> IF i \in BatchItems \ Published
                                   THEN (IF i = forged THEN Coord ELSE Writer[i])
                                   ELSE certBy[i]]
  /\ UNCHANGED <<pub, owner, epoch, head, rcpt, staged, status, stageOK,
                 staleRejected, Readerless, viol>>

(* T12: one transaction. n < N only when the all-or-nothing rule is removed. *)
CommitBatch(n) ==
  /\ ~Staged
  /\ cphase = "prepared"
  /\ ~Committed
  /\ n \in 1..N
  /\ IF AllOrNothing THEN n = N ELSE TRUE
  /\ SeqOK(1, n, ReaderVisible, head)
  /\ IF n < N THEN ~MemberOK(Members[n + 1], ReaderVisible \cup Prefix(n), SeqHead(1, n, head)) ELSE TRUE
  /\ pub' = pub \cup Prefix(n)
  /\ head' = SeqHead(1, n, head)
  /\ viol' = viol \cup SeqTags(1, n, Published, head)
  /\ cphase' \in {"done", "unknown"}
  /\ UNCHANGED <<owner, epoch, prepEpoch, prepHead, prepared, rcpt, certBy,
                 staged, status, stageOK, staleRejected, Readerless>>

(* A guard fails: nothing is written and the whole batch is rejected. *)
CommitReject ==
  /\ cphase = "prepared"
  /\ ~Committed
  /\ IF Staged THEN status = "pending" /\
                    ~(IF RecheckAtCommit THEN SeqOK(1, N, ReaderVisible, head) ELSE stageOK)
               ELSE ~SeqOK(1, N, ReaderVisible, head)
  /\ cphase' = "failed"
  /\ staleRejected' = (staleRejected \/ ~(OwnerOK("g1") /\ EpochOK("g1")))
  /\ UNCHANGED <<pub, owner, epoch, head, prepEpoch, prepHead, prepared, rcpt,
                 certBy, staged, status, stageOK, Readerless, viol>>

(* The retry of an already committed batch finds its record and writes nothing. *)
CommitDone ==
  /\ cphase = "prepared" /\ Committed
  /\ cphase' = "done"
  /\ UNCHANGED <<pub, owner, epoch, head, prepEpoch, prepHead, prepared, rcpt,
                 certBy, staged, status, stageOK, staleRejected, Readerless, viol>>

(* commit_unknown_result for an attempt that did not commit. *)
CommitLost ==
  /\ cphase = "prepared"
  /\ cphase' = "unknown"
  /\ UNCHANGED <<pub, owner, epoch, head, prepEpoch, prepHead, prepared, rcpt,
                 certBy, staged, status, stageOK, staleRejected, Readerless, viol>>

Resolve ==
  /\ cphase = "unknown"
  /\ cphase' = IF ResolveReads THEN "prepared" ELSE "failed"
  /\ UNCHANGED <<pub, owner, epoch, head, prepEpoch, prepHead, prepared, rcpt,
                 certBy, staged, status, stageOK, staleRejected, Readerless, viol>>

(* The coordinator crashes and forgets; the store keeps what committed. *)
Crash ==
  /\ cphase \in {"prepared", "unknown"}
  /\ cphase' = "idle"
  /\ UNCHANGED <<pub, owner, epoch, head, prepEpoch, prepHead, prepared, rcpt,
                 certBy, staged, status, stageOK, staleRejected, Readerless, viol>>

(* Staged mode: one invisible row per transaction, in any order. *)
StageRow(m) ==
  /\ Staged
  /\ cphase = "prepared" /\ status = "pending"
  /\ m \in BatchItems \ staged
  /\ staged' = staged \cup {m}
  /\ stageOK' = IF staged' = BatchItems THEN SeqOK(1, N, ReaderVisible, head) ELSE stageOK
  /\ UNCHANGED <<pub, owner, epoch, head, prepEpoch, prepHead, prepared, rcpt,
                 certBy, cphase, status, staleRejected, Readerless, viol>>

(* Staged mode: the intent record, committed last, after re-checking. *)
CommitIntent ==
  /\ Staged
  /\ cphase = "prepared" /\ status = "pending"
  /\ AllStaged
  /\ IF RecheckAtCommit THEN SeqOK(1, N, ReaderVisible, head) ELSE stageOK
  /\ status' = "committed"
  /\ head' = SeqHead(1, N, head)
  /\ viol' = viol \cup SeqTags(1, N, Published, head)
  /\ cphase' \in {"done", "unknown"}
  /\ UNCHANGED <<pub, owner, epoch, prepEpoch, prepHead, prepared, rcpt, certBy,
                 staged, stageOK, staleRejected, Readerless>>

(* Staged mode: an abandoned batch is aborted; its rows never become visible. *)
Abort ==
  /\ Staged
  /\ status = "pending" /\ cphase \in {"idle", "failed"}
  /\ status' = "aborted"
  /\ UNCHANGED <<pub, owner, epoch, head, prepEpoch, prepHead, prepared, rcpt,
                 certBy, cphase, staged, stageOK, staleRejected, Readerless, viol>>

---------------------------------------------------------------------------
(* Readers. *)

StoreOnly == <<pub, owner, epoch, head, prepEpoch, prepHead, prepared, rcpt,
               certBy, Coordless, viol>>

(* One scan, starting at any moment; it interleaves with every commit.
   Discovery closes a scan under batch membership: a member found on one page
   names its batch record, whose members are all committed by then. *)
CloseScan == TRUE
Close(S) ==
  IF CloseScan /\ S \cap BatchItems # {} THEN S \cup (BatchItems \cap ReaderVisible) ELSE S

ScanStart ==
  /\ "scan" \in Readers /\ ~scanning /\ scanPos = 0
  /\ scanning' = TRUE /\ scanPos' = 0 /\ scanSet' = {}
  /\ UNCHANGED <<StoreOnly, sview, peer, parts, cache, cfile, ckptBad>>

ScanPage ==
  /\ scanning /\ scanPos < Len(Order)
  /\ LET i == Order[scanPos + 1] IN
       scanSet' = IF i \in ReaderVisible THEN scanSet \cup {i} ELSE scanSet
  /\ scanPos' = scanPos + 1
  /\ UNCHANGED <<StoreOnly, scanning, sview, peer, parts, cache, cfile, ckptBad>>

ScanEnd ==
  /\ scanning /\ scanPos = Len(Order)
  /\ sview' = Close(scanSet) /\ scanning' = FALSE
  /\ UNCHANGED <<StoreOnly, scanPos, scanSet, peer, parts, cache, cfile, ckptBad>>

(* Anti-entropy: T9/T10 refuse batch-bound items; a batch travels as one event
   whose parts are staged, then imported in one transaction (T13). *)
PeerAloneOK(i) == Bound[i] = None
PartsOK == parts = BatchItems

RECURSIVE PeerOK(_, _)
PeerOK(k, S) ==
  IF k > N THEN TRUE
  ELSE LET m == Members[k] IN
       (IF m \in parts
        THEN Deps[m] \subseteq S /\ (IF m \in Tombs THEN TargetOf[m] \in S ELSE TRUE)
        ELSE TRUE) /\
       PeerOK(k + 1, IF m \in parts THEN S \cup {m} ELSE S)

AeItem(i) ==
  /\ "peer" \in Readers
  /\ i \in ReaderVisible \ peer
  /\ PeerAloneOK(i)
  /\ Deps[i] \subseteq peer
  /\ IF i \in Tombs THEN TargetOf[i] \in peer ELSE TRUE
  /\ peer' = peer \cup {i}
  /\ UNCHANGED <<StoreOnly, scanning, scanPos, scanSet, sview, parts, cache, cfile, ckptBad>>

AePart(m) ==
  /\ "peer" \in Readers
  /\ Committed
  /\ m \in BatchItems \ parts
  /\ parts' = parts \cup {m}
  /\ UNCHANGED <<StoreOnly, scanning, scanPos, scanSet, sview, peer, cache, cfile, ckptBad>>

AeImport ==
  /\ "peer" \in Readers
  /\ parts # {} /\ ~(parts \subseteq peer)
  /\ PartsOK
  /\ PeerOK(1, peer)
  /\ peer' = peer \cup parts
  /\ UNCHANGED <<StoreOnly, scanning, scanPos, scanSet, sview, parts, cache, cfile, ckptBad>>

(* Working copy: `plr pull` writes one record at a time and the batch file
   last; the copy's loader ignores batch records without their batch file. *)
FileOK == BatchItems \subseteq cache
FilterOK(i) == IF Bound[i] = None THEN TRUE ELSE cfile
CacheView == {i \in cache : FilterOK(i)}

Pull(i) ==
  /\ "cache" \in Readers
  /\ i \in ReaderVisible \ cache
  /\ cache' = cache \cup {i}
  /\ UNCHANGED <<StoreOnly, scanning, scanPos, scanSet, sview, peer, parts, cfile, ckptBad>>

PullFile ==
  /\ "cache" \in Readers
  /\ ~cfile /\ Committed /\ cache \cap BatchItems # {}
  /\ FileOK
  /\ cfile' = TRUE
  /\ UNCHANGED <<StoreOnly, scanning, scanPos, scanSet, sview, peer, parts, cache, ckptBad>>

(* Checkpoint commit (T5): current, dependency-closed members, read in one
   transaction. A straddling checkpoint mixes the batch with what it replaces. *)
CurrentOK(g) == ~Superseded(g, ReaderVisible)
Straddle(S) == S \cap BatchItems # {} /\ S \cap Replaced # {}

Checkpoint(S) ==
  /\ "ckpt" \in Readers
  /\ S # {}
  /\ \A g \in S : CurrentOK(g) /\ Deps[g] \subseteq S
  /\ ckptBad' = ckptBad \cup {x \in {"straddle", "batch"} :
                   \/ x = "straddle" /\ Straddle(S)
                   \/ x = "batch" /\ BatchItems \subseteq S \cup Tombs}
  /\ UNCHANGED <<StoreOnly, scanning, scanPos, scanSet, sview, peer, parts, cache, cfile>>

Next ==
  \/ \E i \in Items : Validate(i) \/ PrepareSingle(i) \/ SinglePublish(i)
  \/ \E w \in Writers : Reassign(w)
  \/ PrepareBatch \/ CommitReject \/ CommitDone \/ CommitLost \/ Resolve \/ Crash
  \/ \E n \in 1..N : CommitBatch(n)
  \/ \E m \in BatchItems : StageRow(m)
  \/ CommitIntent \/ Abort
  \/ ScanStart \/ ScanPage \/ ScanEnd
  \/ \E i \in Items : AeItem(i) \/ Pull(i)
  \/ \E m \in BatchItems : AePart(m)
  \/ AeImport \/ PullFile
  \/ \E S \in SUBSET (ReaderVisible \ Tombs) : Checkpoint(S)

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
TypeOK ==
  /\ pub \subseteq Items /\ staged \subseteq BatchItems
  /\ owner \in Writers /\ epoch \in 0..MaxEpoch /\ head \in Heads
  /\ cphase \in Phases /\ status \in {"pending", "committed", "aborted"}
  /\ scanSet \subseteq Items /\ sview \subseteq Items
  /\ peer \subseteq Items /\ parts \subseteq BatchItems /\ cache \subseteq Items

(* Every safety invariant of single-group publication still holds. *)
ReceiptSafety == "receipt" \notin viol
CertSafety == "cert" \notin viol
NoStalePublication == "stale" \notin viol
TargetChain == "fork" \notin viol
DepsClosed == "deps" \notin viol /\ \A i \in Published : Deps[i] \subseteq Published
TombstoneSafety == "tomb" \notin viol
BatchBound == "bound" \notin viol
PublishOnce == "dup" \notin viol
HeadIsLatest == head # None => head \in Published /\ ~Superseded(head, Published)

(* No reader, recovery or anti-entropy import sees a partial batch. *)
NoPartialStore == ~Partial(ReaderVisible)
NoPartialScan == ~Partial(sview)
NoPartialPeer == ~Partial(peer)
NoPartialCache == ~Partial(CacheView)
CheckpointNoStraddle == "straddle" \notin ckptBad
OutcomeTruthful == /\ cphase = "failed" => ~Committed
                   /\ cphase = "done" => Committed

(* Useful-work witnesses: each must be violated in the unmutated model. *)
NeverCommitted == ~Committed
NeverStaleRejected == ~staleRejected
NeverScanBatch == ~(BatchItems \subseteq sview)
NeverPeerBatch == ~(BatchItems \subseteq peer)
NeverCacheBatch == ~(BatchItems \subseteq CacheView)
NeverCheckpointBatch == "batch" \notin ckptBad
=============================================================================
