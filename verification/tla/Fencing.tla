------------------------------ MODULE Fencing ------------------------------
EXTENDS FiniteSets, Naturals, TLC

(* Fenced catalogue commits for one workspace. The fence is a linearizable
   register in the same store as the catalogue. A writer acquires the fence by
   rotating it; the rotation issues it the next token. A writer may re-acquire
   the fence later under a fresh token. Three replicas, majority quorums.

   Each record embeds the token it was written under and names its parents.
   - Put: a first write of record bytes, conditional on the fence (the store
     compares the presented token with the fence register atomically).
   - Repair: copies bytes the repairer read from a live replica that holds them.
     Unconditional. The receiving replica accepts only existing, signed bytes.
   - Ack: the writer's conclusion from its own replies that the bytes are on a
     live write quorum. Not a store write, not fenced.
   - CommitCert: the commit record. A per-replica certificate written by a
     conditional write on the fence register, after the writer's Ack.
   - Scan: recovery reads the certificates of every live replica. A record is
     ready when, for some write quorum, every live member holds its certificate,
     and its parents are ready. Scan reads no ghost state.
   writtenAt and certFence are ghost history (the fence at a record's first
   write, reset when every copy is gone, and at its commit certificate).
   lateAcked (records acknowledged while their token was below the fence) and
   lateRepair are ghost coverage state. *)

CONSTANTS Replicas, Records, Writers, Token, Parent

None == "none"
CaseToken == [c \in {"a", "s", "d"} |-> IF c = "d" THEN 3 ELSE 1]
CaseParent == [c \in {"a", "s", "d"} |-> IF c = "a" THEN {} ELSE {"a"}]
ReplicaSymmetry == Permutations(Replicas)
Tokens == 1..3
Quorums == {Q \in SUBSET Replicas : 2 * Cardinality(Q) > Cardinality(Replicas)}

VARIABLES fence, holds, live, stored, acked, cert, writtenAt, certFence,
          known, heads, scanned, reconstructed, selected, desktopLost,
          lateAcked, lateRepair
vars == <<fence, holds, live, stored, acked, cert, writtenAt, certFence,
          known, heads, scanned, reconstructed, selected, desktopLost,
          lateAcked, lateRepair>>

(* Conditional-write predicates evaluated by the store against its own fence. *)
FenceOK(w) == holds[w] = fence
CertFenceOK(w) == fence = holds[w]

(* What a writer observes from its own write replies. *)
OnLiveQuorum(c) == \E Q \in Quorums : Q \subseteq live /\ \A r \in Q : c \in stored[r]

(* What recovery reads: certificates on live replicas. *)
CertDurable(c) == \E W \in Quorums : \A r \in W \cap live : c \in cert[r]

Init ==
    /\ fence = 1
    /\ holds = [w \in Writers |-> IF w = "old" THEN 1 ELSE 0]
    /\ live = Replicas
    /\ stored = [r \in Replicas |-> {}]
    /\ acked = {}
    /\ cert = [r \in Replicas |-> {}]
    /\ writtenAt = [c \in Records |-> 0]
    /\ certFence = [c \in Records |-> 0]
    /\ known = {}
    /\ heads = {}
    /\ scanned = FALSE
    /\ reconstructed = FALSE
    /\ selected = None
    /\ desktopLost = FALSE
    /\ lateAcked = {}
    /\ lateRepair = FALSE

Ghost == <<writtenAt, certFence>>

(* Fenced first write of the writer's own record. *)
Put(w, c, r) ==
    /\ Token[c] = holds[w]
    /\ FenceOK(w)
    /\ r \in live
    /\ c \notin stored[r]
    /\ Parent[c] \subseteq acked
    /\ stored' = [stored EXCEPT ![r] = @ \cup {c}]
    /\ writtenAt' = IF writtenAt[c] = 0 THEN [writtenAt EXCEPT ![c] = fence] ELSE writtenAt
    /\ UNCHANGED <<desktopLost, fence, holds, live, acked, cert, certFence,
                   known, heads, scanned, reconstructed, selected, lateAcked, lateRepair>>

(* Repair: copy bytes read from live replica src. Unconditional; any process. *)
Repair(c, src, r) ==
    /\ src \in live /\ c \in stored[src]   \* repair copies existing bytes
    /\ r \in live
    /\ c \notin stored[r]
    /\ stored' = [stored EXCEPT ![r] = @ \cup {c}]
    /\ writtenAt' = IF writtenAt[c] = 0 THEN [writtenAt EXCEPT ![c] = fence] ELSE writtenAt
    /\ lateRepair' = (lateRepair \/ Token[c] < fence)
    /\ UNCHANGED <<desktopLost, fence, holds, live, acked, cert, certFence,
                   known, heads, scanned, reconstructed, selected, lateAcked>>

(* The writer's conclusion that its record is on a live write quorum. Not fenced. *)
Ack(w, c) ==
    /\ Token[c] = holds[w]
    /\ c \notin acked
    /\ OnLiveQuorum(c)
    /\ acked' = acked \cup {c}
    /\ lateAcked' = IF Token[c] < fence THEN lateAcked \cup {c} ELSE lateAcked
    /\ UNCHANGED <<desktopLost, fence, holds, live, stored, cert, writtenAt, certFence,
                   known, heads, scanned, reconstructed, selected, lateRepair>>

(* The commit record: a certificate on replica r, conditional on the fence. *)
CommitCert(w, c, r) ==
    /\ Token[c] = holds[w]
    /\ CertFenceOK(w)
    /\ c \in acked
    /\ r \in live
    /\ c \notin cert[r]
    /\ cert' = [cert EXCEPT ![r] = @ \cup {c}]
    /\ certFence' = IF certFence[c] = 0 THEN [certFence EXCEPT ![c] = fence] ELSE certFence
    /\ UNCHANGED <<desktopLost, fence, holds, live, stored, acked, writtenAt,
                   known, heads, scanned, reconstructed, selected, lateAcked, lateRepair>>

(* Linearizable lease rotation: writer w acquires the next token. *)
RotateFence(w) ==
    /\ fence < 3
    /\ fence' = fence + 1
    /\ holds' = [holds EXCEPT ![w] = fence + 1]
    /\ UNCHANGED <<desktopLost, live, stored, acked, cert, writtenAt, certFence,
                   known, heads, scanned, reconstructed, selected, lateAcked, lateRepair>>

LoseReplica(r) ==
    /\ r \in live
    /\ \E Q \in Quorums : Q \subseteq live \ {r}
    /\ live' = live \ {r}
    /\ stored' = [stored EXCEPT ![r] = {}]
    /\ cert' = [cert EXCEPT ![r] = {}]
    \* Ghost: a record whose last copy is gone may be first-written again.
    /\ writtenAt' = [c \in Records |->
                       IF \E x \in Replicas : c \in stored'[x] THEN writtenAt[c] ELSE 0]
    /\ UNCHANGED <<desktopLost, fence, holds, acked, certFence,
                   known, heads, scanned, reconstructed, selected, lateAcked, lateRepair>>

LoseDesktop ==
    /\ known' = {}
    /\ heads' = {}
    /\ scanned' = FALSE
    /\ reconstructed' = FALSE
    /\ selected' = None
    /\ desktopLost' = TRUE
    /\ UNCHANGED <<fence, holds, live, stored, acked, cert, writtenAt, certFence,
                   lateAcked, lateRepair>>

(* Recovery reads every live replica's certificates and the record bytes on a
   live read quorum Q. *)
Scan(Q) ==
    /\ Q \in Quorums
    /\ Q \subseteq live
    /\ LET found == UNION {stored[r] : r \in Q}
           ready == {c \in found : CertDurable(c)}
       IN known' = {c \in ready : Parent[c] \subseteq ready}
    /\ heads' = {}
    /\ scanned' = TRUE
    /\ reconstructed' = FALSE
    /\ selected' = None
    /\ UNCHANGED <<desktopLost, fence, holds, live, stored, acked, cert, writtenAt, certFence,
                   lateAcked, lateRepair>>

Reconstruct ==
    /\ scanned
    /\ heads' = {c \in known : ~\E d \in known : c \in Parent[d]}
    /\ reconstructed' = TRUE
    /\ UNCHANGED <<desktopLost, fence, holds, live, stored, acked, cert, writtenAt, certFence,
                   known, scanned, selected, lateAcked, lateRepair>>

Automatic(c) ==
    /\ reconstructed
    /\ heads = {c}
    /\ selected' = c
    /\ UNCHANGED <<desktopLost, fence, holds, live, stored, acked, cert, writtenAt, certFence,
                   known, heads, scanned, reconstructed, lateAcked, lateRepair>>

Next ==
    \/ \E w \in Writers, c \in Records, r \in Replicas : Put(w, c, r)
    \/ \E c \in Records, src \in Replicas, r \in Replicas : Repair(c, src, r)
    \/ \E w \in Writers, c \in Records : Ack(w, c)
    \/ \E w \in Writers, c \in Records, r \in Replicas : CommitCert(w, c, r)
    \/ \E w \in Writers : RotateFence(w)
    \/ \E r \in Replicas : LoseReplica(r)
    \/ LoseDesktop
    \/ \E Q \in SUBSET Replicas : Scan(Q)
    \/ Reconstruct
    \/ \E c \in Records : Automatic(c)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ fence \in Tokens
    /\ holds \in [Writers -> 0..3]
    /\ live \subseteq Replicas
    /\ stored \in [Replicas -> SUBSET Records]
    /\ cert \in [Replicas -> SUBSET Records]
    /\ acked \subseteq Records
    /\ writtenAt \in [Records -> 0..3]
    /\ certFence \in [Records -> 0..3]
    /\ known \subseteq Records
    /\ heads \subseteq Records
    /\ selected \in Records \cup {None}
    /\ lateAcked \subseteq Records
    /\ lateRepair \in BOOLEAN

(* Every record with bytes on a replica was first written (since its last
   disappearance) while its token was the fence. *)
StaleNeverStored ==
    \A c \in Records : (\E r \in Replicas : c \in stored[r]) =>
        writtenAt[c] = Token[c] /\ Token[c] <= fence

(* Every commit certificate was written while the record's token was the fence. *)
CertFenced ==
    \A c \in Records : (\E r \in Replicas : c \in cert[r]) => certFence[c] = Token[c]

(* Recovery adopts only records committed under the fence. *)
KnownFenced == \A c \in known : certFence[c] = Token[c] /\ Token[c] <= fence

(* A record acknowledged by its writer after the fence passed its token (a
   zombie) is never adopted by recovery. *)
NoLateAckedKnown == known \cap lateAcked = {}

(* The selected record was committed while its writer held the fence. *)
SelectedFenced ==
    selected # None => certFence[selected] = Token[selected] /\ Token[selected] <= fence

(* Completeness: every scan of a fully live read quorum finds the bytes of
   every durably certified record. *)
ScanFindsCertified ==
    \A Q \in Quorums : Q \subseteq live =>
        \A c \in Records : CertDurable(c) => \E r \in Q : c \in stored[r]

(* Coverage: expect a violation, i.e. recovery after rotation, replica loss and
   desktop loss auto-selects the legitimately fenced old-token record. *)
NeverRecoveredAfterRotation ==
    ~(fence >= 2 /\ desktopLost /\ live # Replicas /\ selected = "a")

(* Coverage: a writer re-acquires the fence under a fresh token and its new
   record is recovered. *)
NeverReacquiredRecovered == ~(selected = "d" /\ holds["old"] = 3)

(* Coverage: expect violations. An old-token record put before rotation is
   acknowledged after rotation; an old-token record is repaired after rotation. *)
NeverLateAck == lateAcked = {}
NeverLateRepair == ~lateRepair
=============================================================================
