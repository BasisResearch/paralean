------------------------------ MODULE Targets ------------------------------
(* Alternative proofs of one required target name, with fenced ownership.
   Every proof declares the same pinned target name. Ownership of the name is
   state: a controller may reassign it at any moment, which bumps the owner
   epoch. The controller cannot observe a partitioned owner, so the old owner
   may keep running as a zombie with pending proofs.

   The store holds one record per target name: owner, epoch and the latest
   published proof (recHead). Preparation reads that record (one atomic read
   together with the preparation) and is admitted only at the current owner,
   only if the proof explicitly revises the recorded head, and only if the
   preparer has no other pending proof of the name. No scan of published
   proofs is read. The proof records the epoch it was prepared under.
   Publication is one fenced conditional write: it succeeds only if that epoch
   is still current, and it sets the recorded head to the new proof.

   Revision is transitive: a proof's revision set is closed (it revises
   everything its revised proofs revise), as Groups' valid_ancestry assumes. *)
EXTENDS FiniteSets, Naturals

CONSTANTS Workers, Proofs, InitialOwner, MaxEpoch

VARIABLES published, pending, known, revises, used, head,
          owner, epoch, prepEpoch, pubEpoch, recHead

vars == <<published, pending, known, revises, used, head,
          owner, epoch, prepEpoch, pubEpoch, recHead>>

None == "none"

OwnerOK(w) == w = owner
RevisesHead(R) == recHead = None \/ recHead \in R
HeadUpdate(p) == p
Closed(R) == \A q \in R : revises[q] \subseteq R
NoOtherPending(w) == pending[w] = {}
EpochOK(w, p) == prepEpoch[w][p] = epoch

TargetGuard(w, R) ==
  /\ OwnerOK(w)
  /\ RevisesHead(R)
  /\ NoOtherPending(w)

Heads(w) == {p \in known[w] : ~\E q \in known[w] : p \in revises[q]}

Init ==
  /\ published = {}
  /\ pending = [w \in Workers |-> {}]
  /\ known = [w \in Workers |-> {}]
  /\ revises = [p \in Proofs |-> {}]
  /\ used = {}
  /\ head = [w \in Workers |-> None]
  /\ owner = InitialOwner
  /\ epoch = 0
  /\ prepEpoch = [w \in Workers |-> [p \in Proofs |-> 0]]
  /\ pubEpoch = [p \in Proofs |-> 0]
  /\ recHead = None

(* A fresh proof whose explicit revisions are known, stamped with the epoch.
   The guard reads owner, epoch and recHead from the store record. *)
Prepare(w, p, R) ==
  /\ p \notin used
  /\ R \subseteq known[w]
  /\ Closed(R)
  /\ TargetGuard(w, R)
  /\ used' = used \cup {p}
  /\ revises' = [revises EXCEPT ![p] = R]
  /\ pending' = [pending EXCEPT ![w] = @ \cup {p}]
  /\ prepEpoch' = [prepEpoch EXCEPT ![w][p] = epoch]
  /\ UNCHANGED <<published, known, head, owner, epoch, pubEpoch, recHead>>

(* Fenced publication marker write; the same conditional write sets the head. *)
Publish(w, p) ==
  /\ p \in pending[w]
  /\ EpochOK(w, p)
  /\ published' = published \cup {p}
  /\ known' = [known EXCEPT ![w] = @ \cup {p}]
  /\ pending' = [pending EXCEPT ![w] = @ \ {p}]
  /\ pubEpoch' = [pubEpoch EXCEPT ![p] = epoch]
  /\ recHead' = HeadUpdate(p)
  /\ UNCHANGED <<revises, used, head, owner, epoch, prepEpoch>>

(* Controller reassignment, at any time, without the old owner's cooperation. *)
Reassign(w) ==
  /\ epoch < MaxEpoch
  /\ owner' = w
  /\ epoch' = epoch + 1
  /\ UNCHANGED <<published, pending, known, revises, used, head, prepEpoch, pubEpoch, recHead>>

(* Publication-marker scan: published proofs are discoverable by everyone. *)
Receive(w, p) ==
  /\ p \in published \ known[w]
  /\ known' = [known EXCEPT ![w] = @ \cup {p}]
  /\ UNCHANGED <<published, pending, revises, used, head, owner, epoch, prepEpoch, pubEpoch, recHead>>

(* A commit containing p requires p to be the unique head of the name. *)
Commit(w, p) ==
  /\ p \in known[w]
  /\ Heads(w) = {p}
  /\ head' = [head EXCEPT ![w] = p]
  /\ UNCHANGED <<published, pending, known, revises, used, owner, epoch, prepEpoch, pubEpoch, recHead>>

Crash(w) ==
  /\ pending' = [pending EXCEPT ![w] = {}]
  /\ known' = [known EXCEPT ![w] = {}]
  /\ UNCHANGED <<published, revises, used, head, owner, epoch, prepEpoch, pubEpoch, recHead>>

Next ==
  \/ \E w \in Workers, p \in Proofs, R \in SUBSET Proofs : Prepare(w, p, R)
  \/ \E w \in Workers, p \in Proofs : Publish(w, p) \/ Receive(w, p) \/ Commit(w, p)
  \/ \E w \in Workers : Crash(w) \/ Reassign(w)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ published \subseteq used /\ used \subseteq Proofs
  /\ pending \in [Workers -> SUBSET Proofs]
  /\ known \in [Workers -> SUBSET published]
  /\ revises \in [Proofs -> SUBSET Proofs]
  /\ head \in [Workers -> Proofs \cup {None}]
  /\ owner \in Workers
  /\ epoch \in 0..MaxEpoch
  /\ prepEpoch \in [Workers -> [Proofs -> 0..MaxEpoch]]
  /\ pubEpoch \in [Proofs -> 0..MaxEpoch]
  /\ recHead \in published \cup {None}

(* No two incomparable published proofs of the target name. *)
TargetChain ==
  \A g, h \in published : g = h \/ g \in revises[h] \/ h \in revises[g]

HeadUnique == \A w \in Workers : Cardinality(Heads(w)) <= 1

(* The recorded head tops the chain: every published proof is it or is revised by it. *)
RecordTopsChain ==
  published # {} => /\ recHead \in published
                    /\ \A g \in published \ {recHead} : g \in revises[recHead]

(* Witness (must be violated): two distinct proofs were published and a
   commit selected the latest, which revises every other published proof. *)
NeverAlternativeCommitted ==
  ~\E w \in Workers, g \in Proofs :
      /\ head[w] = g
      /\ Cardinality(published) >= 2
      /\ \A h \in published \ {g} : h \in revises[g]

(* Witness (must be violated): after a reassignment the old owner still holds
   an unpublished pending proof from an older epoch, and the new owner has
   published, under the current epoch, a proof that revises an earlier one. *)
NeverHandover ==
  ~\E z \in Workers, p, q \in Proofs :
      /\ epoch >= 1
      /\ z # owner
      /\ p \in pending[z] \ published
      /\ prepEpoch[z][p] < epoch
      /\ q \in published
      /\ q # p
      /\ pubEpoch[q] = epoch
      /\ revises[q] # {}
=============================================================================
