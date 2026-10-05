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
   everything its revised proofs revise), as Groups' valid_ancestry assumes.

   Discovery. Other workers learn a published proof only from a certificate
   quorum (`certified`, the abstraction of Certificates' CertQuorum), and a
   certificate may be written only by a worker that knows the proof (put needs
   `known n d`). With AtomicCert = FALSE (the original design) certification
   is a separate later step, so a publisher that crashes between publication
   and its certificate writes strands the proof: nobody knows it, nobody can
   certify it, nobody can receive it. If it is the recorded head, no owner can
   ever revise it and the target name is blocked forever (`HandoverProgress`
   fails). With AtomicCert = TRUE (the fix) the publication marker, the
   publisher's certificate quorum and the record's head update are one
   metadata-store transaction.

   Liveness. `stable` is the usual eventual-stability assumption (as Registry's
   Heal): before it, crashes and reassignments are arbitrary; after it, none.
   An owner whose pending proof was fenced learns the failed conditional write
   and drops it (Abandon). *)
EXTENDS FiniteSets, Naturals

CONSTANTS Workers, Proofs, InitialOwner, MaxEpoch, AtomicCert

VARIABLES published, pending, known, revises, used, head,
          owner, epoch, prepEpoch, pubEpoch, recHead, certified, stable

vars == <<published, pending, known, revises, used, head,
          owner, epoch, prepEpoch, pubEpoch, recHead, certified, stable>>

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
  /\ certified = {}
  /\ stable = FALSE

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
  /\ UNCHANGED <<published, known, head, owner, epoch, pubEpoch, recHead, certified, stable>>

(* Fenced publication marker write; the same conditional write sets the head.
   Under AtomicCert the same transaction writes the publisher's certificate
   quorum. *)
Publish(w, p) ==
  /\ p \in pending[w]
  /\ EpochOK(w, p)
  /\ published' = published \cup {p}
  /\ known' = [known EXCEPT ![w] = @ \cup {p}]
  /\ pending' = [pending EXCEPT ![w] = @ \ {p}]
  /\ pubEpoch' = [pubEpoch EXCEPT ![p] = epoch]
  /\ recHead' = HeadUpdate(p)
  /\ certified' = IF AtomicCert THEN certified \cup {p} ELSE certified
  /\ UNCHANGED <<revises, used, head, owner, epoch, prepEpoch, stable>>

(* A worker that knows p writes its certificate quorum (put needs known). *)
Certify(w, p) ==
  /\ p \in known[w]
  /\ p \notin certified
  /\ certified' = certified \cup {p}
  /\ UNCHANGED <<published, pending, known, revises, used, head, owner, epoch,
                 prepEpoch, pubEpoch, recHead, stable>>

(* The fenced publish of p failed; its preparer learns that and drops it. *)
Abandon(w, p) ==
  /\ p \in pending[w]
  /\ ~EpochOK(w, p)
  /\ pending' = [pending EXCEPT ![w] = @ \ {p}]
  /\ UNCHANGED <<published, known, revises, used, head, owner, epoch,
                 prepEpoch, pubEpoch, recHead, certified, stable>>

(* Controller reassignment, at any time, without the old owner's cooperation. *)
Reassign(w) ==
  /\ ~stable
  /\ epoch < MaxEpoch
  /\ owner' = w
  /\ epoch' = epoch + 1
  /\ UNCHANGED <<published, pending, known, revises, used, head, prepEpoch, pubEpoch, recHead,
                 certified, stable>>

(* Certificate scan: a proof is discoverable once it has a certificate quorum. *)
Receive(w, p) ==
  /\ p \in certified \ known[w]
  /\ known' = [known EXCEPT ![w] = @ \cup {p}]
  /\ UNCHANGED <<published, pending, revises, used, head, owner, epoch, prepEpoch, pubEpoch, recHead,
                 certified, stable>>

(* A commit containing p requires p to be the unique head of the name. *)
Commit(w, p) ==
  /\ p \in known[w]
  /\ Heads(w) = {p}
  /\ head' = [head EXCEPT ![w] = p]
  /\ UNCHANGED <<published, pending, known, revises, used, owner, epoch, prepEpoch, pubEpoch, recHead,
                 certified, stable>>

Crash(w) ==
  /\ ~stable
  /\ pending' = [pending EXCEPT ![w] = {}]
  /\ known' = [known EXCEPT ![w] = {}]
  /\ UNCHANGED <<published, revises, used, head, owner, epoch, prepEpoch, pubEpoch, recHead,
                 certified, stable>>

(* Eventual stability (a liveness assumption only): no more crashes or
   handovers. Safety does not depend on it. *)
Stabilize ==
  /\ ~stable
  /\ stable' = TRUE
  /\ UNCHANGED <<published, pending, known, revises, used, head, owner, epoch,
                 prepEpoch, pubEpoch, recHead, certified>>

Next ==
  \/ \E w \in Workers, p \in Proofs, R \in SUBSET Proofs : Prepare(w, p, R)
  \/ \E w \in Workers, p \in Proofs : Publish(w, p) \/ Receive(w, p) \/ Commit(w, p)
  \/ \E w \in Workers, p \in Proofs : Certify(w, p) \/ Abandon(w, p)
  \/ \E w \in Workers : Crash(w) \/ Reassign(w)
  \/ Stabilize

Spec == Init /\ [][Next]_vars

(* Fairness: stability eventually holds; the current owner keeps preparing;
   pending proofs are published or dropped; known proofs are certified and
   certified proofs are received. Crash and Reassign get no fairness. *)
FairSpec ==
  /\ Spec
  /\ WF_vars(Stabilize)
  /\ WF_vars(\E p \in Proofs, R \in SUBSET Proofs : Prepare(owner, p, R))
  /\ \A w \in Workers, p \in Proofs :
        /\ WF_vars(Publish(w, p)) /\ WF_vars(Abandon(w, p))
        /\ WF_vars(Certify(w, p)) /\ WF_vars(Receive(w, p))

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
  /\ certified \subseteq published
  /\ stable \in BOOLEAN

(* Under the fix every published proof is certified at publication. *)
PublishedCertified == AtomicCert => certified = published

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

(* Liveness: once the system is stable and a fresh proof id remains, the
   recorded head is eventually revised by a published proof. In particular a
   new owner after a handover can always supersede the head it inherited. *)
HandoverProgress ==
  \A h \in Proofs :
      (stable /\ recHead = h /\ used # Proofs) ~> (\E q \in published : h \in revises[q])
=============================================================================
