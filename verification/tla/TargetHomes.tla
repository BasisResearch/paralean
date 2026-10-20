----------------------------- MODULE TargetHomes -----------------------------
(* Distributed refinement of TargetNames, for one target name.
   Home is immutable configuration shared before any participating store writes.
   Each deployment has a physically independent owner/epoch/head register.
   Only Home may prepare, publish or reassign this target. Other deployments
   receive certified proofs; receive does not change an ownership register.

   Erasing the non-home registers and receive copies yields TargetNames'
   single owner/epoch/head state. Publication checks owner, prepared epoch and
   recorded head atomically and writes its publication certificate atomically.
   No timeout or foreign certificate creates ownership.

   For several names, take the product of this model. All targets in one
   publication must have the same home, otherwise reject: this protocol has
   no cross-deployment transaction. Home migration is deliberately absent.
   Removing AtHome permits two independent stores to publish incomparable
   proofs despite both obeying their local owner/epoch/head checks. *)
EXTENDS Naturals, FiniteSets

CONSTANTS Deployments, Workers, Proofs, Home, InitialOwner, MaxEpoch
ASSUME /\ Home \in Deployments
       /\ InitialOwner \in Workers

VARIABLES owner, epoch, recHead, pending, prepEpoch, revises,
          used, published, origin, known

vars == <<owner, epoch, recHead, pending, prepEpoch, revises,
          used, published, origin, known>>
None == "none"
AtHome(d) == d = Home
Heads(d) == {p \in known[d] : ~\E q \in known[d] : p \in revises[q]}
Closed(R) == \A p \in R : revises[p] \subseteq R

Init ==
  /\ owner = [d \in Deployments |-> InitialOwner]
  /\ epoch = [d \in Deployments |-> 0]
  /\ recHead = [d \in Deployments |-> None]
  /\ pending = [d \in Deployments |-> [w \in Workers |-> {}]]
  /\ prepEpoch = [p \in Proofs |-> 0]
  /\ revises = [p \in Proofs |-> {}]
  /\ used = {}
  /\ published = {}
  /\ origin = [p \in Proofs |-> None]
  /\ known = [d \in Deployments |-> {}]

Prepare(d, w, p, R) ==
  /\ AtHome(d)
  /\ w = owner[d]
  /\ p \notin used
  /\ pending[d][w] = {}
  /\ R \subseteq known[d]
  /\ Closed(R)
  /\ recHead[d] = None \/ recHead[d] \in R
  /\ pending' = [pending EXCEPT ![d][w] = {p}]
  /\ prepEpoch' = [prepEpoch EXCEPT ![p] = epoch[d]]
  /\ revises' = [revises EXCEPT ![p] = R]
  /\ used' = used \cup {p}
  /\ UNCHANGED <<owner, epoch, recHead, published, origin, known>>

Publish(d, w, p) ==
  /\ AtHome(d)
  /\ p \in pending[d][w]
  /\ w = owner[d]
  /\ prepEpoch[p] = epoch[d]
  /\ recHead[d] = None \/ recHead[d] \in revises[p]
  /\ published' = published \cup {p}
  /\ origin' = [origin EXCEPT ![p] = d]
  /\ known' = [known EXCEPT ![d] = @ \cup {p}]
  /\ recHead' = [recHead EXCEPT ![d] = p]
  /\ pending' = [pending EXCEPT ![d][w] = {}]
  /\ UNCHANGED <<owner, epoch, prepEpoch, revises, used>>

Reassign(d, w) ==
  /\ AtHome(d)
  /\ epoch[d] < MaxEpoch
  /\ owner' = [owner EXCEPT ![d] = w]
  /\ epoch' = [epoch EXCEPT ![d] = @ + 1]
  /\ UNCHANGED <<recHead, pending, prepEpoch, revises, used,
                 published, origin, known>>

Abandon(d, w, p) ==
  /\ p \in pending[d][w]
  /\ prepEpoch[p] # epoch[d]
  /\ pending' = [pending EXCEPT ![d][w] = {}]
  /\ UNCHANGED <<owner, epoch, recHead, prepEpoch, revises, used,
                 published, origin, known>>

(* `origin` abstracts a checked home publication certificate, not the
   immediately preceding transport peer. Relays preserve that evidence. *)
Receive(d, p) ==
  /\ p \in published \ known[d]
  /\ origin[p] = Home
  /\ revises[p] \subseteq known[d]
  /\ known' = [known EXCEPT ![d] = @ \cup {p}]
  /\ UNCHANGED <<owner, epoch, recHead, pending, prepEpoch, revises,
                 used, published, origin>>

Next ==
  \/ \E d \in Deployments, w \in Workers, p \in Proofs, R \in SUBSET Proofs :
       Prepare(d, w, p, R)
  \/ \E d \in Deployments, w \in Workers, p \in Proofs :
       Publish(d, w, p) \/ Abandon(d, w, p)
  \/ \E d \in Deployments, w \in Workers : Reassign(d, w)
  \/ \E d \in Deployments, p \in Proofs : Receive(d, p)

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ \A d \in Deployments, p \in Proofs : WF_vars(Receive(d, p))

TypeOK ==
  /\ owner \in [Deployments -> Workers]
  /\ epoch \in [Deployments -> 0..MaxEpoch]
  /\ recHead \in [Deployments -> published \cup {None}]
  /\ pending \in [Deployments -> [Workers -> SUBSET Proofs]]
  /\ prepEpoch \in [Proofs -> 0..MaxEpoch]
  /\ revises \in [Proofs -> SUBSET Proofs]
  /\ published \subseteq used /\ used \subseteq Proofs
  /\ origin \in [Proofs -> Deployments \cup {None}]
  /\ known \in [Deployments -> SUBSET published]
HomeAuthority == \A p \in published : origin[p] = Home
RemoteRegistersUnchanged ==
  \A d \in Deployments \ {Home} :
    owner[d] = InitialOwner /\ epoch[d] = 0 /\ recHead[d] = None
TargetChain ==
  \A p, q \in published : p = q \/ p \in revises[q] \/ q \in revises[p]
HeadUnique == \A d \in Deployments : Cardinality(Heads(d)) <= 1
HomeHeadTopsChain ==
  /\ (published = {}) = (recHead[Home] = None)
  /\ \A p \in published : p = recHead[Home] \/ p \in revises[recHead[Home]]
EventualDelivery == \A d \in Deployments, p \in Proofs :
  (p \in published) ~> (p \in known[d])

(* Reachability witnesses checked as expected invariant failures. *)
NeverPublished == published = {}
NeverRemoteReceived == \A d \in Deployments \ {Home} : known[d] = {}
NeverReassignedPublication ==
  ~\E p \in published : prepEpoch[p] > 0
=============================================================================
