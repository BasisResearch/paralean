----------------------------- MODULE Registry -----------------------------
EXTENDS FiniteSets, TLC

CONSTANTS Nodes, Decls, Names, Name, Deps, Ancestors, Valid, Exportable,
          CollisionLeft, CollisionRight

ASSUME /\ Nodes # {}
       /\ Decls # {}
       /\ Name \in [Decls -> Names]
       /\ Deps \in [Decls -> SUBSET Decls]
       /\ Ancestors \in [Decls -> SUBSET Decls]
       /\ Valid \subseteq Decls
       /\ \A d \in Valid : \A a \in Ancestors[d] :
             Name[a] = Name[d] /\ Ancestors[a] \subseteq Ancestors[d]
       /\ Exportable \subseteq SUBSET Decls
       /\ {} \in Exportable
       /\ CollisionLeft \in Decls
       /\ CollisionRight \in Decls

VARIABLES published, known, pending, head, alive, online, stable,
          lastCommitCurrent
vars == <<published, known, pending, head, alive, online, stable,
          lastCommitCurrent>>

Closed(S) == \A d \in S : Deps[d] \subseteq S
CausallyClosed(S) == \A d \in S : Ancestors[d] \subseteq S
Compatible(S) == \A a, b \in S : Name[a] = Name[b] => a = b
Buildable(S) == /\ S \subseteq Valid
                /\ Closed(S)
                /\ Compatible(S)
                /\ S \in Exportable
Heads(K, name) == {d \in K : Name[d] = name /\
                              ~\E e \in K : d \in Ancestors[e]}
Conflict(K, name) == \E a, b \in Heads(K, name) : a # b
Current(K, S) == \A d \in S : Heads(K, Name[d]) = {d}
(* No numeric ranks: every nonempty subset has a dependency-free member. *)
Acyclic(S) == \A T \in (SUBSET S) \ {{} } :
                \E d \in T : Deps[d] \intersect T = {}

Init == /\ published = {}
        /\ known = [n \in Nodes |-> {}]
        /\ pending = [n \in Nodes |-> {}]
        /\ head = [n \in Nodes |-> {}]
        /\ alive = Nodes
        /\ online = Nodes
        /\ stable = FALSE
        /\ lastCommitCurrent = TRUE

(* Valid is the abstract trusted checker interface. Drafts cannot enter known.
   Ancestors are explicit causal edits, never an inferred clock order. *)
Prepare(n, d) ==
    /\ n \in alive
    /\ d \in Valid
    /\ Deps[d] \subseteq known[n]
    /\ Ancestors[d] \subseteq known[n]
    /\ d \notin Deps[d] \cup Ancestors[d]
    /\ pending' = [pending EXCEPT ![n] = @ \cup {d}]
    /\ UNCHANGED <<published, known, head, alive, online, stable,
                   lastCommitCurrent>>

(* This action linearizes the successful durable-store call. The storage
   implementation and its failure envelope are modeled in Durability.tla. *)
Publish(n, d) ==
    /\ n \in alive \intersect online
    /\ d \in pending[n]
    /\ published' = published \cup {d}
    /\ known' = [known EXCEPT ![n] = @ \cup {d}]
    /\ pending' = [pending EXCEPT ![n] = @ \ {d}]
    /\ UNCHANGED <<head, alive, online, stable, lastCommitCurrent>>

(* Anti-entropy can deliver any durable record, repeatedly and out of order.
   Receipt does not mean that its dependencies are locally materialized. *)
Receive(n, d) ==
    /\ n \in alive \intersect online
    /\ d \in published
    /\ d \notin known[n]
    /\ known' = [known EXCEPT ![n] = @ \cup {d}]
    /\ UNCHANGED <<published, pending, head, alive, online, stable,
                   lastCommitCurrent>>

Commit(n, S) ==
    /\ n \in alive \intersect online
    /\ S \subseteq known[n]
    /\ Buildable(S)
    /\ Current(known[n], S)
    /\ head' = [head EXCEPT ![n] = S]
    /\ lastCommitCurrent' = Current(known[n], S)
    /\ UNCHANGED <<published, known, pending, alive, online, stable>>

Crash(n) ==
    /\ ~stable
    /\ n \in alive
    /\ alive' = alive \ {n}
    /\ known' = [known EXCEPT ![n] = {}]
    /\ pending' = [pending EXCEPT ![n] = {}]
    /\ UNCHANGED <<published, head, online, stable, lastCommitCurrent>>

Recover(n) == /\ n \notin alive
              /\ alive' = alive \cup {n}
              /\ UNCHANGED <<published, known, pending, head, online, stable,
                             lastCommitCurrent>>

Partition(n) == /\ ~stable
                /\ n \in online
                /\ online' = online \ {n}
                /\ UNCHANGED <<published, known, pending, head, alive, stable,
                               lastCommitCurrent>>

Reconnect(n) == /\ n \notin online
                /\ online' = online \cup {n}
                /\ UNCHANGED <<published, known, pending, head, alive, stable,
                               lastCommitCurrent>>

(* Eventual recovery/connectivity is an explicit liveness assumption. Safety
   does not require Heal to occur and allows permanent partitions/crashes. *)
Heal == /\ ~stable
        /\ stable' = TRUE
        /\ alive' = Nodes
        /\ online' = Nodes
        /\ UNCHANGED <<published, known, pending, head, lastCommitCurrent>>

Next == \/ \E n \in Nodes, d \in Decls : Prepare(n, d) \/ Publish(n, d) \/ Receive(n, d)
        \/ \E n \in Nodes, S \in SUBSET Decls : Commit(n, S)
        \/ \E n \in Nodes : Crash(n) \/ Recover(n) \/ Partition(n) \/ Reconnect(n)
        \/ Heal

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Heal)
            /\ \A n \in Nodes, d \in Decls : WF_vars(Receive(n, d))

TypeOK == /\ published \subseteq Decls
          /\ known \in [Nodes -> SUBSET Decls]
          /\ pending \in [Nodes -> SUBSET Decls]
          /\ head \in [Nodes -> SUBSET Decls]
          /\ alive \subseteq Nodes
          /\ online \subseteq Nodes
          /\ stable \in BOOLEAN
          /\ lastCommitCurrent \in BOOLEAN
AdmissionSafety == /\ published \subseteq Valid
                   /\ Closed(published)
                   /\ Acyclic(published)
                   /\ \A n \in Nodes : known[n] \subseteq published
                   /\ \A n \in Nodes : \A d \in pending[n] :
                         d \in Valid /\ Deps[d] \subseteq published
PublishedAncestorSafety == CausallyClosed(published)
PendingAncestorSafety == \A n \in Nodes : \A d \in pending[n] :
                          Ancestors[d] \subseteq published
CausalAdmissionSafety == PublishedAncestorSafety /\ PendingAncestorSafety
(* Observational ghost state: erase lastCommitCurrent to recover the Lean
   registry state. Commit writes its PRE-STATE Current check; other actions
   preserve it. Thus a stale repeated commit is visible even when head does
   not change. Later receives/publications may make an old snapshot stale. *)
CommitFreshness == lastCommitCurrent
SnapshotSafety == \A n \in Nodes : Buildable(head[n]) /\ head[n] \subseteq published
CollisionSafety == \A n \in Nodes, name \in Names :
                       Conflict(known[n], name) =>
                         ~\E d \in Heads(known[n], name) : Current(known[n], {d})

EventualDelivery == \A n \in Nodes, d \in Decls :
                       d \in published ~> d \in known[n]
Convergence == <>[](\A n \in Nodes : known[n] = published)
(* This property is instantiated with a conflicting pair having no descendants
   in the finite scenario. Explicit later resolution would change the premise. *)
EventualCollision ==
    ({CollisionLeft, CollisionRight} \subseteq published) ~>
      (\A n \in Nodes : Conflict(known[n], Name[CollisionLeft]))

(* Coverage goals: EXPECT invariant failure; witness files record reachable
   useful work. These are not correctness requirements. *)
NeverPublished == published = {}
NeverCommitted == \A n \in Nodes : head[n] = {}
NeverCollided == \A n \in Nodes, name \in Names : ~Conflict(known[n], name)
=============================================================================
