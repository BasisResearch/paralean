----------------------------- MODULE W4Scale -----------------------------
(* A bounded controller model. Each shard version is a transactionally advanced
   FDB counter (an ordered FDB read-version abstraction also suffices), never a
   process wall clock. All checks and writes in a named action are one
   serializable transaction. Objects are controller snapshot incarnations:
   a later authorized save may use the same content hash with a new generation.
   P2 protocol/S3 objects are outside this model and remain grow-only. *)
EXTENDS Naturals, FiniteSets

CONSTANTS Shards, Workers, Objects, MaxVersion, LeaseSpan, Grace

VARIABLES version, holder, term, expiry, heldTerm, pending, pendingTerm,
          roots, live, retired, deleted, known, demand, checkpoint, catalog,
          retained, commitFenced, fetchDemanded, recovered, handoverPublished,
          lostDesktop

vars == <<version, holder, term, expiry, heldTerm, pending, pendingTerm,
          roots, live, retired, deleted, known, demand, checkpoint, catalog,
          retained, commitFenced, fetchDemanded, recovered, handoverPublished,
          lostDesktop>>

None == "none"
Deps == [o \in Objects |-> IF o = "dependent" THEN {"base"} ELSE {}]
Home == [o \in Objects |-> IF o = "dependent" THEN "s2" ELSE "s1"]
InitialRoot == [s \in Shards |-> IF s = "s1" THEN "base" ELSE None]
Range(f) == {f[x] : x \in DOMAIN f}
RootSet == (Range(roots) \ {None}) \cup pending \cup checkpoint \cup catalog
           \cup retained \cup UNION {demand[w] : w \in Workers}
ActualRootSet == (Range(roots) \ {None}) \cup pending \cup checkpoint
                 \cup catalog \cup retained
                 \cup UNION {demand[w] : w \in Workers}
Closure(R) == R \cup UNION {Deps[o] : o \in R}
Protected == Closure(Closure(Closure(RootSet)))
LeaseOK(s, w) == holder[s] = w /\ version[s] < expiry[s]
TermOK(s, w, o) == LeaseOK(s, w) /\ pendingTerm[o] = term[s]
OldEnough(o) == retired[o] > 0 /\ version[Home[o]] >= retired[o] + Grace

Init ==
  /\ version = [s \in Shards |-> 1]
  /\ holder = [s \in Shards |-> None]
  /\ term = [s \in Shards |-> 0]
  /\ expiry = [s \in Shards |-> 0]
  /\ heldTerm = [w \in Workers |-> [s \in Shards |-> 0]]
  /\ pending = {}
  /\ pendingTerm = [o \in Objects |-> 0]
  /\ roots = InitialRoot
  /\ live = Objects
  /\ retired = [o \in Objects |-> 0]
  /\ deleted = {}
  /\ known = [w \in Workers |-> {}]
  /\ demand = [w \in Workers |-> {}]
  /\ checkpoint = {}
  /\ catalog = {}
  /\ retained = {}
  /\ commitFenced = TRUE
  /\ fetchDemanded = TRUE
  /\ recovered = [w \in Workers |-> {}]
  /\ handoverPublished = FALSE
  /\ lostDesktop = FALSE

Advance(s) ==
  /\ version[s] < MaxVersion
  /\ version' = [version EXCEPT ![s] = @ + 1]
  /\ UNCHANGED <<holder, term, expiry, heldTerm, pending, pendingTerm,
                 roots, live, retired, deleted, known, demand, checkpoint,
                 catalog, retained, commitFenced, fetchDemanded, recovered,
                 handoverPublished, lostDesktop>>

Acquire(s, w) ==
  /\ expiry[s] <= version[s]
  /\ holder' = [holder EXCEPT ![s] = w]
  /\ term' = [term EXCEPT ![s] = @ + 1]
  /\ expiry' = [expiry EXCEPT ![s] = version[s] + LeaseSpan]
  /\ heldTerm' = [heldTerm EXCEPT ![w][s] = term[s] + 1]
  /\ UNCHANGED <<version, pending, pendingTerm, roots, live, retired,
                 deleted, known, demand, checkpoint, catalog, commitFenced,
                 retained, fetchDemanded, recovered, handoverPublished,
                 lostDesktop>>

Renew(s, w) ==
  /\ LeaseOK(s, w)
  /\ heldTerm[w][s] = term[s]
  /\ expiry' = [expiry EXCEPT ![s] = version[s] + LeaseSpan]
  /\ UNCHANGED <<version, holder, term, heldTerm, pending, pendingTerm,
                 roots, live, retired, deleted, known, demand, checkpoint,
                 catalog, retained, commitFenced, fetchDemanded, recovered,
                 handoverPublished, lostDesktop>>

Stage(w, o) ==
  /\ o \in live \ pending
  /\ o \notin Range(roots)
  /\ Deps[o] \subseteq live
  /\ LeaseOK(Home[o], w)
  /\ pending' = pending \cup {o}
  /\ pendingTerm' = [pendingTerm EXCEPT ![o] = heldTerm[w][Home[o]]]
  /\ UNCHANGED <<version, holder, term, expiry, heldTerm, roots, live,
                 retired, deleted, known, demand, checkpoint, catalog,
                 retained, commitFenced, fetchDemanded, recovered,
                 handoverPublished, lostDesktop>>

Publish(w, o) ==
  /\ o \in pending
  /\ TermOK(Home[o], w, o)
  /\ Deps[o] \subseteq live
  /\ LET old == roots[Home[o]] IN
       retired' = IF old = None THEN retired
                  ELSE [retired EXCEPT ![old] = version[Home[old]]]
  /\ roots' = [roots EXCEPT ![Home[o]] = o]
  /\ pending' = pending \ {o}
  /\ commitFenced' = (commitFenced /\ holder[Home[o]] = w
                       /\ version[Home[o]] < expiry[Home[o]]
                       /\ heldTerm[w][Home[o]] = term[Home[o]]
                       /\ pendingTerm[o] = term[Home[o]])
  /\ handoverPublished' = (handoverPublished \/ term[Home[o]] > 1)
  /\ UNCHANGED <<version, holder, term, expiry, heldTerm, pendingTerm,
                 live, deleted, known, demand, checkpoint, catalog,
                 retained, fetchDemanded, recovered, lostDesktop>>

AbortStale(o) ==
  /\ o \in pending
  /\ pendingTerm[o] # term[Home[o]]
  /\ pending' = pending \ {o}
  /\ UNCHANGED <<version, holder, term, expiry, heldTerm, pendingTerm,
                 roots, live, retired, deleted, known, demand, checkpoint,
                 catalog, retained, commitFenced, fetchDemanded, recovered,
                 handoverPublished, lostDesktop>>

PinCheckpoint(o) ==
  /\ o = "base"
  /\ o \in live
  /\ Deps[o] \subseteq live
  /\ checkpoint' = checkpoint \cup {o}
  /\ UNCHANGED <<version, holder, term, expiry, heldTerm, pending,
                 pendingTerm, roots, live, retired, deleted, known, demand,
                 catalog, retained, commitFenced, fetchDemanded, recovered,
                 handoverPublished, lostDesktop>>

PinCatalog(o) ==
  /\ o = "base"
  /\ o \in live
  /\ Deps[o] \subseteq live
  /\ catalog' = catalog \cup {o}
  /\ UNCHANGED <<version, holder, term, expiry, heldTerm, pending,
                 pendingTerm, roots, live, retired, deleted, known, demand,
                 checkpoint, retained, commitFenced, fetchDemanded, recovered,
                 handoverPublished, lostDesktop>>

PinRetained(o) ==
  /\ o = "base"
  /\ o \in live
  /\ Deps[o] \subseteq live
  /\ retained' = retained \cup {o}
  /\ UNCHANGED <<version, holder, term, expiry, heldTerm, pending,
                 pendingTerm, roots, live, retired, deleted, known, demand,
                 checkpoint, catalog, commitFenced, fetchDemanded, recovered,
                 handoverPublished, lostDesktop>>

(* Root membership and the deletion conflict-read occur in the same FDB
   transaction. A retained snapshot starts its grace when superseded. *)
Collect(o) ==
  /\ o \in live
  /\ o \notin Protected
  /\ OldEnough(o)
  /\ live' = live \ {o}
  /\ deleted' = deleted \cup {o}
  /\ known' = [w \in Workers |-> known[w] \ {o}]
  /\ UNCHANGED <<version, holder, term, expiry, heldTerm, pending,
                 pendingTerm, roots, retired, demand, checkpoint, catalog,
                 retained, commitFenced, fetchDemanded, recovered,
                 handoverPublished, lostDesktop>>

LoseDesktop(w) ==
  /\ w = "b"
  /\ known[w] # {}
  /\ known' = [known EXCEPT ![w] = {}]
  /\ demand' = [demand EXCEPT ![w] = {}]
  /\ lostDesktop' = TRUE
  /\ UNCHANGED <<version, holder, term, expiry, heldTerm, pending,
                 pendingTerm, roots, live, retired, deleted, checkpoint,
                 catalog, retained, commitFenced, fetchDemanded, recovered,
                 handoverPublished>>

Request(w, o) ==
  /\ w = "b"
  /\ o = "base"
  /\ o \in Protected \cap live
  /\ demand' = [demand EXCEPT ![w] = @ \cup {o}]
  /\ UNCHANGED <<version, holder, term, expiry, heldTerm, pending,
                 pendingTerm, roots, live, retired, deleted, known,
                 checkpoint, catalog, retained, commitFenced, fetchDemanded,
                 recovered, handoverPublished, lostDesktop>>

(* A demand-driven recovery fetch can only read a still-live incarnation. A
   retired incarnation is not revived by an old advertisement. *)
Fetch(w, o) ==
  /\ o \in demand[w]
  /\ o \in live
  /\ known' = [known EXCEPT ![w] = @ \cup {o}]
  /\ fetchDemanded' = (fetchDemanded /\ (o \in demand[w]))
  /\ recovered' = IF lostDesktop
                  THEN [recovered EXCEPT ![w] = @ \cup {o}]
                  ELSE recovered
  /\ UNCHANGED <<version, holder, term, expiry, heldTerm, pending,
                 pendingTerm, roots, live, retired, deleted, demand,
                 checkpoint, catalog, retained, commitFenced,
                 handoverPublished, lostDesktop>>

Next == (\E s \in Shards : Advance(s))
  \/ (\E s \in Shards, w \in Workers : Acquire(s, w) \/ Renew(s, w))
  \/ (\E w \in Workers, o \in Objects : Stage(w, o) \/ Publish(w, o)
                                            \/ Request(w, o) \/ Fetch(w, o))
  \/ (\E o \in Objects : PinCheckpoint(o) \/ PinCatalog(o) \/ PinRetained(o)
                         \/ Collect(o) \/ AbortStale(o))
  \/ (\E w \in Workers : LoseDesktop(w))
Spec == Init /\ [][Next]_vars

RootsLive == Closure(Closure(Closure(ActualRootSet))) \subseteq live
NoResurrection == deleted \cap live = {}
NoStalePublish == commitFenced
NoUnrequestedFetch == fetchDemanded
GraceKept == \A o \in deleted : retired[o] > 0
                              /\ version[Home[o]] >= retired[o] + Grace
NoDemandDeleted == \A w \in Workers : demand[w] \cap deleted = {}
NeverHandover == \A s \in Shards : term[s] <= 1
NeverCrossShardPublished == \A s \in Shards : roots[s] = InitialRoot[s]
NeverCollected == deleted = {}
NeverRecovered == \A w \in Workers : recovered[w] = {}
NeverHandoverPublished == ~handoverPublished
NeverDependentPublished == roots["s2"] # "dependent"
NeverRetained == retained = {}

=============================================================================
