----------------------------- MODULE W4Scale -----------------------------
(* A bounded controller model. Each shard version is a transactionally advanced
   FDB counter (an ordered FDB read-version abstraction also suffices), never a
   process wall clock. All checks and writes in a named action are one
   serializable transaction. Objects are controller snapshot incarnations:
   a later authorized save may use the same content hash with a new generation.
   P2 protocol/S3 objects are outside this model and remain grow-only.
   W3 tombstones are modelled only as roots: a tombstoned position leaves the
   live view, but its record, certificates and marker remain an RGA anchor and
   lineage, so nothing reachable from them may be collected. *)
EXTENDS Naturals, FiniteSets

CONSTANTS Shards, Workers, Objects, MaxVersion, LeaseSpan, Grace

VARIABLES version, holder, term, expiry, heldTerm, pending, pendingTerm,
          roots, live, retired, deleted, known, demand, checkpoint, catalog,
          retained, commitFenced, fetchDemanded, recovered, handoverPublished,
          lostDesktop, tombstoned

vars == <<version, holder, term, expiry, heldTerm, pending, pendingTerm,
          roots, live, retired, deleted, known, demand, checkpoint, catalog,
          retained, commitFenced, fetchDemanded, recovered, handoverPublished,
          lostDesktop, tombstoned>>

None == "none"
Deps == [o \in Objects |-> IF o = "dependent" THEN {"base"} ELSE {}]
Home == [o \in Objects |-> IF o = "dependent" THEN "s2" ELSE "s1"]
InitialRoot == [s \in Shards |-> IF s = "s1" THEN "base" ELSE None]
Range(f) == {f[x] : x \in DOMAIN f}
TombstoneRoots == tombstoned
RootSet == (Range(roots) \ {None}) \cup pending \cup checkpoint \cup catalog
           \cup retained \cup UNION {demand[w] : w \in Workers}
           \cup TombstoneRoots
ActualRootSet == (Range(roots) \ {None}) \cup pending \cup checkpoint
                 \cup catalog \cup retained
                 \cup UNION {demand[w] : w \in Workers}
                 \cup tombstoned
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
  /\ tombstoned = {}

Advance(s) ==
  /\ version[s] < MaxVersion
  /\ version' = [version EXCEPT ![s] = @ + 1]
  /\ UNCHANGED <<holder, term, expiry, heldTerm, pending, pendingTerm,
                 roots, live, retired, deleted, known, demand, checkpoint,
                 catalog, retained, commitFenced, fetchDemanded, recovered,
                 handoverPublished, lostDesktop, tombstoned>>

Acquire(s, w) ==
  /\ expiry[s] <= version[s]
  /\ holder' = [holder EXCEPT ![s] = w]
  /\ term' = [term EXCEPT ![s] = @ + 1]
  /\ expiry' = [expiry EXCEPT ![s] = version[s] + LeaseSpan]
  /\ heldTerm' = [heldTerm EXCEPT ![w][s] = term[s] + 1]
  /\ UNCHANGED <<version, pending, pendingTerm, roots, live, retired,
                 deleted, known, demand, checkpoint, catalog, commitFenced,
                 retained, fetchDemanded, recovered, handoverPublished,
                 lostDesktop, tombstoned>>

Renew(s, w) ==
  /\ LeaseOK(s, w)
  /\ heldTerm[w][s] = term[s]
  /\ expiry' = [expiry EXCEPT ![s] = version[s] + LeaseSpan]
  /\ UNCHANGED <<version, holder, term, heldTerm, pending, pendingTerm,
                 roots, live, retired, deleted, known, demand, checkpoint,
                 catalog, retained, commitFenced, fetchDemanded, recovered,
                 handoverPublished, lostDesktop, tombstoned>>

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
                 handoverPublished, lostDesktop, tombstoned>>

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
                 retained, fetchDemanded, recovered, lostDesktop, tombstoned>>

AbortStale(o) ==
  /\ o \in pending
  /\ pendingTerm[o] # term[Home[o]]
  /\ pending' = pending \ {o}
  /\ UNCHANGED <<version, holder, term, expiry, heldTerm, pendingTerm,
                 roots, live, retired, deleted, known, demand, checkpoint,
                 catalog, retained, commitFenced, fetchDemanded, recovered,
                 handoverPublished, lostDesktop, tombstoned>>

PinCheckpoint(o) ==
  /\ o = "base"
  /\ o \in live
  /\ Deps[o] \subseteq live
  /\ checkpoint' = checkpoint \cup {o}
  /\ UNCHANGED <<version, holder, term, expiry, heldTerm, pending,
                 pendingTerm, roots, live, retired, deleted, known, demand,
                 catalog, retained, commitFenced, fetchDemanded, recovered,
                 handoverPublished, lostDesktop, tombstoned>>

PinCatalog(o) ==
  /\ o = "base"
  /\ o \in live
  /\ Deps[o] \subseteq live
  /\ catalog' = catalog \cup {o}
  /\ UNCHANGED <<version, holder, term, expiry, heldTerm, pending,
                 pendingTerm, roots, live, retired, deleted, known, demand,
                 checkpoint, retained, commitFenced, fetchDemanded, recovered,
                 handoverPublished, lostDesktop, tombstoned>>

PinRetained(o) ==
  /\ o = "base"
  /\ o \in live
  /\ Deps[o] \subseteq live
  /\ retained' = retained \cup {o}
  /\ UNCHANGED <<version, holder, term, expiry, heldTerm, pending,
                 pendingTerm, roots, live, retired, deleted, known, demand,
                 checkpoint, catalog, commitFenced, fetchDemanded, recovered,
                 handoverPublished, lostDesktop, tombstoned>>

(* A tombstoned position leaves the live file view; its lineage stays a root. *)
Tombstone(o) ==
  /\ o = "base"
  /\ o \in live
  /\ Deps[o] \subseteq live
  /\ tombstoned' = tombstoned \cup {o}
  /\ UNCHANGED <<version, holder, term, expiry, heldTerm, pending,
                 pendingTerm, roots, live, retired, deleted, known, demand,
                 checkpoint, catalog, retained, commitFenced, fetchDemanded,
                 recovered, handoverPublished, lostDesktop>>

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
                 handoverPublished, lostDesktop, tombstoned>>

LoseDesktop(w) ==
  /\ w = "b"
  /\ known[w] # {}
  /\ known' = [known EXCEPT ![w] = {}]
  /\ demand' = [demand EXCEPT ![w] = {}]
  /\ lostDesktop' = TRUE
  /\ UNCHANGED <<version, holder, term, expiry, heldTerm, pending,
                 pendingTerm, roots, live, retired, deleted, checkpoint,
                 catalog, retained, commitFenced, fetchDemanded, recovered,
                 handoverPublished, tombstoned>>

Request(w, o) ==
  /\ w = "b"
  /\ o = "base"
  /\ o \in Protected \cap live
  /\ demand' = [demand EXCEPT ![w] = @ \cup {o}]
  /\ UNCHANGED <<version, holder, term, expiry, heldTerm, pending,
                 pendingTerm, roots, live, retired, deleted, known,
                 checkpoint, catalog, retained, commitFenced, fetchDemanded,
                 recovered, handoverPublished, lostDesktop, tombstoned>>

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
                 handoverPublished, lostDesktop, tombstoned>>

Next == (\E s \in Shards : Advance(s))
  \/ (\E s \in Shards, w \in Workers : Acquire(s, w) \/ Renew(s, w))
  \/ (\E w \in Workers, o \in Objects : Stage(w, o) \/ Publish(w, o)
                                            \/ Request(w, o) \/ Fetch(w, o))
  \/ (\E o \in Objects : PinCheckpoint(o) \/ PinCatalog(o) \/ PinRetained(o)
                         \/ Tombstone(o) \/ Collect(o) \/ AbortStale(o))
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
NeverTombstoned == tombstoned = {}

=============================================================================
