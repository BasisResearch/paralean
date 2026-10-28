--------------------------- MODULE ReplayHorizon ---------------------------
(* W4-rest Design 3: replay horizons for one controller shard
   (docs/w4-rest-log.md). A client-chosen request ID is scoped by the shard's
   replay generation; a request is the pair (g, id). Generation 0 is legacy.

   The shard accepts generations G and G - 1, and 0 unless generation is
   required. The leader advances G under its lease and term once the shard
   clock passes started + H. The collector, fenced by the lease like snapshot
   GC, deletes terminal replay rows of generations at most G - 2 once G - 2 has
   been refused for Grace ticks. Terminal work leaves the snapshot only as a
   replay row in the same transaction (W4History's compaction step).

   A submission is a leader operation: Load reads the generation record with
   the snapshot; the commit decides refuse / deduplicate / execute and saves
   under the lease and term. The advance is a separate leader task, also
   load-then-save; it is not assumed to hold the operation lock. Clients are
   adversarial: any (g, id) may be sent, retried, delayed, duplicated or
   replayed at any time. Each named action is one FDB transaction.

   Design fix checked here: the commit re-reads the generation record in its
   own transaction (CommitGen). Deciding with the generation the operation
   loaded lets an advance and a retirement land between load and commit, and
   no logical Grace bounds that window (horizon_loaded_generation). Lease
   expiry is abstracted to an immediate takeover with term + 1, as in
   ShardHandover; W4Scale checks the expiry fence. Poll tokens, group and
   validation request IDs follow the same rule and are not modelled. *)
EXTENDS Naturals, FiniteSets

CONSTANTS Procs, Ids, MaxGen, MaxTick, MaxTerm, MaxExec, H, Grace

None == "none"
Gens == 0..MaxGen
Keys == Gens \X Ids
Gen(k) == k[1]

VARIABLES tick, holder, term, G, started, requireGen,
          busy, memG, opTerm, advBusy, advG, advTerm,
          snapshot, row, exec, finished, retired,
          answerBad, legacyDeleted, dedupedFromRow, refusedRetired
vars == <<tick, holder, term, G, started, requireGen,
          busy, memG, opTerm, advBusy, advG, advTerm,
          snapshot, row, exec, finished, retired,
          answerBad, legacyDeleted, dedupedFromRow, refusedRetired>>
leaseVars == <<holder, term>>
procVars == <<busy, memG, opTerm, advBusy, advG, advTerm>>
stateVars == <<snapshot, row, exec, finished, retired>>
ghostVars == <<answerBad, legacyDeleted, dedupedFromRow, refusedRetired>>

(* --- Guards. Each is named so a mutation can remove exactly one. --- *)
Accepted(gen) == {x \in Gens : x = gen \/ x + 1 = gen}
                 \cup (IF requireGen THEN {} ELSE {0})
(* The commit reads the generation record in its own transaction. *)
CommitGen(p) == G
LeaseFence(p) == holder = p /\ term = opTerm[p]
AdvanceFence(p) == holder = p /\ term = advTerm[p]
RetireFence(p) == holder = p
RetireGen(g) == g + 2 <= G
RetireLegacy(g) == g # 0
RetireGrace == tick >= started + Grace
TerminalOK(k) == snapshot[k] = "D"
(* The dedupe lookup: the exact (g, id) key. *)
Lookup(k) == {k}
Known(K) == \E x \in K : snapshot[x] # "absent" \/ row[x]

Init ==
  /\ tick = 0
  /\ holder = CHOOSE p \in Procs : TRUE
  /\ term = 1
  /\ G = 1
  /\ started = 0
  /\ requireGen \in BOOLEAN
  /\ busy = [p \in Procs |-> FALSE]
  /\ memG = [p \in Procs |-> 0]
  /\ opTerm = [p \in Procs |-> 0]
  /\ advBusy = [p \in Procs |-> FALSE]
  /\ advG = [p \in Procs |-> 0]
  /\ advTerm = [p \in Procs |-> 0]
  /\ snapshot = [k \in Keys |-> "absent"]
  /\ row = [k \in Keys |-> FALSE]
  /\ exec = [k \in Keys |-> 0]
  /\ finished = [k \in Keys |-> FALSE]
  /\ retired = {}
  /\ answerBad = FALSE
  /\ legacyDeleted = FALSE
  /\ dedupedFromRow = FALSE
  /\ refusedRetired = FALSE

Tick ==
  /\ tick < MaxTick
  /\ tick' = tick + 1
  /\ UNCHANGED <<leaseVars, G, started, requireGen, procVars, stateVars, ghostVars>>

(* The lease lapses and is acquired, possibly by the same process, with
   term + 1. The expiry fence itself is checked by W4Scale. *)
Takeover(p) ==
  /\ term < MaxTerm
  /\ holder' = p
  /\ term' = term + 1
  /\ UNCHANGED <<tick, G, started, requireGen, procVars, stateVars, ghostVars>>

(* A process dies with whatever operation or advance it was running. *)
Kill(p) ==
  /\ busy[p] \/ advBusy[p]
  /\ busy' = [busy EXCEPT ![p] = FALSE]
  /\ advBusy' = [advBusy EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<tick, leaseVars, G, started, requireGen, memG, opTerm, advG,
                 advTerm, stateVars, ghostVars>>

(* The operator flips --require-replay-generation at any time. *)
ToggleRequire ==
  /\ requireGen' = ~requireGen
  /\ UNCHANGED <<tick, leaseVars, G, started, procVars, stateVars, ghostVars>>

Load(p) ==
  /\ ~busy[p]
  /\ holder = p
  /\ busy' = [busy EXCEPT ![p] = TRUE]
  /\ memG' = [memG EXCEPT ![p] = G]
  /\ opTerm' = [opTerm EXCEPT ![p] = term]
  /\ UNCHANGED <<tick, leaseVars, G, started, requireGen, advBusy, advG,
                 advTerm, stateVars, ghostVars>>

EndOp(p) ==
  /\ busy' = [busy EXCEPT ![p] = FALSE]
  /\ memG' = [memG EXCEPT ![p] = 0]
  /\ opTerm' = [opTerm EXCEPT ![p] = 0]

(* A submission names (g, id). Every outcome is answered after the commit. *)
Submit(p, k) ==
  LET g == Gen(k)
      L == Lookup(k)
  IN
  /\ busy[p]
  /\ LeaseFence(p)
  /\ IF g \notin Accepted(CommitGen(p))
     THEN (* definite Expired; never executed *)
          /\ refusedRetired' = (refusedRetired \/ k \in retired)
          /\ UNCHANGED <<stateVars, answerBad, legacyDeleted, dedupedFromRow>>
     ELSE IF Known(L)
     THEN (* duplicate: answer from the stored entry or replay row *)
          /\ answerBad' = (answerBad \/ ~(snapshot[k] # "absent" \/ row[k]))
          /\ dedupedFromRow' = (dedupedFromRow \/ row[k])
          /\ UNCHANGED <<stateVars, legacyDeleted, refusedRetired>>
     ELSE (* first sight of (g, id): execute *)
          /\ exec[k] < 2
          /\ Cardinality({x \in Keys : exec[x] > 0} \cup {k}) <= MaxExec
          /\ snapshot' = [snapshot EXCEPT ![k] = "R"]
          /\ exec' = [exec EXCEPT ![k] = @ + 1]
          /\ UNCHANGED <<row, finished, retired, ghostVars>>
  /\ EndOp(p)
  /\ UNCHANGED <<tick, leaseVars, G, started, requireGen, advBusy, advG, advTerm>>

Abort(p) ==
  /\ busy[p]
  /\ EndOp(p)
  /\ UNCHANGED <<tick, leaseVars, G, started, requireGen, advBusy, advG,
                 advTerm, stateVars, ghostVars>>

(* The worker finishes running work; finishes refer to the job by ID. *)
Finish(p, k) ==
  /\ holder = p
  /\ snapshot[k] = "R"
  /\ snapshot' = [snapshot EXCEPT ![k] = "D"]
  /\ finished' = [finished EXCEPT ![k] = TRUE]
  /\ UNCHANGED <<tick, leaseVars, G, started, requireGen, procVars, row,
                 exec, retired, ghostVars>>

(* W4 history compaction: terminal work becomes a replay row atomically. *)
Compact(p, k) ==
  /\ holder = p
  /\ snapshot[k] # "absent"
  /\ TerminalOK(k)
  /\ snapshot' = [snapshot EXCEPT ![k] = "absent"]
  /\ row' = [row EXCEPT ![k] = TRUE]
  /\ UNCHANGED <<tick, leaseVars, G, started, requireGen, procVars, exec,
                 finished, retired, ghostVars>>

(* The leader's advance task: read the generation record, then save. *)
AdvanceRead(p) ==
  /\ ~advBusy[p]
  /\ holder = p
  /\ G < MaxGen
  /\ tick >= started + H
  /\ advBusy' = [advBusy EXCEPT ![p] = TRUE]
  /\ advG' = [advG EXCEPT ![p] = G]
  /\ advTerm' = [advTerm EXCEPT ![p] = term]
  /\ UNCHANGED <<tick, leaseVars, G, started, requireGen, busy, memG, opTerm,
                 stateVars, ghostVars>>

AdvanceCommit(p) ==
  /\ advBusy[p]
  /\ AdvanceFence(p)
  /\ G' = advG[p] + 1
  /\ started' = tick
  /\ advBusy' = [advBusy EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<tick, leaseVars, requireGen, busy, memG, opTerm, advG,
                 advTerm, stateVars, ghostVars>>

AdvanceAbort(p) ==
  /\ advBusy[p]
  /\ advBusy' = [advBusy EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<tick, leaseVars, G, started, requireGen, busy, memG, opTerm,
                 advG, advTerm, stateVars, ghostVars>>

(* The collector deletes one terminal replay row of a refused generation. *)
Retire(p, k) ==
  /\ row[k]
  /\ RetireFence(p)
  /\ RetireGen(Gen(k))
  /\ RetireLegacy(Gen(k))
  /\ RetireGrace
  /\ row' = [row EXCEPT ![k] = FALSE]
  /\ retired' = retired \cup {k}
  /\ legacyDeleted' = (legacyDeleted \/ Gen(k) = 0)
  /\ UNCHANGED <<tick, leaseVars, G, started, requireGen, procVars, snapshot,
                 exec, finished, answerBad, dedupedFromRow, refusedRetired>>

Next ==
  \/ Tick \/ ToggleRequire
  \/ \E p \in Procs : Takeover(p) \/ Kill(p) \/ Load(p) \/ Abort(p)
                      \/ AdvanceRead(p) \/ AdvanceCommit(p) \/ AdvanceAbort(p)
  \/ \E p \in Procs, k \in Keys : Submit(p, k) \/ Finish(p, k)
                                  \/ Compact(p, k) \/ Retire(p, k)
Spec == Init /\ [][Next]_vars

(* --- Safety. --- *)
AtMostOnce == \A k \in Keys : exec[k] <= 1
RetiredRefused == \A k \in retired : Gen(k) \notin Accepted(G)
ActiveNotLost == \A k \in Keys :
  exec[k] > 0 /\ ~finished[k] => snapshot[k] = "R"
AnswerConsistent == ~answerBad
LegacyKept == ~legacyDeleted

(* --- Reachability witnesses: each must be violated. --- *)
NeverAdvanced == G <= 1
NeverRetired == retired = {}
NeverDedupedFromRow == ~dedupedFromRow
NeverRefusedAfterRetire == ~refusedRetired
=============================================================================
