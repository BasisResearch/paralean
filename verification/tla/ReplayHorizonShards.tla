------------------------- MODULE ReplayHorizonShards -------------------------
(* Replay horizons (Design 3) across dynamic shards (Design 2). Each shard has
   its own replay generation G[s]. Replay rows stay at the shard that
   compacted them and are read across every shard ever in the topology, so a
   duplicate of work compacted at A is recognised after its bucket moved to B.
   A request's bucket may move between shards; its active work travels with it
   (ShardHandover checks the handoff itself). Leases, terms and the in-txn
   generation check are checked in ReplayHorizon; here every action is one
   fenced transaction by the current leader of the shard it names.

   The design as written retires a row of generation g at shard s once
   g <= G[s] - 2 there. A shard with a lagging generation still accepts g, and
   finds no row. The fix checked here: a row of generation g is retired only
   when every shard in the topology has refused g for Grace ticks, and a shard
   added later starts at the largest generation in the topology. *)
EXTENDS Naturals, FiniteSets

CONSTANTS Shards, InitialShards, Ids, MaxGen, MaxTick, H, Grace, MaxExec

Gens == 0..MaxGen
Keys == Gens \X Ids
Gen(k) == k[1]
Id(k) == k[2]

VARIABLES tick, members, G, started, home, snapshot, row, exec,
          retiredAny, crossDedupe
vars == <<tick, members, G, started, home, snapshot, row, exec,
          retiredAny, crossDedupe>>

Topology == {s \in Shards : members[s] # "Absent"}
Accepted(s) == {x \in Gens : x = G[s] \/ x + 1 = G[s]} \cup {0}
RefusedLongEnough(s, g) == g + 2 <= G[s] /\ tick >= started[s] + Grace
(* Retirement reads every shard's generation record in its transaction. *)
RetireOK(s, g) == \A t \in Topology : RefusedLongEnough(t, g)
StartGen == LET gs == {G[t] : t \in Topology} IN
            CHOOSE x \in gs : \A y \in gs : y <= x

Init ==
  /\ tick = 0
  /\ members = [s \in Shards |-> IF s \in InitialShards THEN "Active" ELSE "Absent"]
  /\ G = [s \in Shards |-> 1]
  /\ started = [s \in Shards |-> 0]
  /\ home = [i \in Ids |-> CHOOSE s \in InitialShards : TRUE]
  /\ snapshot = [k \in Keys |-> "absent"]
  /\ row = [s \in Shards |-> [k \in Keys |-> FALSE]]
  /\ exec = [k \in Keys |-> 0]
  /\ retiredAny = FALSE
  /\ crossDedupe = FALSE

Tick ==
  /\ tick < MaxTick
  /\ tick' = tick + 1
  /\ UNCHANGED <<members, G, started, home, snapshot, row, exec, retiredAny,
                 crossDedupe>>

Advance(s) ==
  /\ members[s] = "Active"
  /\ G[s] < MaxGen
  /\ tick >= started[s] + H
  /\ G' = [G EXCEPT ![s] = @ + 1]
  /\ started' = [started EXCEPT ![s] = tick]
  /\ UNCHANGED <<tick, members, home, snapshot, row, exec, retiredAny,
                 crossDedupe>>

AddShard(s) ==
  /\ members[s] = "Absent"
  /\ members' = [members EXCEPT ![s] = "Active"]
  /\ G' = [G EXCEPT ![s] = StartGen]
  /\ started' = [started EXCEPT ![s] = tick]
  /\ UNCHANGED <<tick, home, snapshot, row, exec, retiredAny, crossDedupe>>

(* A bucket move: the ID's route and any active work go to dst. *)
Move(i, dst) ==
  /\ members[dst] = "Active"
  /\ home[i] # dst
  /\ home' = [home EXCEPT ![i] = dst]
  /\ UNCHANGED <<tick, members, G, started, snapshot, row, exec, retiredAny,
                 crossDedupe>>

(* The home shard decides; dedupe reads its snapshot and every shard's rows. *)
Submit(k) ==
  LET s == home[Id(k)] IN
  /\ Gen(k) \in Accepted(s)
  /\ IF snapshot[k] # "absent" \/ \E t \in Topology : row[t][k]
     THEN /\ crossDedupe' = (crossDedupe \/ (snapshot[k] = "absent" /\ ~row[s][k]))
          /\ UNCHANGED <<snapshot, exec>>
     ELSE /\ exec[k] < 2
          /\ Cardinality({x \in Keys : exec[x] > 0} \cup {k}) <= MaxExec
          /\ snapshot' = [snapshot EXCEPT ![k] = "done"]
          /\ exec' = [exec EXCEPT ![k] = @ + 1]
          /\ UNCHANGED crossDedupe
  /\ UNCHANGED <<tick, members, G, started, home, row, retiredAny>>

(* Terminal work becomes a replay row at the shard that holds it. *)
Compact(k) ==
  /\ snapshot[k] = "done"
  /\ snapshot' = [snapshot EXCEPT ![k] = "absent"]
  /\ row' = [row EXCEPT ![home[Id(k)]][k] = TRUE]
  /\ UNCHANGED <<tick, members, G, started, home, exec, retiredAny, crossDedupe>>

Retire(s, k) ==
  /\ row[s][k]
  /\ Gen(k) # 0
  /\ RetireOK(s, Gen(k))
  /\ row' = [row EXCEPT ![s][k] = FALSE]
  /\ retiredAny' = TRUE
  /\ UNCHANGED <<tick, members, G, started, home, snapshot, exec, crossDedupe>>

Next ==
  \/ Tick
  \/ \E s \in Shards : Advance(s) \/ AddShard(s)
  \/ \E i \in Ids, s \in Shards : Move(i, s)
  \/ \E k \in Keys : Submit(k) \/ Compact(k)
  \/ \E s \in Shards, k \in Keys : Retire(s, k)
Spec == Init /\ [][Next]_vars

AtMostOnce == \A k \in Keys : exec[k] <= 1

NeverRetired == ~retiredAny
NeverCrossShardDedupe == ~crossDedupe
=============================================================================
