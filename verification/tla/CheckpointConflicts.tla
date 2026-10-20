----------------------- MODULE CheckpointConflicts -----------------------
EXTENDS FiniteSets, Naturals

(* A finite commit-boundary model for OPEN-26. `ancestor` is per-name revision
   ancestry, already validated at publication. Tombstones remove a head from
   the current file view; an unrelated live head blocks either branch. The two
   Boolean constants are guard-removal probes, not protocol configuration. *)
CONSTANTS Groups, Names, member, ancestor, deps, CheckBuildable, CheckCurrent, CheckDeps
VARIABLES published, tombstoned, selected, committed, lastCommit
vars == <<published, tombstoned, selected, committed, lastCommit>>

Live == published \ tombstoned
Heads(x) == {g \in Live : member[g][x] /\
                    ~\E h \in published : ancestor[h][g][x]}
Unrelated(g, h, x) == g # h /\ member[g][x] /\ member[h][x] /\
                         ~ancestor[g][h][x] /\ ~ancestor[h][g][x]
Buildable(S) == \A g, h \in S : \A x \in Names :
                  (g # h) => ~(member[g][x] /\ member[h][x])
DepsClosed(S) == \A g \in S : deps[g] \subseteq S
Current(S) == \A g \in S : \A x \in Names :
                  member[g][x] =>
                    (Heads(x) = {g} \/
                     (g \in tombstoned /\ Heads(x) = {} /\
                      ~\E h \in published : ancestor[h][g][x]))
CommitGuard(S) == (~CheckBuildable \/ Buildable(S)) /\
                  (~CheckDeps \/ DepsClosed(S)) /\
                  (~CheckCurrent \/ Current(S))

Init == /\ published = {}
        /\ tombstoned = {}
        /\ selected = {}
        /\ committed = {}
        /\ lastCommit = FALSE
Publish(g) == /\ g \in Groups \ published
              /\ published' = published \cup {g}
              /\ lastCommit' = FALSE
              /\ UNCHANGED <<tombstoned, selected, committed>>
Tombstone(g) == /\ g \in published \ tombstoned
                /\ tombstoned' = tombstoned \cup {g}
                /\ lastCommit' = FALSE
                /\ UNCHANGED <<published, selected, committed>>
Select(S) == /\ S \in SUBSET published
             /\ selected' = S
             /\ lastCommit' = FALSE
             /\ UNCHANGED <<published, tombstoned, committed>>
Commit == /\ selected # {}
          /\ CommitGuard(selected)
          /\ committed' = committed \cup {selected}
          /\ lastCommit' = TRUE
          /\ UNCHANGED <<published, tombstoned, selected>>
Next == (\E g \in Groups : Publish(g) \/ Tombstone(g)) \/
        (\E S \in SUBSET Groups : Select(S)) \/ Commit
Spec == Init /\ [][Next]_vars

TypeOK == /\ published \subseteq Groups /\ tombstoned \subseteq published
          /\ selected \subseteq published /\ committed \subseteq SUBSET Groups
          /\ lastCommit \in BOOLEAN
CommittedBuildable == \A S \in committed : Buildable(S)
CommittedDeps == \A S \in committed : DepsClosed(S)
(* The commit event, not later publication, is where freshness is required. *)
CommitCurrent == lastCommit => Current(selected)
CaseMember == [g \in {"a", "b", "merge", "d"} |-> [x \in {"x", "y"} |->
  IF g = "d" THEN x = "y" ELSE x = "x"]]
CaseAncestor == [g \in {"a", "b", "merge", "d"} |-> [h \in {"a", "b", "merge", "d"} |->
  [x \in {"x", "y"} |-> g = "merge" /\ h \in {"a", "b"} /\ x = "x"]]]
CaseDeps == [g \in {"a", "b", "merge", "d"} |-> IF g = "d" THEN {"b"} ELSE {}]
NoHistoricalTombstonedCommit ==
  ~(lastCommit /\ selected = {"a"} /\ "a" \in tombstoned /\ Heads("x") = {})
=============================================================================
