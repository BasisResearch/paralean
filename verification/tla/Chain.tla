------------------------------ MODULE Chain ------------------------------
EXTENDS Registry
CaseName == [d \in {"b", "a", "c"} |-> d]
CaseDeps == [d \in {"b", "a", "c"} |-> CASE d = "a" -> {"b"}
                                              [] d = "c" -> {"a"}
                                              [] OTHER -> {}]
CaseAncestors == [d \in {"b", "a", "c"} |-> {}]
CaseExportable == SUBSET {"b", "a", "c"}
(* A restricted execution of the same registry actions witnesses useful work:
   B publishes b, A consumes b and publishes a, B consumes a and publishes c.
   No additional protocol state or fairness assumption is introduced. *)
Producer == [d \in {"b", "a", "c"} |-> IF d = "a" THEN "A" ELSE "B"]
ChainWorkNext ==
    \/ \E n \in Nodes, d \in Decls :
         (n = Producer[d] /\ (Prepare(n,d) \/ Publish(n,d))) \/ Receive(n,d)
    \/ \E n \in Nodes, S \in SUBSET Decls : Commit(n,S)
    \/ \E n \in Nodes : Crash(n) \/ Recover(n) \/ Partition(n) \/ Reconnect(n)
    \/ Heal
ChainWorkSpec == Init /\ [][ChainWorkNext]_vars
NeverChainCommitted == head["B"] # {"b", "a", "c"}
NeverDependentPublished == published \intersect {"a", "c"} = {}
=============================================================================
