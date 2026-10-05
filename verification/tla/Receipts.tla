------------------------------ MODULE Receipts ------------------------------
EXTENDS FiniteSets

(* Staging gated by a trusted validator receipt, with Byzantine workers.
   No worker evaluates validity: Prepare checks only that dependencies are
   observed published and that the worker holds a receipt for exactly that
   group (the guard). A trusted validator signs a receipt only for a valid
   group whose dependencies are already published. Publish requires the group
   to be staged by that worker, as base publish does.

   Correspondence with Paralean.PublicationReceipts: Prepare here is the Lean
   UntrustedPrepare (base prepare without `valid d`) conjoined with Guard (a
   newly staged group needs a held verified receipt). Publish is base publish.
   The Lean HeldReceipt reads the shared transport (`flight`); here receipts
   are held per worker and lost on crash, which only restricts the guard. *)
CONSTANTS Workers, Groups, Valid, Deps

VARIABLES published, pending, receipts, held
vars == <<published, pending, receipts, held>>

TypeOK ==
  /\ published \subseteq Groups
  /\ receipts \subseteq Groups
  /\ pending \in [Workers -> SUBSET Groups]
  /\ held \in [Workers -> SUBSET Groups]

Init ==
  /\ published = {}
  /\ receipts = {}
  /\ pending = [w \in Workers |-> {}]
  /\ held = [w \in Workers |-> {}]

(* Byzantine staging: structural checks only, no validity evaluation.
   The receipt guard is the only check that depends on validity. *)
Prepare(w, g) ==
  /\ Deps[g] \subseteq published
  /\ g \in held[w]
  /\ pending' = [pending EXCEPT ![w] = @ \cup {g}]
  /\ UNCHANGED <<published, receipts, held>>

(* Trusted validator: the only place validity is evaluated. *)
Issue(g) ==
  /\ g \in Valid
  /\ Deps[g] \subseteq published
  /\ receipts' = receipts \cup {g}
  /\ UNCHANGED <<published, pending, held>>

Deliver(w, g) ==
  /\ g \in receipts
  /\ held' = [held EXCEPT ![w] = @ \cup {g}]
  /\ UNCHANGED <<published, pending, receipts>>

Publish(w, g) ==
  /\ g \in pending[w]
  /\ published' = published \cup {g}
  /\ pending' = [pending EXCEPT ![w] = @ \ {g}]
  /\ UNCHANGED <<receipts, held>>

Crash(w) ==
  /\ pending' = [pending EXCEPT ![w] = {}]
  /\ held' = [held EXCEPT ![w] = {}]
  /\ UNCHANGED <<published, receipts>>

Next ==
  \/ \E w \in Workers, g \in Groups : Prepare(w, g) \/ Deliver(w, g) \/ Publish(w, g)
  \/ \E g \in Groups : Issue(g)
  \/ \E w \in Workers : Crash(w)

Spec == Init /\ [][Next]_vars

PublishedValid == published \subseteq Valid
PublishedReceipted == published \subseteq receipts
StagedReceipted == \A w \in Workers : pending[w] \subseteq receipts
StagedValid == \A w \in Workers : pending[w] \subseteq Valid
DepsClosed == \A g \in published : Deps[g] \subseteq published

CaseDeps == [g \in Groups |-> IF g = "b" THEN {"a"} ELSE {}]

(* Reachability witnesses: their violation shows the good runs exist. *)
NeverValidPublished == published \cap Valid = {}
NeverDependentPublished == "b" \notin published
=============================================================================
