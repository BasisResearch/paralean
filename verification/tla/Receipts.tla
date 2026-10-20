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
   are held per worker and lost on crash, which only restricts the guard.

   Anti-entropy (W2 A-2). `published` is the issuing deployment's store, whose
   controller signed every job and alone may cancel a request (`cancelled`;
   one request per group here). A cancellation commits before publication or
   not at all: Cancel requires an unpublished group, and Publish (T1) reads it
   in the same transaction. RelayReceive is T9 at the issuing deployment: a
   Byzantine peer may serve any receipted group with a self-signed writer
   certificate at any time, so only the receiver's own guards stand between a
   cancelled request and publication. `remote` is another deployment's store,
   filled by RemoteReceive (T9 there) from any relay: its dependency guard
   reads its own published set, never the issuer's. *)
CONSTANTS Workers, Groups, Valid, Deps

VARIABLES published, pending, receipts, held, cancelled, remote
vars == <<published, pending, receipts, held, cancelled, remote>>

TypeOK ==
  /\ published \subseteq Groups
  /\ receipts \subseteq Groups
  /\ pending \in [Workers -> SUBSET Groups]
  /\ held \in [Workers -> SUBSET Groups]
  /\ cancelled \subseteq Groups
  /\ remote \subseteq Groups

Init ==
  /\ published = {}
  /\ receipts = {}
  /\ pending = [w \in Workers |-> {}]
  /\ held = [w \in Workers |-> {}]
  /\ cancelled = {}
  /\ remote = {}

(* Byzantine staging: structural checks only, no validity evaluation.
   The receipt guard is the only check that depends on validity. *)
Prepare(w, g) ==
  /\ Deps[g] \subseteq published
  /\ g \in held[w]
  /\ pending' = [pending EXCEPT ![w] = @ \cup {g}]
  /\ UNCHANGED <<published, receipts, held, cancelled, remote>>

(* Trusted validator: the only place validity is evaluated. *)
Issue(g) ==
  /\ g \in Valid
  /\ Deps[g] \subseteq published
  /\ receipts' = receipts \cup {g}
  /\ UNCHANGED <<published, pending, held, cancelled, remote>>

Deliver(w, g) ==
  /\ g \in receipts
  /\ held' = [held EXCEPT ![w] = @ \cup {g}]
  /\ UNCHANGED <<published, pending, receipts, cancelled, remote>>

Publish(w, g) ==
  /\ g \in pending[w]
  /\ g \notin cancelled
  /\ published' = published \cup {g}
  /\ pending' = [pending EXCEPT ![w] = @ \ {g}]
  /\ UNCHANGED <<receipts, held, cancelled, remote>>

(* J3 at the issuing deployment. Cancelling a published request leaves the
   monotone published set unchanged, so only unpublished requests matter. *)
Cancel(g) ==
  /\ g \notin published
  /\ cancelled' = cancelled \cup {g}
  /\ UNCHANGED <<published, pending, receipts, held, remote>>

(* T9 at the issuing deployment: the receipt passes the staging rule and the
   transaction reads this deployment's cancellation and dependency markers. *)
RelayReceive(g) ==
  /\ g \in receipts
  /\ g \notin cancelled
  /\ Deps[g] \subseteq published
  /\ published' = published \cup {g}
  /\ UNCHANGED <<pending, receipts, held, cancelled, remote>>

(* T9 at another deployment, which cannot read the issuer's cancellations. *)
RemoteReceive(g) ==
  /\ g \in receipts
  /\ Deps[g] \subseteq remote
  /\ remote' = remote \cup {g}
  /\ UNCHANGED <<published, pending, receipts, held, cancelled>>

Crash(w) ==
  /\ pending' = [pending EXCEPT ![w] = {}]
  /\ held' = [held EXCEPT ![w] = {}]
  /\ UNCHANGED <<published, receipts, cancelled, remote>>

Next ==
  \/ \E w \in Workers, g \in Groups : Prepare(w, g) \/ Deliver(w, g) \/ Publish(w, g)
  \/ \E g \in Groups : Issue(g) \/ Cancel(g) \/ RelayReceive(g) \/ RemoteReceive(g)
  \/ \E w \in Workers : Crash(w)

Spec == Init /\ [][Next]_vars

PublishedValid == published \subseteq Valid
PublishedReceipted == published \subseteq receipts
StagedReceipted == \A w \in Workers : pending[w] \subseteq receipts
StagedValid == \A w \in Workers : pending[w] \subseteq Valid
DepsClosed == \A g \in published : Deps[g] \subseteq published
CancelledUnpublished == published \cap cancelled = {}
RemoteValid == remote \subseteq Valid
RemoteDepsClosed == \A g \in remote : Deps[g] \subseteq remote

CaseDeps == [g \in Groups |-> IF g = "b" THEN {"a"} ELSE {}]

(* Reachability witnesses: their violation shows the good runs exist. *)
NeverValidPublished == published \cap Valid = {}
NeverDependentPublished == "b" \notin published
NeverCancelled == cancelled = {}
NeverRemoteDependentReceived == "b" \notin remote
=============================================================================
