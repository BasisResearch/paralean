-------------------------- MODULE ReplayIdentity --------------------------
EXTENDS Naturals, FiniteSets

(* A replay context is chosen before elaboration. A generated name literal is
   an observable part of the resulting kernel term. The original module and a
   synthetic replay module therefore produce different bytes for an initializer
   or a quotation, even if their generated declarations are otherwise scoped. *)
Groups == {"literal", "ordinary"}
Contexts == {"original", "synthetic"}
Pairs == Groups \X Contexts

Stored == [g \in Groups |-> IF g = "literal" THEN "originalName" ELSE "fixed"]
Produced(g, c) ==
  IF g = "literal" /\ c = "synthetic" THEN "syntheticName" ELSE Stored[g]

VARIABLES attempted, accepted, rejected
vars == <<attempted, accepted, rejected>>

Init == /\ attempted = {}
        /\ accepted = {}
        /\ rejected = {}

(* Context selection is unrestricted. Success requires exact stored content,
   rather than equality after erasing or renaming a term-level Name literal. *)
ReplayAccept(g, c) ==
  /\ <<g, c>> \in Pairs \ attempted
  /\ Produced(g, c) = Stored[g]
  /\ attempted' = attempted \cup {<<g, c>>}
  /\ accepted' = accepted \cup {<<g, c>>}
  /\ UNCHANGED rejected

ReplayReject(g, c) ==
  /\ <<g, c>> \in Pairs \ attempted
  /\ Produced(g, c) # Stored[g]
  /\ attempted' = attempted \cup {<<g, c>>}
  /\ rejected' = rejected \cup {<<g, c>>}
  /\ UNCHANGED accepted

Next == \E g \in Groups, c \in Contexts : ReplayAccept(g, c) \/ ReplayReject(g, c)
Spec == Init /\ [][Next]_vars

TypeOK == /\ attempted \subseteq Pairs
          /\ accepted \subseteq attempted
          /\ rejected \subseteq attempted
          /\ accepted \cap rejected = {}

AcceptedExact == \A g \in Groups, c \in Contexts :
  <<g, c>> \in accepted => Produced(g, c) = Stored[g]
RejectedMismatch == \A g \in Groups, c \in Contexts :
  <<g, c>> \in rejected => Produced(g, c) # Stored[g]

(* Coverage witnesses: the original context can replay the sensitive group;
   synthetic context is rejected there, but succeeds for an ordinary group. *)
NeverOriginalAccepted == <<"literal", "original">> \notin accepted
NeverSyntheticRejected == <<"literal", "synthetic">> \notin rejected
NeverOrdinarySyntheticAccepted == <<"ordinary", "synthetic">> \notin accepted

LiteralDistinct == Produced("literal", "original") # Produced("literal", "synthetic")
=============================================================================
