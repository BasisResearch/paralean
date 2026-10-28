--------------------------- MODULE ExportLookup ---------------------------
EXTENDS Naturals, FiniteSets

(* Captured initializer members occur in source order ref, trace, option.
   Exported .olean constNames can instead order them trace, option, ref.
   Their raw hygiene contexts retain a command discriminator and scope; only
   the source module prefix is rebased before key comparison. *)
Groups == {"ref", "trace", "option", "literal", "ambiguous", "duplicate"}
Candidates == {"eRef", "eTrace", "eOption", "eChanged", "eDup1", "eDup2"}
Pairs == Groups \X Candidates

CapturedKey == [g \in Groups |-> CASE g = "ref" -> "kRef"
                                    [] g = "trace" -> "kTrace"
                                    [] g = "option" -> "kOption"
                                    [] g = "literal" -> "kLiteral"
                                    [] g = "duplicate" -> "kRef"
                                    [] OTHER -> "kDup"]
CandidateKey == [c \in Candidates |-> CASE c = "eRef" -> "kRef"
                                        [] c = "eTrace" -> "kTrace"
                                        [] c = "eOption" -> "kOption"
                                        [] c = "eChanged" -> "kLiteral"
                                        [] OTHER -> "kDup"]
Stored == [g \in Groups |-> CASE g = "ref" -> "IORef"
                                [] g = "trace" -> "Trace"
                                [] g = "option" -> "Option"
                                [] g = "literal" -> "originalName"
                                [] g = "duplicate" -> "IORef"
                                [] OTHER -> "SameBody"]
Body == [c \in Candidates |-> CASE c = "eRef" -> "IORef"
                                   [] c = "eTrace" -> "Trace"
                                   [] c = "eOption" -> "Option"
                                   [] c = "eChanged" -> "changedName"
                                   [] OTHER -> "SameBody"]

Matches(g) == {c \in Candidates : CandidateKey[c] = CapturedKey[g]}

(* A positional queue associates ref with trace and trace with option. *)
Positional == [g \in Groups |-> CASE g = "ref" -> "eTrace"
                                  [] g = "trace" -> "eOption"
                                  [] g = "option" -> "eRef"
                                  [] g = "literal" -> "eChanged"
                                  [] g = "duplicate" -> "eRef"
                                  [] OTHER -> "eDup1"]
Match(g, c) == CandidateKey[c] = CapturedKey[g]

VARIABLES attempted, accepted, rejected
vars == <<attempted, accepted, rejected>>
Init == /\ attempted = {}
        /\ accepted = {}
        /\ rejected = {}

Unused(c) == \A g \in Groups : <<g, c>> \notin accepted

CheckSuccess(g, c) ==
  /\ <<g, c>> \in Pairs \ attempted
  /\ Match(g, c)
  /\ Cardinality(Matches(g)) = 1
  /\ Unused(c)
  /\ Body[c] = Stored[g]
  /\ attempted' = attempted \cup {<<g, c>>}
  /\ accepted' = accepted \cup {<<g, c>>}
  /\ UNCHANGED rejected

CheckReject(g, c) ==
  /\ <<g, c>> \in Pairs \ attempted
  /\ Match(g, c)
  /\ Cardinality(Matches(g)) # 1 \/ ~Unused(c) \/ Body[c] # Stored[g]
  /\ attempted' = attempted \cup {<<g, c>>}
  /\ rejected' = rejected \cup {<<g, c>>}
  /\ UNCHANGED accepted

Next == \E g \in Groups, c \in Candidates : CheckSuccess(g, c) \/ CheckReject(g, c)
Spec == Init /\ [][Next]_vars

TypeOK == /\ attempted \subseteq Pairs
          /\ accepted \subseteq attempted
          /\ rejected \subseteq attempted
          /\ accepted \cap rejected = {}
AttemptedKey == \A g \in Groups, c \in Candidates :
  <<g, c>> \in attempted => CandidateKey[c] = CapturedKey[g]
AcceptedUnique == \A g \in Groups, c \in Candidates :
  <<g, c>> \in accepted => Cardinality(Matches(g)) = 1
AcceptedNotReused == \A g1, g2 \in Groups, c \in Candidates :
  <<g1, c>> \in accepted /\ <<g2, c>> \in accepted => g1 = g2
AcceptedExact == \A g \in Groups, c \in Candidates :
  <<g, c>> \in accepted => Body[c] = Stored[g]

NeverRefAccepted == <<"ref", "eRef">> \notin accepted
NeverTraceAccepted == <<"trace", "eTrace">> \notin accepted
NeverOptionAccepted == <<"option", "eOption">> \notin accepted
NeverLiteralRejected == <<"literal", "eChanged">> \notin rejected
NeverAmbiguousRejected == <<"ambiguous", "eDup1">> \notin rejected
NeverReusedRejected == <<"duplicate", "eRef">> \notin rejected
=============================================================================
