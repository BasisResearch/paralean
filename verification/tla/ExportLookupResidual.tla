------------------------ MODULE ExportLookupResidual ------------------------
EXTENDS Naturals, FiniteSets

(* The F10 initializer has captured scopes 5,22 and exported scopes 5,28.
   Exact full-key lookup reserves 5 first. The remaining captured and exported
   members share a command stem and are each unique, so 22 -> 28 is forced.
   No body or literal is normalized; admission still checks stored content. *)
Groups == {"stable", "drift", "owner", "early", "ambiguous", "ambigEarly",
           "twoA", "twoB", "multi", "changed"}
Candidates == {"cStable", "cDrift", "cOwner", "cAmbig1", "cAmbig2",
               "cTwo", "cMulti1", "cMulti2", "cChanged"}
Pairs == Groups \X Candidates

FullKey == [g \in Groups |-> CASE g = "stable" -> "scope5"
                                [] g = "drift" -> "scope22"
                                [] g = "owner" -> "ownerKey"
                                [] g = "early" -> "missingEarly"
                                [] g = "ambiguous" -> "ambigKey"
                                [] g = "ambigEarly" -> "missingAmbigEarly"
                                [] g = "twoA" -> "missingTwoA"
                                [] g = "twoB" -> "missingTwoB"
                                [] g = "multi" -> "missingMulti"
                                [] OTHER -> "missingChanged"]
CandidateKey == [c \in Candidates |-> CASE c = "cStable" -> "scope5"
                                        [] c = "cDrift" -> "scope28"
                                        [] c = "cOwner" -> "ownerKey"
                                        [] c = "cAmbig1" -> "ambigKey"
                                        [] c = "cAmbig2" -> "ambigKey"
                                        [] c = "cTwo" -> "twoKey"
                                        [] c = "cMulti1" -> "multiKey1"
                                        [] c = "cMulti2" -> "multiKey2"
                                        [] OTHER -> "changedKey"]
Stem == [g \in Groups |-> CASE g \in {"stable", "drift"} -> "f10Command"
                             [] g \in {"owner", "early"} -> "earlyCommand"
                             [] g \in {"ambiguous", "ambigEarly"} -> "ambigCommand"
                             [] g \in {"twoA", "twoB"} -> "twoCommand"
                             [] g = "multi" -> "multiCommand"
                             [] OTHER -> "changedCommand"]
CandidateStem == [c \in Candidates |-> CASE c \in {"cStable", "cDrift"} -> "f10Command"
                                              [] c = "cOwner" -> "earlyCommand"
                                              [] c \in {"cAmbig1", "cAmbig2"} -> "ambigCommand"
                                              [] c = "cTwo" -> "twoCommand"
                                              [] c \in {"cMulti1", "cMulti2"} -> "multiCommand"
                                              [] OTHER -> "changedCommand"]
Stored == [g \in Groups |-> CASE g = "stable" -> "S"
                               [] g = "drift" -> "D"
                               [] g = "owner" -> "differentFromExport"
                               [] g = "early" -> "E"
                               [] g \in {"ambiguous", "ambigEarly"} -> "A"
                               [] g \in {"twoA", "twoB"} -> "T"
                               [] g = "multi" -> "M"
                               [] OTHER -> "originalName"]
Body == [c \in Candidates |-> CASE c = "cStable" -> "S"
                                  [] c = "cDrift" -> "D"
                                  [] c = "cOwner" -> "E"
                                  [] c \in {"cAmbig1", "cAmbig2"} -> "A"
                                  [] c = "cTwo" -> "T"
                                  [] c \in {"cMulti1", "cMulti2"} -> "M"
                                  [] OTHER -> "differentName"]

FullMatches(g) == {c \in Candidates : CandidateKey[c] = FullKey[g]}
StemMatches(g) == {c \in Candidates : CandidateStem[c] = Stem[g]}
ResidualCaptures(g) == {h \in Groups : FullMatches(h) = {} /\ Stem[h] = Stem[g]}

VARIABLES phase, attempted, accepted, rejected
vars == <<phase, attempted, accepted, rejected>>
Init == /\ phase = "exact"
        /\ attempted = {}
        /\ accepted = {}
        /\ rejected = {}
Unused(c) == \A g \in Groups : <<g, c>> \notin accepted
(* Every exported full-key candidate is reserved, even if its owner has an
   ambiguous key or fails the exact body check. The production prepass makes
   the same reservation before it chooses any residual candidate. *)
FullClaimed(c) == \E h \in Groups : c \in FullMatches(h)
UnusedStem(g) == {c \in StemMatches(g) : Unused(c) /\ ~FullClaimed(c)}
ExactDone == \A g \in Groups : \A c \in FullMatches(g) : <<g, c>> \in attempted

ExactSuccess(g, c) ==
  /\ phase = "exact"
  /\ <<g, c>> \in Pairs \ attempted
  /\ c \in FullMatches(g)
  /\ Cardinality(FullMatches(g)) = 1
  /\ Unused(c)
  /\ Body[c] = Stored[g]
  /\ attempted' = attempted \cup {<<g, c>>}
  /\ accepted' = accepted \cup {<<g, c>>}
  /\ UNCHANGED <<phase, rejected>>

ExactReject(g, c) ==
  /\ phase = "exact"
  /\ <<g, c>> \in Pairs \ attempted
  /\ c \in FullMatches(g)
  /\ Cardinality(FullMatches(g)) # 1 \/ ~Unused(c) \/ Body[c] # Stored[g]
  /\ attempted' = attempted \cup {<<g, c>>}
  /\ rejected' = rejected \cup {<<g, c>>}
  /\ UNCHANGED <<phase, accepted>>

Advance == /\ phase = "exact"
           /\ ExactDone
           /\ phase' = "residual"
           /\ UNCHANGED <<attempted, accepted, rejected>>

ResidualSuccess(g, c) ==
  /\ phase = "residual"
  /\ <<g, c>> \in Pairs \ attempted
  /\ FullMatches(g) = {}
  /\ c \in UnusedStem(g)
  /\ Cardinality(ResidualCaptures(g)) = 1
  /\ Cardinality(UnusedStem(g)) = 1
  /\ Body[c] = Stored[g]
  /\ attempted' = attempted \cup {<<g, c>>}
  /\ accepted' = accepted \cup {<<g, c>>}
  /\ UNCHANGED <<phase, rejected>>

ResidualReject(g, c) ==
  /\ phase = "residual"
  /\ <<g, c>> \in Pairs \ attempted
  /\ FullMatches(g) = {}
  /\ c \in StemMatches(g)
  /\ ~Unused(c) \/ Cardinality(ResidualCaptures(g)) # 1
       \/ Cardinality(UnusedStem(g)) # 1 \/ Body[c] # Stored[g]
  /\ attempted' = attempted \cup {<<g, c>>}
  /\ rejected' = rejected \cup {<<g, c>>}
  /\ UNCHANGED <<phase, accepted>>

Next == Advance \/
  (\E g \in Groups, c \in Candidates :
    ExactSuccess(g, c) \/ ExactReject(g, c) \/
    ResidualSuccess(g, c) \/ ResidualReject(g, c))
Spec == Init /\ [][Next]_vars

TypeOK == /\ phase \in {"exact", "residual"}
          /\ attempted \subseteq Pairs
          /\ accepted \subseteq attempted
          /\ rejected \subseteq attempted
          /\ accepted \cap rejected = {}
AcceptedExact == \A g \in Groups, c \in Candidates :
  <<g, c>> \in accepted => Body[c] = Stored[g]
NoExactCandidateStolen == \A g \in Groups, c \in Candidates :
  <<g, c>> \in accepted /\ FullMatches(g) = {} =>
    ~FullClaimed(c)
NoReuse == \A g1, g2 \in Groups, c \in Candidates :
  <<g1, c>> \in accepted /\ <<g2, c>> \in accepted => g1 = g2
NoTwoAccepted == \A g \in {"twoA", "twoB"}, c \in Candidates :
  <<g, c>> \notin accepted
NoMultiAccepted == \A c \in Candidates : <<"multi", c>> \notin accepted
NoAmbiguousAccepted == \A c \in Candidates : <<"ambiguous", c>> \notin accepted

NeverDriftAccepted == <<"drift", "cDrift">> \notin accepted
NeverOwnerRejected == <<"owner", "cOwner">> \notin rejected
NeverEarlyRejected == <<"early", "cOwner">> \notin rejected
NeverAmbiguousRejected == <<"ambiguous", "cAmbig1">> \notin rejected
NeverAmbigEarlyRejected == <<"ambigEarly", "cAmbig1">> \notin rejected
NeverTwoRejected == <<"twoA", "cTwo">> \notin rejected
NeverMultiRejected == <<"multi", "cMulti1">> \notin rejected
NeverChangedRejected == <<"changed", "cChanged">> \notin rejected
=============================================================================
