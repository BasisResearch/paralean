-------------------------- MODULE StorePositions --------------------------
EXTENDS FiniteSets, Naturals

(* One group may have several certified placements. A deletion names a marker
   ID, never a registry revision. Local certificates are separate from foreign
   evidence and are issued only after that replica has the acknowledged bytes.
   Receiving evidence alone cannot make a position visible. *)
CONSTANTS Replicas, Groups, Positions, Deletes, GroupOf, Parent, Stamp,
          Author, Target, DelStamp, DelAuthor, NameOf, LineageKey,
          PosRank, GroupRank, UseForeignEvidence, GroupWideDelete, SkipMoveGuard

Root == "start"
None == "none"
CaseGroupOf == [p \in Positions |-> IF p = "p3" THEN "h" ELSE "g"]
CaseParent == [p \in Positions |-> IF p = "p3" THEN "p1" ELSE Root]
CaseStamp == [p \in Positions |-> IF p = "p1" THEN 1 ELSE IF p = "p3" THEN 2 ELSE 3]
CaseAuthor == [p \in Positions |-> IF p = "p3" THEN "b" ELSE "a"]
CaseTarget == [d \in Deletes |-> IF d = "d1" THEN "p1" ELSE "p2"]
CaseDelStamp == [d \in Deletes |-> IF d = "d1" THEN 2 ELSE 4]
CaseDelAuthor == [d \in Deletes |-> "a"]
CaseNameOf == [g \in Groups |-> "x"]
CaseLineageKey == [g \in Groups |-> IF g = "g" THEN 1 ELSE 2]
CasePosRank == [p \in Positions |-> IF p = "p1" THEN 1 ELSE IF p = "p2" THEN 2 ELSE 3]
CaseGroupRank == [g \in Groups |-> IF g = "g" THEN 1 ELSE 2]

ASSUME /\ GroupOf \in [Positions -> Groups]
       /\ Parent \in [Positions -> Positions \cup {Root}]
       /\ Stamp \in [Positions -> Nat]
       /\ Author \in [Positions -> Replicas]
       /\ Target \in [Deletes -> Positions]
       /\ DelStamp \in [Deletes -> Nat]
       /\ DelAuthor \in [Deletes -> Replicas]
       /\ NameOf \in [Groups -> {"x", "y"}]
       /\ LineageKey \in [Groups -> Nat]
       /\ PosRank \in [Positions -> Nat]
       /\ GroupRank \in [Groups -> Nat]
       /\ \A d \in Deletes : DelStamp[d] > Stamp[Target[d]]
       /\ \A p \in Positions : Parent[p] # Root => Stamp[p] > Stamp[Parent[p]]

VARIABLES stagedP, ackP, storedP, certP, foreignP,
          ackD, storedD, certD, foreignD, registry, checkpoint
vars == <<stagedP, ackP, storedP, certP, foreignP,
          ackD, storedD, certD, foreignD, registry, checkpoint>>

PublishedP == UNION {certP[r] : r \in Replicas}
PublishedD == UNION {certD[r] : r \in Replicas}
KnownP(r) == IF UseForeignEvidence THEN certP[r] \cup foreignP[r] ELSE certP[r]
KnownD(r) == IF UseForeignEvidence THEN certD[r] \cup foreignD[r] ELSE certD[r]
MoveEvidence(p) ==
  \E q \in PublishedP, d \in PublishedD :
    GroupOf[q] = GroupOf[p] /\ Target[d] = q /\ Stamp[q] < Stamp[p]
FirstPosition(p) == ~\E q \in PublishedP : GroupOf[q] = GroupOf[p]

Init ==
  /\ stagedP = {}
  /\ ackP = [r \in Replicas |-> {}]
  /\ storedP = [r \in Replicas |-> {}]
  /\ certP = [r \in Replicas |-> {}]
  /\ foreignP = [r \in Replicas |-> {}]
  /\ ackD = [r \in Replicas |-> {}]
  /\ storedD = [r \in Replicas |-> {}]
  /\ certD = [r \in Replicas |-> {}]
  /\ foreignD = [r \in Replicas |-> {}]
  /\ registry = [r \in Replicas |-> {}]
  /\ checkpoint = [r \in Replicas |-> {}]

Stage(p) ==
  /\ p \notin stagedP
  /\ Parent[p] = Root \/ Parent[p] \in PublishedP
  /\ stagedP' = stagedP \cup {p}
  /\ UNCHANGED <<ackP, storedP, certP, foreignP, ackD, storedD,
                 certD, foreignD, registry, checkpoint>>

PutP(r, p) ==
  /\ p \in stagedP /\ p \notin ackP[r]
  /\ r = Author[p] \/ p \in foreignP[r]
  /\ ackP' = [ackP EXCEPT ![r] = @ \cup {p}]
  /\ UNCHANGED <<stagedP, storedP, certP, foreignP, ackD, storedD,
                 certD, foreignD, registry, checkpoint>>

PublishP(r, p) ==
  /\ r = Author[p] /\ p \in (ackP[r] \ certP[r])
  /\ FirstPosition(p) \/ SkipMoveGuard \/ MoveEvidence(p)
  /\ storedP' = [storedP EXCEPT ![r] = @ \cup {p}]
  /\ certP' = [certP EXCEPT ![r] = @ \cup {p}]
  /\ registry' = [registry EXCEPT ![r] = @ \cup {GroupOf[p]}]
  /\ UNCHANGED <<stagedP, ackP, foreignP, ackD, storedD,
                 certD, foreignD, checkpoint>>

ReceiveEvidenceP(r, p) ==
  /\ p \in (PublishedP \ foreignP[r])
  /\ foreignP' = [foreignP EXCEPT ![r] = @ \cup {p}]
  /\ UNCHANGED <<stagedP, ackP, storedP, certP, ackD, storedD,
                 certD, foreignD, registry, checkpoint>>

ReceiveP(r, p) ==
  /\ p \in (foreignP[r] \ certP[r]) /\ p \in ackP[r]
  /\ storedP' = [storedP EXCEPT ![r] = @ \cup {p}]
  /\ certP' = [certP EXCEPT ![r] = @ \cup {p}]
  /\ registry' = [registry EXCEPT ![r] = @ \cup {GroupOf[p]}]
  /\ UNCHANGED <<stagedP, ackP, foreignP, ackD, storedD,
                 certD, foreignD, checkpoint>>

PutD(r, d) ==
  /\ Target[d] \in PublishedP /\ d \notin ackD[r]
  /\ r = DelAuthor[d] \/ d \in foreignD[r]
  /\ ackD' = [ackD EXCEPT ![r] = @ \cup {d}]
  /\ UNCHANGED <<stagedP, ackP, storedP, certP, foreignP, storedD,
                 certD, foreignD, registry, checkpoint>>

Delete(r, d) ==
  /\ r = DelAuthor[d] /\ d \in (ackD[r] \ certD[r])
  /\ Target[d] \in certP[r]
  /\ r = Author[Target[d]]
  /\ storedD' = [storedD EXCEPT ![r] = @ \cup {d}]
  /\ certD' = [certD EXCEPT ![r] = @ \cup {d}]
  /\ UNCHANGED <<stagedP, ackP, storedP, certP, foreignP, ackD,
                 foreignD, registry, checkpoint>>

ReceiveEvidenceD(r, d) ==
  /\ d \in (PublishedD \ foreignD[r])
  /\ foreignD' = [foreignD EXCEPT ![r] = @ \cup {d}]
  /\ UNCHANGED <<stagedP, ackP, storedP, certP, foreignP, ackD,
                 storedD, certD, registry, checkpoint>>

ReceiveD(r, d) ==
  /\ d \in (foreignD[r] \ certD[r]) /\ d \in ackD[r]
  /\ Target[d] \in certP[r]
  /\ storedD' = [storedD EXCEPT ![r] = @ \cup {d}]
  /\ certD' = [certD EXCEPT ![r] = @ \cup {d}]
  /\ UNCHANGED <<stagedP, ackP, storedP, certP, foreignP, ackD,
                 foreignD, registry, checkpoint>>

Checkpoint(r, g) ==
  /\ g \in registry[r]
  /\ g \notin checkpoint[r]
  /\ checkpoint' = [checkpoint EXCEPT ![r] = @ \cup {g}]
  /\ UNCHANGED <<stagedP, ackP, storedP, certP, foreignP,
                 ackD, storedD, certD, foreignD, registry>>

Next ==
  \/ \E p \in Positions : Stage(p)
  \/ \E r \in Replicas, p \in Positions : PutP(r, p) \/ PublishP(r, p)
  \/ \E r \in Replicas, p \in Positions : ReceiveEvidenceP(r, p) \/ ReceiveP(r, p)
  \/ \E r \in Replicas, d \in Deletes : PutD(r, d) \/ Delete(r, d)
  \/ \E r \in Replicas, d \in Deletes : ReceiveEvidenceD(r, d) \/ ReceiveD(r, d)
  \/ \E r \in Replicas, g \in Groups : Checkpoint(r, g)

Spec == Init /\ [][Next]_vars

VisibleP(r) == {p \in KnownP(r) :
  ~\E d \in KnownD(r) : Target[d] = p \/ (GroupWideDelete /\ GroupOf[Target[d]] = GroupOf[p])}
Older(p, q) == Stamp[p] < Stamp[q] \/ (Stamp[p] = Stamp[q] /\ PosRank[p] < PosRank[q])
Chosen(r, g) ==
  LET ps == {p \in VisibleP(r) : GroupOf[p] = g}
  IN IF ps = {} THEN None ELSE CHOOSE p \in ps : \A q \in ps : p = q \/ Older(p, q)
Rendered(r) == {g \in Groups : Chosen(r, g) # None}
Winner(r, n) ==
  LET gs == {g \in Rendered(r) : NameOf[g] = n}
  IN IF gs = {} THEN None ELSE CHOOSE g \in gs :
       \A h \in gs : g = h \/ LineageKey[g] < LineageKey[h]
                            \/ (LineageKey[g] = LineageKey[h] /\ GroupRank[g] < GroupRank[h])
RenderedName(r, g) ==
  IF g \notin Rendered(r) THEN None
  ELSE IF Winner(r, NameOf[g]) = g THEN <<NameOf[g], "">>
  ELSE <<NameOf[g], g>>

TypeOK ==
  /\ stagedP \subseteq Positions
  /\ \A r \in Replicas :
       /\ ackP[r] \subseteq stagedP /\ storedP[r] \subseteq ackP[r]
       /\ certP[r] \subseteq storedP[r] /\ foreignP[r] \subseteq PublishedP
       /\ storedD[r] \subseteq ackD[r] /\ certD[r] \subseteq storedD[r]
       /\ foreignD[r] \subseteq PublishedD
       /\ registry[r] \subseteq Groups /\ checkpoint[r] \subseteq registry[r]
LocalCertOnly == \A r \in Replicas : KnownP(r) \subseteq certP[r] /\ KnownD(r) \subseteq certD[r]
TombstoneNeutral == \A r \in Replicas : registry[r] = {GroupOf[p] : p \in certP[r]}
MoveCertified == \A p \in PublishedP :
  (\E q \in PublishedP : GroupOf[q] = GroupOf[p] /\ Stamp[q] < Stamp[p]) => MoveEvidence(p)
(* A tombstone never removes a group from a checkpoint or registry. *)
CheckpointKept == \A r \in Replicas : checkpoint[r] \subseteq registry[r]
PositionExact == \A r \in Replicas : \A p \in certP[r] :
  (\E d \in certD[r] : Target[d] = p) => p \notin VisibleP(r)
ReinsertVisible == \A r \in Replicas : \A p \in certP[r] :
  (\A d \in certD[r] : Target[d] # p) => p \in VisibleP(r)
NoFreshCollision == \A r \in Replicas : \A g, h \in Rendered(r) :
  g # h => RenderedName(r, g) # RenderedName(r, h)
LineageNameStable == \A r \in Replicas : \A g \in Rendered(r) :
  Winner(r, NameOf[g]) = g => RenderedName(r, g) = <<NameOf[g], "">>
Converged == \A a, b \in Replicas :
  certP[a] = certP[b] /\ certD[a] = certD[b] =>
    \A g \in Groups : Chosen(a, g) = Chosen(b, g) /\ RenderedName(a, g) = RenderedName(b, g)

=============================================================================
