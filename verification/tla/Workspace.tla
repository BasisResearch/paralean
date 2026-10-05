----------------------------- MODULE Workspace -----------------------------
EXTENDS FiniteSets, Naturals, Sequences

(* Transparent workspaces: each file is a declaration-level RGA. A publication
   carries its file, an anchor, a Lamport timestamp 1 + max known ts, and its
   author. Publications are gossiped in arbitrary order; delivery is causal
   only for the anchor and the revision ancestor. Revisions (Rev) supersede
   their ancestors; a tombstone (Tomb) is a revision that deletes: it
   supersedes its ancestors and is never rendered itself.
   Positions: anchors are lineage roots (declarations with no ancestor) or the
   file start. Roots are ordered by anchor-tree preorder, siblings newest
   (ts, author) first. A live head renders at its lineage root's position;
   heads sharing a root sort by their own key, oldest first. Each agent's
   rendered file is a pure function of its known set.
   Names: a declaration declares its primary name Name[d] and the extra names
   Also[d]; a revision revises its ancestor for the primary name only, so a
   two-name declaration can be revised for one of its names. Among live heads
   declaring a name, the one with the least lineage key (the key of its
   lineage root, then its own key) keeps the name; the others get the
   deterministic fresh name <<name, id>>. A superseded declaration is not
   live, so it holds none of its names.
   Declaration IDs are pre-assigned to authors, files and names so
   publications are bounded and the system quiesces. Agent c publishes
   nothing: it is a third replica that only receives. doc is stored state (so
   arrival-order rendering is a one-line mutation); intent, firstSeen and
   rendered (every declaration an agent has ever rendered) are ghost history;
   firstSeen is read only by mutation and rendered only by a witness. *)

CONSTANTS Agents, Decls, Files, Names, Author, File, Name, Also, Rev, Tomb, Rank

Root == "start"
None == "none"

CaseDecls == {"a1", "a2", "a3", "b1", "b2"}
CaseAuthor == [d \in CaseDecls |-> IF d \in {"a1", "a2", "a3"} THEN "a" ELSE "b"]
CaseFile == [d \in CaseDecls |-> IF d \in {"a2", "b2"} THEN "G" ELSE "F"]
CaseName == [d \in CaseDecls |-> IF d \in {"a2", "b2"} THEN "bar" ELSE "foo"]
(* a1 also declares bar; its revision a3 revises it for foo only. *)
CaseAlso == [d \in CaseDecls |-> IF d = "a1" THEN {"bar"} ELSE {}]
(* a3 revises a1 (a1 and b1 collide on foo); b2 deletes a2. *)
CaseRev == [d \in CaseDecls |-> IF d = "a3" THEN "a1" ELSE IF d = "b2" THEN "a2" ELSE None]
CaseTomb == [d \in CaseDecls |-> d = "b2"]
CaseRank == [x \in {"a", "b", "c"} |-> IF x = "a" THEN 1 ELSE IF x = "b" THEN 2 ELSE 3]

ASSUME /\ Author \in [Decls -> Agents]
       /\ File \in [Decls -> Files]
       /\ Name \in [Decls -> Names]
       /\ Also \in [Decls -> SUBSET Names]
       /\ Rev \in [Decls -> Decls \cup {None}]
       /\ Tomb \in [Decls -> BOOLEAN]
       /\ \A d \in Decls : Rev[d] # None => Name[Rev[d]] = Name[d] /\ File[Rev[d]] = File[d]
       /\ \A d \in Decls : Tomb[d] => Rev[d] # None
       /\ Rank \in [Agents -> Nat]

VARIABLES ts, anchor, known, doc, intent, firstSeen, rendered
vars == <<ts, anchor, known, doc, intent, firstSeen, rendered>>

MaxTs == Cardinality(Decls)

(* Key order: newer (ts, author) first. Total on published declarations
   because each author's timestamps strictly increase. *)
Newer(d, e) == \/ ts[d] > ts[e]
               \/ ts[d] = ts[e] /\ Rank[Author[d]] > Rank[Author[e]]
Oldest(S) == CHOOSE m \in S : \A e \in S \ {m} : Newer(e, m)

(* Revision ancestry (transitive) and lineage root (least key). *)
RECURSIVE Anc(_)
Anc(d) == IF Rev[d] = None THEN {} ELSE {Rev[d]} \cup Anc(Rev[d])
LRoot(d) == Oldest({d} \cup Anc(d))

Live(K, d) == d \in K /\ ~Tomb[d] /\ ~\E e \in K : d \in Anc(e)
LiveIn(K, f) == {d \in K : File[d] = f /\ Live(K, d)}

Children(K, p) == {d \in K : anchor[d] = p}
Top(S) == CHOOSE m \in S : \A e \in S \ {m} : Newer(m, e)

(* Preorder of the anchor forest rooted at the siblings S. *)
RECURSIVE Pre(_, _)
Pre(K, S) == IF S = {} THEN <<>>
             ELSE LET m == Top(S)
                  IN <<m>> \o Pre(K, Children(K, m)) \o Pre(K, S \ {m})

(* Lineage roots of file f known in K, in position order. *)
Positions(K, f) ==
    LET R == {d \in K : File[d] = f /\ Rev[d] = None}
    IN Pre(R, Children(R, Root))

RECURSIVE ByKey(_)
ByKey(S) == IF S = {} THEN <<>> ELSE <<Oldest(S)>> \o ByKey(S \ {Oldest(S)})

RECURSIVE Flat(_, _, _)
Flat(K, f, P) == IF P = <<>> THEN <<>>
                 ELSE ByKey({d \in LiveIn(K, f) : LRoot(d) = Head(P)}) \o Flat(K, f, Tail(P))

Render(K, f) == Flat(K, f, Positions(K, f))
RenderAll(K) == [f \in Files |-> Render(K, f)]

Range(s) == {s[i] : i \in DOMAIN s}
Index(s, e) == CHOOSE i \in DOMAIN s : s[i] = e
Restrict(s, S) == SelectSeq(s, LAMBDA e : e \in S)
IsSubseq(s, t) == Range(s) \subseteq Range(t) /\ Restrict(t, Range(s)) = s

(* The author's render with a fresh d placed right after the lineage block
   of its anchor p (or first, for the file start). *)
AtOrAbove(K, f, e, p) ==
    p # Root /\ LET P == Positions(K, f) IN Index(P, LRoot(e)) <= Index(P, p)
Intended(K, f, p, d) ==
    LET s == Render(K, f)
    IN SelectSeq(s, LAMBDA e : AtOrAbove(K, f, e, p)) \o <<d>> \o
       SelectSeq(s, LAMBDA e : ~AtOrAbove(K, f, e, p))

(* Lamport clock: one more than every timestamp the agent knows. *)
KnownMax(K) == IF K = {} THEN 0 ELSE CHOOSE t \in {ts[d] : d \in K} : \A e \in K : ts[e] <= t
Clock(x) == 1 + KnownMax(known[x])

(* Names: live heads declaring a name; least lineage key wins. *)
NameSet(d) == {Name[d]} \cup Also[d]
Heads(K, n) == {d \in K : n \in NameSet(d) /\ Live(K, d)}
LinBefore(m, e) == \/ Newer(LRoot(e), LRoot(m))
                   \/ LRoot(e) = LRoot(m) /\ Newer(e, m)
LinMin(S) == CHOOSE m \in S : \A e \in S \ {m} : LinBefore(m, e)
Winner(x, K, n) == LinMin(Heads(K, n))
RName(x, d, n) == IF d \in Heads(known[x], n) /\ d = Winner(x, known[x], n)
                  THEN <<n, "">> ELSE <<n, d>>
LiveAll(K) == {d \in K : Live(K, d)}
(* Each rendered declaration with each name it declares. *)
Decl(K) == {p \in LiveAll(K) \X Names : p[2] \in NameSet(p[1])}
Names_(x) == [p \in Decl(known[x]) |-> RName(x, p[1], p[2])]

SeeName(x, d) == IF firstSeen[x][Name[d]] = None
                 THEN [firstSeen EXCEPT ![x][Name[d]] = d] ELSE firstSeen

(* Ghost: add what x renders after the step (doc' is already determined). *)
Rendered(x) == [rendered EXCEPT ![x] = @ \cup UNION {Range(doc'[x][f]) : f \in Files}]

Init ==
    /\ ts = [d \in Decls |-> 0]
    /\ anchor = [d \in Decls |-> None]
    /\ known = [x \in Agents |-> {}]
    /\ doc = [x \in Agents |-> [f \in Files |-> <<>>]]
    /\ intent = [d \in Decls |-> <<>>]
    /\ firstSeen = [x \in Agents |-> [n \in Names |-> None]]
    /\ rendered = [x \in Agents |-> {}]

(* Fresh declarations anchor at a known lineage root of their file; revisions
   take their root's position, so their anchor field is the file start. *)
Publish(x, d, p) ==
    /\ Author[d] = x
    /\ ts[d] = 0
    /\ Rev[d] = None \/ Rev[d] \in known[x]
    /\ IF Rev[d] = None
       THEN p \in {Root} \cup {e \in known[x] : File[e] = File[d] /\ Rev[e] = None}
       ELSE p = Root
    /\ ts' = [ts EXCEPT ![d] = Clock(x)]
    /\ anchor' = [anchor EXCEPT ![d] = p]
    /\ known' = [known EXCEPT ![x] = @ \cup {d}]
    /\ intent' = [intent EXCEPT ![d] =
                    IF Rev[d] = None THEN Intended(known[x], File[d], p, d)
                    ELSE (Render(known[x] \cup {d}, File[d]))']
    /\ doc' = [doc EXCEPT ![x] = (RenderAll(known[x]))']
    /\ firstSeen' = SeeName(x, d)
    /\ rendered' = Rendered(x)

Receive(x, d) ==
    /\ ts[d] # 0
    /\ d \notin known[x]
    /\ anchor[d] = Root \/ anchor[d] \in known[x]
    /\ Rev[d] = None \/ Rev[d] \in known[x]
    /\ known' = [known EXCEPT ![x] = @ \cup {d}]
    /\ doc' = [doc EXCEPT ![x][File[d]] = Render(known'[x], File[d])]
    /\ firstSeen' = SeeName(x, d)
    /\ rendered' = Rendered(x)
    /\ UNCHANGED <<ts, anchor, intent>>

Next ==
    \/ \E x \in Agents, d \in Decls, p \in Decls \cup {Root} : Publish(x, d, p)
    \/ \E x \in Agents, d \in Decls : Receive(x, d)

Spec == Init /\ [][Next]_vars
(* Fairness: whenever some agent can receive some publication, some receive
   eventually happens. RecvKnown is Receive's guard and known-set update; it
   leaves the derived state free, so checking it does not re-render. Every
   RecvKnown step of Next is a Receive step (a Publish adds an unpublished
   declaration). Publications are bounded, so this suffices. *)
RecvKnown ==
    \E x \in Agents, d \in Decls :
        /\ ts[d] # 0
        /\ d \notin known[x]
        /\ anchor[d] = Root \/ anchor[d] \in known[x]
        /\ Rev[d] = None \/ Rev[d] \in known[x]
        /\ known' = [known EXCEPT ![x] = @ \cup {d}]
FairSpec == Spec /\ WF_known(RecvKnown)

TypeOK ==
    /\ ts \in [Decls -> 0..MaxTs]
    /\ anchor \in [Decls -> Decls \cup {Root, None}]
    /\ known \in [Agents -> SUBSET Decls]
    /\ \A x \in Agents : known[x] \subseteq {d \in Decls : ts[d] # 0}

(* Agents knowing the same publications render byte-identical files and names. *)
SameKnownSameRender ==
    \A x, y \in Agents : x # y /\ known[x] = known[y] =>
        doc[x] = doc[y] /\ Names_(x) = Names_(y)

(* Names alone, for mutations that keep the rendered order. *)
NameAgreement ==
    \A x, y \in Agents : x # y /\ known[x] = known[y] => Names_(x) = Names_(y)

(* A rendered declaration follows the whole lineage block of its root's anchor. *)
AnchorBefore ==
    \A x \in Agents, f \in Files : \A i \in DOMAIN doc[x][f] :
        LET p == anchor[LRoot(doc[x][f][i])]
        IN p # Root =>
             \A j \in DOMAIN doc[x][f] : LRoot(doc[x][f][j]) = p => j < i

(* Superseded declarations and tombstones are never rendered. *)
NoSupersededRendered ==
    \A x \in Agents, f \in Files : \A i \in DOMAIN doc[x][f] :
        LET d == doc[x][f][i]
        IN ~Tomb[d] /\ ~\E e \in known[x] : d \in Anc(e)

(* Every known live declaration is rendered: causal receive leaves no known
   declaration invisible for want of its anchor or its lineage root. *)
RenderComplete ==
    \A x \in Agents : \A d \in LiveAll(known[x]) : d \in Range(doc[x][File[d]])

NamesUnique ==
    \A x \in Agents :
        Cardinality({RName(x, p[1], p[2]) : p \in Decl(known[x])}) = Cardinality(Decl(known[x]))

(* A name declared by some rendered declaration is kept by a rendered
   declaration: a superseded declaration never holds it. *)
NameHeld ==
    \A x \in Agents, n \in Names :
        (\E d \in LiveAll(known[x]) : n \in NameSet(d)) =>
            \E d \in LiveAll(known[x]) : n \in NameSet(d) /\ RName(x, d, n) = <<n, "">>

(* Growth never reorders: declarations rendered before and after a step keep
   their relative order. *)
RenderStable ==
    [][\A x \in Agents, f \in Files :
         IsSubseq(Restrict(doc[x][f], Range(doc'[x][f])), doc'[x][f])]_vars

(* A rendered declaration disappears only when a known revision or tombstone
   supersedes it. *)
DisappearOnlySuperseded ==
    [][\A x \in Agents, f \in Files :
         \A d \in Range(doc[x][f]) \ Range(doc'[x][f]) : \E e \in known'[x] : d \in Anc(e)]_vars

(* The author's intended render at publish time (d right after its anchor's
   lineage block) stays a subsequence of every later render, restricted to the
   declarations still rendered there. *)
IntentionPreserved ==
    [][\A x \in Agents : \A d \in known'[x] :
         IsSubseq(Restrict(intent'[d], Range(doc'[x][File[d]])), doc'[x][File[d]])]_vars

(* Revising the winner keeps the name: when an agent learns a live revision of
   the current winner, the revision wins. *)
WinnerLineageKeepsName ==
    [][\A x \in Agents, r \in Decls :
         (/\ r \in known'[x] /\ r \notin known[x]
          /\ Rev[r] # None /\ ~Tomb[r]
          /\ Rev[r] \in Heads(known[x], Name[r])
          /\ Rev[r] = Winner(x, known[x], Name[r]))
         => (RName(x, r, Name[r]))' = <<Name[r], "">>]_vars

Identical ==
    \A x, y \in Agents : doc[x] = doc[y] /\ Names_(x) = Names_(y)
EventuallyIdentical == <>[]Identical

(* Coverage witnesses: each is expected to be violated. *)
Concurrent(d, e) == d \notin Range(intent[e]) /\ e \notin Range(intent[d])
NeverConcurrentConverged ==
    ~\E d, e \in Decls :
        /\ d # e /\ ts[d] # 0 /\ ts[e] # 0
        /\ anchor[d] = anchor[e] /\ File[d] = File[e]
        /\ Author[d] # Author[e] /\ Concurrent(d, e)
        /\ {d, e} \subseteq known[Author[d]] /\ {d, e} \subseteq known[Author[e]]
        /\ doc[Author[d]][File[d]] = doc[Author[e]][File[d]]
NeverCollisionResolved ==
    ~\E x \in Agents : \E d, e \in Heads(known[x], "foo") : d # e
(* The revised collision winner keeps foo against an older-keyed loser. *)
NeverWinnerRevised ==
    ~\E x \in Agents :
        /\ {"a3", "b1"} \subseteq known[x]
        /\ Newer("a3", "b1")
        /\ RName(x, "a3", "foo") = <<"foo", "">>
(* The partial revision a3 has retired a1, and a2 holds bar. *)
NeverPartialRevisionFreed ==
    ~\E x \in Agents :
        /\ {"a1", "a2", "a3"} \subseteq known[x]
        /\ Newer("a2", "a1")
        /\ RName(x, "a2", "bar") = <<"bar", "">>
(* A tombstone has removed a declaration the same agent rendered earlier. *)
NeverDeleted ==
    ~\E x \in Agents : /\ "b2" \in known[x]
                       /\ "a2" \in rendered[x]
                       /\ Render(known[x], "G") = <<>>
=============================================================================
