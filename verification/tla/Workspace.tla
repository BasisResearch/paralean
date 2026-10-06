----------------------------- MODULE Workspace -----------------------------
EXTENDS FiniteSets, Naturals, Sequences

(* Transparent workspaces: each file is a declaration-level RGA. An author
   first stages a declaration (pending, unpublished), then publishes it. A
   record carries its file, an anchor, a Lamport timestamp from the author's
   persistent clock, its author and the anchor path of its lineage root.
   Staging anchors a fresh declaration at the file start, at a published
   lineage root the author knows, or at one of the author's own pending
   lineage roots. PublishGuard: a declaration publishes only once its anchor
   is known to the publisher, so an own pending anchor is published first.
   Publications are gossiped in arbitrary order; a record may arrive before
   its anchor. Delivery is causal only for the revision ancestor. Revisions
   (Rev) supersede their ancestors; a tombstone (Tomb) is a revision that
   deletes: it supersedes its ancestors and is never rendered itself.
   Positions: lineage roots are ordered by their carried anchor paths (the
   keys from the file start down to the root): a proper prefix first,
   otherwise the newer (ts, author) key at the first difference first. This
   is the anchor-tree preorder with siblings newest first, but it reads only
   the records an agent knows. A live head renders at its lineage root's
   position; heads sharing a root sort by their own key, oldest first. Each
   agent's rendered file is a pure function of its known (published) set; its
   pending declarations are drafts and are not rendered.
   Names: a declaration declares its primary name Name[d] and the extra names
   Also[d]; a revision revises its ancestor for the primary name only, so a
   two-name declaration can be revised for one of its names. Among live heads
   declaring a name, the one with the least lineage key (the key of its
   lineage root, then its own key) keeps the name; the others get the
   deterministic fresh name <<name, id>>. A superseded declaration is not
   live, so it holds none of its names.
   Declaration IDs are pre-assigned to authors, files and names so
   publications are bounded and the system quiesces. Agents with no
   declarations only receive. doc is stored state (so arrival-order rendering
   is a one-line mutation); intent, firstSeen and rendered (every declaration
   an agent has ever rendered) are ghost history; firstSeen is read only by
   mutation and rendered only by a witness. *)

CONSTANTS Agents, Decls, Files, Names, Author, File, Name, Also, Rev, Tomb, Rank

Root == "start"
None == "none"

CaseAuthor == [d \in Decls |-> IF d \in {"a1", "a2", "a3", "a4"} THEN "a" ELSE "b"]
CaseFile == [d \in Decls |-> IF d \in {"a2", "b2"} THEN "G" ELSE "F"]
CaseName == [d \in Decls |-> IF d \in {"a2", "b2"} THEN "bar"
                                 ELSE IF d = "a4" THEN "baz" ELSE "foo"]
(* a1 also declares bar; its revision a3 revises it for foo only. *)
CaseAlso == [d \in Decls |-> IF d = "a1" THEN {"bar"} ELSE {}]
(* a3 revises a1 (a1 and b1 collide on foo); b2 deletes a2. a4 (used by
   WorkspacePending.cfg) is a second fresh declaration of a in F, which a may
   anchor at a1 while a1 is pending. *)
CaseRev == [d \in Decls |-> IF d = "a3" THEN "a1" ELSE IF d = "b2" THEN "a2" ELSE None]
CaseTomb == [d \in Decls |-> d = "b2"]
CaseRank == [x \in {"a", "b", "c"} |-> IF x = "a" THEN 1 ELSE IF x = "b" THEN 2 ELSE 3]

(* Larger scope (WorkspaceWide.cfg): three publishing authors in one file.
   a1, b1 collide on foo; c revises b1 with c1; a2 is a second fresh
   declaration of a, which a may anchor at a1 while a1 is pending. *)
WideAuthor == [d \in Decls |-> IF d \in {"a1", "a2"} THEN "a" ELSE IF d = "b1" THEN "b" ELSE "c"]
WideFile == [d \in Decls |-> "F"]
WideName == [d \in Decls |-> IF d = "a2" THEN "bar" ELSE "foo"]
WideAlso == [d \in Decls |-> {}]
WideRev == [d \in Decls |-> IF d = "c1" THEN "b1" ELSE None]
WideTomb == [d \in Decls |-> FALSE]

ASSUME /\ Author \in [Decls -> Agents]
       /\ File \in [Decls -> Files]
       /\ Name \in [Decls -> Names]
       /\ Also \in [Decls -> SUBSET Names]
       /\ Rev \in [Decls -> Decls \cup {None}]
       /\ Tomb \in [Decls -> BOOLEAN]
       /\ \A d \in Decls : Rev[d] # None => Name[Rev[d]] = Name[d] /\ File[Rev[d]] = File[d]
       /\ \A d \in Decls : Tomb[d] => Rev[d] # None
       /\ Rank \in [Agents -> Nat]

VARIABLES ts, anchor, path, lamport, pending, known, doc, intent, firstSeen, rendered
vars == <<ts, anchor, path, lamport, pending, known, doc, intent, firstSeen, rendered>>

MaxTs == Cardinality(Decls)

(* Staged declarations carry ts # 0; published ones are known somewhere. *)
Published == UNION {known[x] : x \in Agents}
(* The author's working view: published declarations it knows and its own
   pending ones. *)
View(x) == known[x] \cup pending[x]

(* Key order: newer (ts, author) first. Total on staged declarations because
   each author's timestamps strictly increase (KeysUnique). *)
Key(d) == <<ts[d], Rank[Author[d]]>>
KeyGt(k, l) == k[1] > l[1] \/ (k[1] = l[1] /\ k[2] > l[2])
Newer(d, e) == KeyGt(Key(d), Key(e))
Oldest(S) == CHOOSE m \in S : \A e \in S \ {m} : Newer(e, m)

(* Revision ancestry (transitive) and lineage root (least key). *)
RECURSIVE Anc(_)
Anc(d) == IF Rev[d] = None THEN {} ELSE {Rev[d]} \cup Anc(Rev[d])
LRoot(d) == Oldest({d} \cup Anc(d))

Live(K, d) == d \in K /\ ~Tomb[d] /\ ~\E e \in K : d \in Anc(e)
LiveIn(K, f) == {d \in K : File[d] = f /\ Live(K, d)}

Roots(K, f) == {d \in K : File[d] = f /\ Rev[d] = None}

(* RGA order on carried anchor paths: a proper prefix first, otherwise the
   newer key at the first difference first. *)
PathBefore(p, q) ==
    LET n == IF Len(p) < Len(q) THEN Len(p) ELSE Len(q)
        D == {i \in 1..n : p[i] # q[i]}
    IN IF D = {} THEN Len(p) < Len(q)
       ELSE LET i == CHOOSE i \in D : \A j \in D : i <= j IN KeyGt(p[i], q[i])

RECURSIVE ByPath(_)
ByPath(S) == IF S = {} THEN <<>>
             ELSE LET m == CHOOSE m \in S : \A e \in S \ {m} : PathBefore(path[m], path[e])
                  IN <<m>> \o ByPath(S \ {m})

(* The anchor-tree preorder over K (siblings newest first). It reads the
   anchors of K only, so it drops a root whose anchor is not in K. It equals
   Positions when K is anchor-closed (CarriedPathAgrees). *)
Children(K, p) == {d \in K : anchor[d] = p}
Top(S) == CHOOSE m \in S : \A e \in S \ {m} : Newer(m, e)
RECURSIVE Pre(_, _)
Pre(K, S) == IF S = {} THEN <<>>
             ELSE LET m == Top(S)
                  IN <<m>> \o Pre(K, Children(K, m)) \o Pre(K, S \ {m})
TreeOrder(K, f) == LET R == Roots(K, f) IN Pre(R, Children(R, Root))

(* Lineage roots of file f known in K, in position order. Reads only the
   paths carried by the records in K. *)
Positions(K, f) == ByPath(Roots(K, f))

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

(* The author's render of its view with a fresh d placed right after the
   lineage block of its anchor p (or first, for the file start). *)
Intended(K, f, p, d) ==
    LET s == Render(K, f)
        P == Positions(K, f)
        above == IF p = Root THEN {}
                 ELSE {e \in Range(s) : Index(P, LRoot(e)) <= Index(P, p)}
    IN SelectSeq(s, LAMBDA e : e \in above) \o <<d>> \o
       SelectSeq(s, LAMBDA e : e \notin above)

(* Persistent Lamport clock: staging takes one more than the clock and every
   receive raises the clock to the received timestamp. *)
Clock(x) == 1 + lamport[x]

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
    /\ path = [d \in Decls |-> <<>>]
    /\ lamport = [x \in Agents |-> 0]
    /\ pending = [x \in Agents |-> {}]
    /\ known = [x \in Agents |-> {}]
    /\ doc = [x \in Agents |-> [f \in Files |-> <<>>]]
    /\ intent = [d \in Decls |-> <<>>]
    /\ firstSeen = [x \in Agents |-> [n \in Names |-> None]]
    /\ rendered = [x \in Agents |-> {}]

(* Staging. A fresh declaration anchors at the file start or at a lineage root
   of its file in the author's view: a published one it knows or one of its
   own pending ones. A revision takes its root's position, so its anchor field
   is the file start and it carries its root's path. The record's path is
   fixed here from the author's view. *)
Stage(x, d, p) ==
    /\ Author[d] = x
    /\ ts[d] = 0
    /\ Rev[d] = None \/ Rev[d] \in known[x]
    /\ IF Rev[d] = None
       THEN p \in {Root} \cup {e \in View(x) : File[e] = File[d] /\ Rev[e] = None}
       ELSE p = Root
    /\ ts' = [ts EXCEPT ![d] = Clock(x)]
    /\ lamport' = [lamport EXCEPT ![x] = Clock(x)]
    /\ anchor' = [anchor EXCEPT ![d] = p]
    /\ path' = [path EXCEPT ![d] =
                  IF Rev[d] # None THEN path[LRoot(Rev[d])]
                  ELSE IF p = Root THEN << <<Clock(x), Rank[x]>> >>
                  ELSE Append(path[p], <<Clock(x), Rank[x]>>)]
    /\ pending' = [pending EXCEPT ![x] = @ \cup {d}]
    /\ UNCHANGED <<known, doc, firstSeen, rendered>>
    /\ intent' = [intent EXCEPT ![d] =
                    IF Rev[d] = None THEN Intended(View(x), File[d], p, d)
                    ELSE (Render(View(x), File[d]))']

(* Publication of a pending declaration. PublishGuard: its anchor is known to
   the publisher, so an own pending anchor is published first. *)
Publish(x, d) ==
    /\ d \in pending[x]
    /\ anchor[d] = Root \/ anchor[d] \in known[x]
    /\ pending' = [pending EXCEPT ![x] = @ \ {d}]
    /\ known' = [known EXCEPT ![x] = @ \cup {d}]
    /\ doc' = [doc EXCEPT ![x] = RenderAll(known'[x])]
    /\ firstSeen' = SeeName(x, d)
    /\ rendered' = Rendered(x)
    /\ UNCHANGED <<ts, anchor, path, lamport, intent>>

(* Receive in any order for anchors; causal for the revision ancestor. *)
Receive(x, d) ==
    /\ d \in Published
    /\ d \notin known[x]
    /\ Rev[d] = None \/ Rev[d] \in known[x]
    /\ known' = [known EXCEPT ![x] = @ \cup {d}]
    /\ lamport' = [lamport EXCEPT ![x] = IF ts[d] > @ THEN ts[d] ELSE @]
    /\ doc' = [doc EXCEPT ![x][File[d]] = Render(known'[x], File[d])]
    /\ firstSeen' = SeeName(x, d)
    /\ rendered' = Rendered(x)
    /\ UNCHANGED <<ts, anchor, path, pending, intent>>

Next ==
    \/ \E x \in Agents, d \in Decls, p \in Decls \cup {Root} : Stage(x, d, p)
    \/ \E x \in Agents, d \in Decls : Publish(x, d)
    \/ \E x \in Agents, d \in Decls : Receive(x, d)

Spec == Init /\ [][Next]_vars
(* Fairness: whenever some agent can receive some publication, some receive
   eventually happens. RecvKnown is Receive's guard and known-set update; it
   leaves the derived state free, so checking it does not re-render. Every
   RecvKnown step of Next is a Receive step (Publish adds an unpublished
   declaration; Stage leaves known unchanged). Publications are bounded, so
   this suffices. Staging and publication get no fairness. *)
RecvKnown ==
    \E x \in Agents, d \in Decls :
        /\ d \in Published
        /\ d \notin known[x]
        /\ Rev[d] = None \/ Rev[d] \in known[x]
        /\ known' = [known EXCEPT ![x] = @ \cup {d}]
FairSpec == Spec /\ WF_known(RecvKnown)

TypeOK ==
    /\ ts \in [Decls -> 0..MaxTs]
    /\ anchor \in [Decls -> Decls \cup {Root, None}]
    /\ lamport \in [Agents -> 0..MaxTs]
    /\ pending \in [Agents -> SUBSET Decls]
    /\ known \in [Agents -> SUBSET Decls]
    /\ \A x \in Agents :
         /\ pending[x] \subseteq {d \in Decls : Author[d] = x /\ ts[d] # 0}
         /\ known[x] \subseteq {d \in Decls : ts[d] # 0}
         /\ pending[x] \cap Published = {}

(* Staged keys are distinct: the persistent clock exceeds every timestamp in
   the author's view, including its own pending declarations. *)
KeysUnique ==
    \A d, e \in Decls : d # e /\ ts[d] # 0 /\ ts[e] # 0 => Key(d) # Key(e)
ClockCovers == \A x \in Agents : \A d \in View(x) : ts[d] <= lamport[x]

(* A published declaration's anchor is published; a pending one's anchor is
   published or the author's own pending declaration. *)
AnchorClosed == \A d \in Published : anchor[d] = Root \/ anchor[d] \in Published
PendingAnchor ==
    \A x \in Agents : \A d \in pending[x] :
        anchor[d] = Root \/ anchor[d] \in Published \cup pending[x]

(* The carried paths order roots as the anchor tree does wherever the anchors
   are present: in every agent's view, and in its known set when that is
   anchor-closed. *)
CarriedPathAgrees ==
    \A x \in Agents, f \in Files : \A K \in {View(x), known[x]} :
        (\A d \in Roots(K, f) : anchor[d] = Root \/ anchor[d] \in K)
            => Positions(K, f) = TreeOrder(K, f)

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

(* Every known live declaration is rendered, including one whose anchor has
   not arrived: rendering reads the carried path, not the anchor record. *)
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

(* The author's intended render at staging (d right after its anchor's
   lineage block in the author's view, which includes its own pending
   declarations) stays a subsequence of every later render, restricted to
   the declarations still rendered there. *)
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
        /\ d # e /\ d \in Published /\ e \in Published
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
(* An author has staged a declaration anchored at its own pending one. *)
NeverOwnPendingAnchor ==
    ~\E x \in Agents : \E d \in pending[x] : anchor[d] \in pending[x]
(* An agent renders d before receiving d's anchor, and orders d against
   another declaration e as d's author does. *)
NeverEarlyArrivalRendered ==
    ~\E x \in Agents, d, e \in Decls :
        LET f == File[d] IN
        /\ d \in known[x] /\ anchor[d] \notin known[x] \cup {Root}
        /\ d # e /\ {d, e} \subseteq Range(doc[x][f]) /\ {d, e} \subseteq Range(doc[Author[d]][f])
        /\ Restrict(doc[x][f], {d, e}) = Restrict(doc[Author[d]][f], {d, e})
=============================================================================
