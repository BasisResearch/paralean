# Paralean design

Proposed implementation. Research date: 2026-10-03.
See [Lean integration](lean-integration.md), [plan](plan.md), and
[verification scope](../verification/README.md).

## Decision

Distribute immutable, checked declaration groups and exact dependencies. Replicate
small discovery records by set union. Resolve names by explicit revision ancestry.
Concurrent conflicting declarations are recorded as conflicts, and the workspace
view renames every lineage but the one with the lowest root (Lamport time, author).
Keep candidates
private until validation and durable replication succeed. Export ordinary source
snapshots that compile under the unmodified pinned Lean.

No global name lock or ordered declaration log is required. Storage acknowledgements
require a write quorum. A partition may delay publication/discovery without
invalidating an existing snapshot. Safety and availability have separate assumptions.

## Requirements

| Original requirement | Design response | Implementation acceptance gate |
|---|---|---|
| Latest Mathlib-compatible Lean nightly | Pin tested compiler/library revisions | Stock and fork build same Mathlib |
| Fine-grained sharing | Checked `addDecl` groups | B uses A's helper before A finishes its file |
| Distributed checking and LSP | Immutable jobs and remote document sessions | Local/remote results agree |
| Ordinary agent workflow | Files, Lake, Lean diagnostics/search/completion | Unmodified agent uses remote helpers |
| No speculative library facts | Admit only completed checked declarations | Failed drafts and `sorry` remain private |
| Avoid stepping on others' work | Private workspaces; explicit conflicts | Duplicate names eventually diagnose |
| Upstream edits | Exact dependency versions; retained snapshots | Changed bodies invalidate current consumers |
| No new axioms or weakened targets | Trusted policy and frozen target contracts | Adversarial submissions rejected |
| Machine cycles allowed | Declaration DAG; mutual groups atomic | B.helper_b → A.helper → B.helper_c works |
| Large proof terms; caching | Immutable compressed blobs; lazy fetch | Transfer/cache benchmarks |
| Crash tolerance | Replicated source, terms, receipts, manifests | Recover acknowledged work after disk loss |
| Stock-Lean final project | Source export and clean base-compiler build | No fork/runtime/cache needed |
| Less merging | Merge dependency graphs; regenerate import layout | Valid graph exports with acyclic imports |
| Massive parallelism | Independent jobs, warm caches, backpressure | Scaling measurements |
| One autonomous entry point | Controller command/skill | End-to-end multi-agent demonstration |
| Prove2me-style purity/decomposition | Pinned checking inputs; private AND/OR task graph | Open obligations never become usable facts |

## Objects and identity

```
DeclID = hash(format, Lean commit, declaration kind, names, universes,
              types, bodies, safety/reducibility metadata,
              exact dependency IDs, atomic group membership)
RevisionID = hash(DeclID, parent RevisionIDs, source/frontend manifest)
package = {declarations, dependency map, source capsule,
           frontend manifest, provenance, validation receipt}
```

Use canonical length-delimited encoding and domain-separated hashes. Verify fetched
bytes. Collision resistance is an assumption. Do not serialize process pointers.
Keep declaration identity, source identity, receipt identity and elaboration-cache
key separate. Byte-identical declarations/dependencies deduplicate despite distinct
source locations. Different proof bodies conservatively have different IDs in v1.
The registry indexes revision/package IDs. A revert creates a new revision pointing
to existing content; it does not resurrect an ancestor as a new head. The formal
models' `Decls` sort denotes these immutable revision packages. Dependencies pin
exact packages; content-equivalence optimizations are deferred.

Advertise signatures eagerly: name, type, universes, kind, dependency IDs, receipt
and source location. Fetch bodies lazily. An advertisement describes validated
content; it does not authorize inserting an axiom with that type.

Large bodies may use shared chunks/subtrees. These are storage units, not independent
proofs. The logical unit is a completed declaration or atomic group. It has no free
locals or unresolved metavariables; bound variables and universe parameters remain
normal. Arbitrary internal expression fragments would require their local context.

## Admission and B's workflow

1. A edits ordinary files in its private workspace.
2. Elaboration completes a declaration group against a pinned environment.
3. Capture exact dependencies and frontend inputs. Local elaboration keeps Lean's
   asynchronous mode. The capture hook waits until every kernel task of the
   command has succeeded, so no other worker sees a statement before its proof is
   kernel-checked. Capture names generated auxiliaries deterministically.
4. A trusted validator reconstructs the environment, checks the candidate, enforces
   axiom policy and compares any fixed task contract. It signs a receipt over the
   exact group ID. A worker stages a group only while holding that receipt.
5. Durably store the package, source, receipt and dependency closure.
6. Publish a small record only after durable acknowledgement.
7. B's anti-entropy refresh adds the record to ordinary search/completion and source
   lookup. Using its name pins the ID and materializes a compatible dependency closure.

Publication also persists a separate discovery marker naming the exact group.
Successful marker acknowledgement is the publication event. A partial marker
upload remains staged. After a replica is lost, a single surviving copy cannot
show whether its marker was acknowledged. So each replica also stores an
acknowledgement certificate, written only by a node that knows the group as
published. The writer records each replica's reply; replies collected over time
form a certificate quorum, even if a replying replica is later lost. Discovery
reads certificates from live replicas, never raw marker bytes.

Publication has one atomic point. The marker is durable on a write quorum first;
then a single conditional write publishes the group (for a target, conditional on
the owner's epoch). Certificates are written only after that write succeeds, so a
writer whose conditional publish failed never certifies its group.

Discovery after index loss is complete for groups with a certificate quorum.
A published group without one is published but not yet discoverable: if every
node that knows it loses its index first, it is lost to discovery. Any node that
knows the group writes certificates, and a checkpoint commit requires the
committer's own certificate quorum for every group it contains. So no checkpoint
depends on an undiscoverable group, and no surviving peer or remembered group ID
is needed to recover one.

The project has a generated shared prelude/import managed by the controller. New
discoveries enter at frontend command boundaries. Pin an elaborating command;
rebase and invalidate the affected document suffix before changing its environment.
Search may show incompatible versions, but completion must respect the pinned
environment. Agents use normal Lean tools, without a remote-publication API.

A worker's claim that it checked something is insufficient. Either replay validation
locally or require a receipt from a trusted validator with pinned policy/version.
The validator does not trust worker `.olean` files or cached axiom summaries.

The immutable record set is already a grow-only CRDT. Gossip transports differences;
Merkle summaries avoid full scans. No general CRDT library is needed initially.
There are no clocks or merge metadata on every proof-expression node.

## Revisions and eventual errors

For each fully qualified name, retain admitted IDs and explicit edit ancestry.
Current heads are records not superseded by a known descendant. Zero means unknown;
one means a candidate; multiple incomparable heads mean a conflict. The registry
records every conflict. Supersession never comes from clocks; the rendered
workspace view separately renames all but one conflicting declaration (see
[transparent workspaces](#transparent-workspaces)).

An edit names the predecessor it actually read. Ancestors must be admitted, have
the same name, and form a transitively closed causal history. Lamport timestamps
do not establish supersession. Identical IDs deduplicate. Two independently checked
proof bodies with the same name/type still conflict unless explicitly revised.

Resolve by a new checked revision naming all resolved heads, or rename and recheck
consumers. Preserve history. For ordinary names, a previously unseen concurrent
head can create another conflict. A persistent unresolved collision eventually
appears everywhere under fair anti-entropy and eventual recovery/connectivity.

Required target names never collide. The controller assigns each target one
owner with an epoch held in the store. Only the current owner prepares a proof
of the target. The owner/epoch record also holds the target's latest published
proof (its head). The new proof must revise that recorded head. A scan of
publication markers or certificates is not enough: it may miss a published proof
that has no certificate quorum yet. Publishing a target proof is a write
conditional on the epoch it was prepared under, and the same write updates the
recorded head. The preparer reads owner, epoch and head in one read and stamps
the proof with that epoch. Reassigning the target, for
example after the owner crashes or is partitioned, bumps the epoch, so the old
owner's pending proof can never publish. Published proofs of a target therefore
form a chain with a unique head across any number of handovers. Targets declared
by one group are assigned jointly. Parallel attempts at the same target by other
workspaces stay private, or publish under other names, until the owner adopts
one as a revision.

A locally unique name may have an unseen competitor during a partition. The system
permits temporarily divergent resolution while preserving each snapshot's meaning.
Immediate global uniqueness would require a different coordination contract.

Changing `def value : Nat := 0` to `:= 1` changes identity despite an unchanged type.
The old proof remains valid in its old snapshot; it is not evidence about the new
definition. Reverse dependency edges identify current jobs to re-elaborate/recheck.
Nothing resolves a pinned dependency against “latest” during checking.

An environment permits one declaration per fully qualified name. A transitive closure
requiring two versions of that name is incompatible, even when its immediate imports
have distinct names. Report this instead of silently rebinding either dependency.
New current checkpoints require every member of their closure to be current. Once
an upstream replacement is known, rebuild affected consumers before committing.
Historical exports remain available by explicit immutable checkpoint ID.

The protocol must establish these obligations separately:

- Every published revision's dependencies and causal ancestors are published.
  The same holds for dependencies and ancestors of a pending revision.
- First-publication order strictly decreases along dependency and ancestor edges.
  Neither relation permits circular admission.
- Every successful commit selects the unique current head for each name in its
  contents, using the committing worker's knowledge immediately before the commit.
  This also applies when the selected checkpoint equals the previous checkpoint.
- Later discoveries may make a committed checkpoint stale. Its pinned contents
  remain valid; freshness is a condition on the commit event.
- The work witness must complete the full `B.helper_b → A.helper → B.helper_c`
  chain and commit its closure. Publishing an independent declaration alone does
  not establish this requirement.

The checker and exporter contracts remain separate. `Valid` must enforce kernel
acceptance, exact dependency meanings, the allowed-axiom policy and any fixed
target contract. `Exportable` must attest to a clean source build of the selected
contents. A controller may report task completion only when every required target
is present with its pinned contract; an empty buildable checkpoint is insufficient.
These interfaces require implementation evidence before the protocol guarantees
can be applied to the Lean fork.

## Transparent workspaces

Agents work on one shared Lean codebase. Each agent has its own working copy and
uses ordinary files, Lake, git and Lean tools. No agent sees the distributed
protocol. `leanc`/Lake perform it underneath.

**Remote declarations.** When a teammate publishes a declaration in file `F`, every
other copy of `F` receives it as `theorem foo : T := remote% <declID>` (likewise
`def`). Elaborating `remote%` checks the registry binding of `<declID>`: its
statement, dependency versions and a valid receipt. The rendered name is only a
local binding of that ID, so the check does not depend on which renames a copy
currently knows. A forged `remote%` fails. In v1 the checker prefetches the missing
declaration packages, theorem proofs included, before kernel checking (see
[lean-integration.md](lean-integration.md)); the kernel does not demand-load bodies.
Definitions, instances and structures load their real bodies, since definitional
unfolding, `simp` and instance search need them. A `remote%` declaration brings
its own dependency closure from the store, independent of the file's imports, so
cross-agent cycles such as `B.helper_b → A.helper → B.helper_c` never create a
module cycle. Export replaces every `remote%` with real source before the clean
stock build. Replacing a `remote%` body with one's own proof publishes a revision
whose ancestor is the remote declaration.

**Placement.** Each file is a declaration-level list CRDT (RGA) whose elements
are declaration lineages. A publication record carries its file path, an anchor,
a Lamport timestamp and its author. The anchor is the nearest declaration above
it in the author's file that is published or that the author has itself staged,
or the file start, and lies below every same-file dependency. It is never a line
number or private text. A group publishes only after its anchor is known to the
publisher, so an author's batch of new declarations keeps its order. Each record
also carries the anchor path of its lineage root and its lineage key per name.
Rendering therefore reads only the records a copy knows, even when anti-entropy
delivers a record before its anchor. Lamport clocks persist across restarts, so a
restarted agent never reuses a timestamp. Concurrent
inserts after one anchor are ordered by (Lamport time, author). A revision takes
its lineage root's position and replaces its ancestors in the rendered file;
concurrent revisions of one root sit together, ordered by their own keys.
Deleting a declaration publishes a tombstone revision, which renders as nothing;
dependents keep the exact old ID. Elements are published declarations only. A
character-level CRDT would stream unfinished drafts, which the admission rules
forbid.

**Identical published files.** The published projection of every file is a pure
function of the replicated publication set, rendered canonically (fixed
`remote%` text, whitespace, blank lines and import order). The models prove the
rendered view (declaration IDs, order and names) is a function of the known
records; canonical printing of that view is an implementation obligation. Two copies that know
the same publications contain byte-identical published projections, whatever
order the publications arrived in. Under fair anti-entropy every copy eventually
knows the same set, so the projections become identical. A whole file matches
only once its authors' drafts are published or discarded. Drafts live only in
their author's copy, between the shared elements. Only live heads render:
superseded revisions and tombstoned declarations leave the file.

**Names.** Explicit revision ancestry still decides supersession. Target names
keep the owner rule. For unrelated declarations sharing a name (neither revises
the other), each head is keyed by the lowest (Lamport time, author) in its
lineage, and the head with the lowest lineage key keeps the name. The author
knows every ancestor when staging, so each publication record carries its lineage
key. Only live, rendered groups compete for a name: a group superseded by any
revision, even one that revises it for a different name, holds none. Revising the
winner keeps the name in the winner's lineage. A concurrent revision of the same
lineage by another author may take it, but no other lineage can. The registry
still records the conflict; the rendered view resolves it. Every other head in
the conflict gets a deterministic fresh name in a reserved namespace that user
source cannot write; validators reject any group declaring a reserved name, so a
later declaration can never clash with a fresh name. Renaming is hierarchical: a
group's derived names (`T.mk`, `T.casesOn`, ...) move with it and stay in the
same namespace, so dot notation keeps working. Published projections are rendered
from pinned dependency IDs, so a rename never redirects a proof term. Tactic
scripts in the losing author's source (`simp [foo]`, `rw [foo]`) need a textual
rename. The winning lineage changes only when a concurrent declaration with a
lower root key arrives, when the winner is tombstoned, or when the winner's
lineage is superseded by a revision for another of its names. When that happens, the losing author
gets a diagnostic and a Lean rename of their own source and drafts at the next
turn boundary. Every copy applies the same renames once it knows the same set.

**Git and timing.** The CRDT state is the truth. Each agent's git history is
projected from it: teammates' insertions arrive as commits authored by those
teammates, so `git diff` shows only the agent's own work. Inserted text is
written into a working copy only between agent turns or before a build, never
during an edit.

## Cycles, source merge and checkpoints

Machine dependencies may cycle. Declaration versions cannot circularly justify
each other. `B.helper_b → A.helper → B.helper_c` works because dependencies precede
admission. Legal Lean mutual inductive/recursive groups are atomic external vertices.

Groups are captured per elaborated command, never per `addDecl`. Names fall into
three classes. Public names are every name a user can write: declared names,
auto-named instances such as `instFooNat`, and eager auxiliaries of inductives and
structures (`casesOn`, `recOn`, `below`, `brecOn`, `noConfusion`, `injEq`,
`ctorIdx`, projections, constructors, `SizeOf` instances). They enter collision
checks; two groups that both produce an eager auxiliary collide on it exactly
when they collide on its base. The fork names
instances canonically, without environment-dependent `_n` suffixes, so two
identical `instance` commands collide like any duplicate. The scheme must also be
injective: Lean's auto-names read only head symbols, so `Foo (∀ x : Nat, P x)` and
`Foo (∀ s : String, Q s)` both become `instFooForall`. Export writes every
instance name explicitly, so the stock build does not re-derive a different one.
Scoped names
(`_private.*`, `proof_n`, `match_n`, `_hyg` names and compiler auxiliaries) are keyed by their
group; the renderer and exporter both mangle them to group-unique Lean names.
The fork disables matcher and auxiliary-lemma reuse across groups, which would
otherwise make one group's elaborated term depend on another group's scoped name
and on arrival order. A `private` declaration used by a later command of the same
file is a cross-group reference; capture rejects or rewrites it.
Reserved names (`eq_1`, `eq_def`, `unfold`, `induct`) are created lazily by
consumers through `realizeConst`. They are never published; consumers and the
validator re-realize them from the pinned base group.

Commands that declare nothing (`namespace`, `section`, `open`, `variable`,
`universe`, `set_option`, `attribute`) also need a position. A rendered group
must elaborate in the scope it was checked in, so the frontend capsule records
that scope and the renderer reproduces it around the group.

Source concatenation is insufficient. Capsules preserve imports, namespaces, section
parameters, local instances, scoped notation, options, macros, attributes, generated
names and command dependencies. Kernel dependency edges alone do not capture this.
Effects or custom commands can require a larger capsule; unsupported extraction is
a diagnostic. Never guess the missing frontend state.

The exporter selects a closed compatible graph and constructs an acyclic file layout.
The machine-cycle example may require three output files from two agent files.
Preserve human layout where possible; arbitrary original layout is not guaranteed.
Generated ordinary Lean declarations are another export route only for supported
declaration kinds. Source must remain available with every acknowledged package.

Build the export in a clean directory using stock Lean and the pinned Mathlib.
Compare required target statements and dependency meanings; check allowed axioms.
Durably store the successful manifest before advancing that workspace's checkpoint.
Failed merge/build leaves the previous checkpoint. A compiling empty project does
not finish a task: every required target contract must be present and validated.

Before reporting completion, also durably retain a catalogue record for the same
workspace and exact snapshot. The completion action checks this record. Its
payloads, manifest and catalogue entry share one store, so a crash immediately
after completion cannot leave the snapshot without a discoverable catalogue ID.
Committing the record means writing its fenced commit certificate (see the storage
model below); completion therefore implies a record that recovery can adopt.

Private editing buffers can be temporarily broken. Crash tolerance means the last
acknowledged checkpoint remains recoverable and buildable, not that every keystroke
forms a compiling project. Source replay/export correctness remains an implementation
gate; the protocol models treat it as an explicit interface.

## Storage and failure model

Storage owns the data; the producer does not own the only copy. A location registry
is advisory. Unannounced power loss must work without a shutdown broadcast.

The interface supplies write quorums `W`, recovery quorums `R`, and `meet(w,r)`
belonging to both. Ack means every member of one write quorum persisted validated
bytes. Failures must leave some recovery quorum alive. Every acknowledged object
then has a surviving copy, accessible through every surviving recovery quorum.
The proof uses this interface, not numerical majority arithmetic. V1 has no
replica repair or membership change, so the loss budget is cumulative over the
deployment's lifetime: with three replicas and majority quorums, one replica may
ever be lost. Repair is a prerequisite for long-running deployments.

The model permits permanent disk destruction. It excludes loss of every recovery
quorum, storage lying about persistence, hash collisions and validator errors.
Network isolation can delay access even when bytes survive. Safety needs no delivery
fairness; progress needs eventual connectivity, recovery and fair service.
Continued publication additionally needs a live write quorum. Surviving recovery
quorums alone guarantee retrieval, not the ability to acknowledge new objects.

Sources, receipts, dependency manifests and checkpoint manifests use the same store.
Each workspace has a distinct identity and one writer. After worker loss, a replacement
uses a fresh workspace identity unless an external fenced ownership service says
otherwise. Timeout alone does not grant ownership. Tokens are signed by the issuer
and bound to the holder, and each token rank is issued once.

Fencing applies at commit, not only at the first write. A catalogue record carries
its writer's token. The first write of the record is conditional on the store's
fence. Repair copies and acknowledgements are not fenced, and a replica accepts a
repair only for bytes some replica already holds. Fencing the first write alone
is not enough: a stale writer can write one copy just before a rotation, then
repair and acknowledge it afterwards. So committing a record is a separate
per-replica commit certificate, written by a conditional write on the fence and
only after the writer's own acknowledgement of the record bytes. Manifest and
payload certificates follow their own acknowledgements. Recovery adopts a record
only when the record's commit certificate, its manifest certificate and every
payload certificate are each held by every live member of some write quorum. A
record whose writer lost the fence before committing never gets a commit
certificate, so it is never adopted, whatever happens to its bytes. The selected
record was committed while its writer held the fence. Both conditional writes
need a transaction that checks a fence item and writes atomically (etcd `Txn`,
DynamoDB `TransactWriteItems` with a condition check, FoundationDB). A plain
per-key conditional put does not suffice.
Multiwriter checkpoint aliases must expose conflicts; no hidden global consensus
is assumed.

Checkpoint records include workspace identity, predecessor IDs, source graph root
and stock-build receipt. The storage adapter must support recovery-quorum enumeration
of these records, or an equally durable manifest catalog. Reconstruct causal heads
from that catalog; do not depend on the dead desktop retaining the final hash.
If multiple heads exist, recover a buildable historical checkpoint and expose the
conflict. Readiness comes from certificates on live replicas, never from
whether surviving bytes were once acknowledged: a lone surviving copy cannot show
that. A discovered record without its certificates stays staged. Certificates
are not repaired in v1, so a record is adoptable after replica loss only if its
certificates were durable beforehand; adding repair needs the same existing-bytes
rule as record repair.
The Veil recovery model proves quorum-catalog coverage, validation of discovered
records, causal head reconstruction and safe selection after local-ID loss. On
the hardened path the scan is computed from certificates in the store, and it
covers every committed record.
Within decoded, schema-valid records, wrong-workspace, nonbuildable or incomplete
staged entries cannot block recovery of acknowledged work. Decoder validation must
reject malformed metadata and enforce the assumed ancestry schema.
Adopting re-acknowledged historical data grants no writer ownership. Physical
enumeration, byte decoding and the fenced ownership authority remain implementation
interfaces. The group, receipt and recovery models share exact artifact meanings;
typed storage identities separate payloads, manifests, catalog records and
publication markers.

Recovery loads a durable checkpoint and rebuilds indexes/caches. Private candidates
and incomplete uploads may be lost. Acknowledged packages cannot disappear within
the stated failure envelope. V1 retains acknowledged objects. Garbage collection,
membership changes and reclamation of offline references need additional protocols.

## LSP, orchestration and performance

Route existing Lean LSP document sessions to workers. Pin workspace ID, environment
ID, document version and worker generation; discard mismatched responses. Preserve
URI mappings, cancellation and backpressure. Lean RPC object references remain tied
to their originating session. They are not global serializable handles.

Global search reads signature/provenance indexes. Hover, goal state and elaboration
requests use the pinned document worker. After failure, recreate it from checkpoint
and editor buffer. Indexes are rebuildable caches.

One controller command/skill creates workspaces, dispatches ordinary agents against
fixed target contracts, monitors conflicts and exports checkpoints. Task ownership
reduces duplicate effort but does not establish correctness. Prove2me's AND/OR
graph can schedule obligations/alternatives privately. An open obligation or conditional
reduction is never advertised as the requested completed lemma. Its API documents
the distinction, not a proof of backend purity/performance.
[Prove2me workflow](https://github.com/prove2me/prove2me_workspace/blob/main/references/prove.md)

Checking is a function of pinned checker, policy, declaration and exact environment.
Timeout/unavailable bytes are inconclusive. Cache state changes cost, never meaning.
Elaboration additionally depends on frontend extensions, plugins, options and IO.
Isolate/record those inputs or mark the result uncacheable.

Preserve expression DAG sharing, compress/chunk large payloads, batch small records,
prefetch dependencies and schedule near warm environments. Bound queues and memory.
Measure cold/warm latency, transferred bytes, cache hits after edits, fanout, LSP
latency and throughput versus worker count. The models establish no speedup.
Kernel-internal remote body loading is conditional on profiling; it is not v1's
trust-boundary shortcut.
