# Paralean design

Proposed implementation. Research date: 2026-10-03.
See [Lean integration](lean-integration.md), [plan](plan.md), and
[verification scope](../verification/README.md).

## Decision

Distribute immutable, checked declaration groups and exact dependencies. Replicate
small discovery records by set union. Resolve names by explicit revision ancestry.
Concurrent conflicting declarations produce eventual errors. Keep candidates
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
3. Capture exact dependencies and frontend inputs. Wait for kernel tasks; an async
   signature becoming available does not establish completed checking.
4. A trusted validator reconstructs the environment, checks the candidate, enforces
   axiom policy and compares any fixed task contract.
5. Durably store the package, source, receipt and dependency closure.
6. Publish a small record only after durable acknowledgement.
7. B's anti-entropy refresh adds the record to ordinary search/completion and source
   lookup. Using its name pins the ID and materializes a compatible dependency closure.

Publication also persists a separate discovery marker naming the exact group.
Successful marker acknowledgement is the publication event. A partial marker
upload remains staged. The store must enumerate publication markers from a
surviving recovery quorum and supply their durable acknowledgement evidence.
This permits discovery when every worker has lost its index; no surviving peer
or remembered group ID is required.

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
one means a candidate; multiple incomparable heads mean an error. No automatic winner.

An edit names the predecessor it actually read. Ancestors must be admitted, have
the same name, and form a transitively closed causal history. Lamport timestamps
do not establish supersession. Identical IDs deduplicate. Two independently checked
proof bodies with the same name/type still conflict unless explicitly revised.

Resolve by a new checked revision naming all resolved heads, or rename and recheck
consumers. Preserve history. A previously unseen concurrent head can create another
conflict. A persistent unresolved collision eventually appears everywhere under
fair anti-entropy and eventual recovery/connectivity.

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

## Cycles, source merge and checkpoints

Machine dependencies may cycle. Declaration versions cannot circularly justify
each other. `B.helper_b → A.helper → B.helper_c` works because dependencies precede
admission. Legal Lean mutual inductive/recursive groups are atomic external vertices.

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
The proof uses this interface, not numerical majority arithmetic.

The model permits permanent disk destruction. It excludes loss of every recovery
quorum, storage lying about persistence, hash collisions and validator errors.
Network isolation can delay access even when bytes survive. Safety needs no delivery
fairness; progress needs eventual connectivity, recovery and fair service.
Continued publication additionally needs a live write quorum. Surviving recovery
quorums alone guarantee retrieval, not the ability to acknowledge new objects.

Sources, receipts, dependency manifests and checkpoint manifests use the same store.
Each workspace has a distinct identity and one writer. After worker loss, a replacement
uses a fresh workspace identity unless an external fenced ownership service says
otherwise. Timeout alone does not grant ownership. Multiwriter checkpoint aliases
must expose conflicts; no hidden global consensus is assumed.

Checkpoint records include workspace identity, predecessor IDs, source graph root
and stock-build receipt. The storage adapter must support recovery-quorum enumeration
of these records, or an equally durable manifest catalog. Reconstruct causal heads
from that catalog; do not depend on the dead desktop retaining the final hash.
If multiple heads exist, recover a buildable historical checkpoint and expose the
conflict. Re-establish durability before adopting a merely discovered staged record.
The Veil recovery model proves quorum-catalog coverage, validation of discovered
records, causal head reconstruction and safe selection after local-ID loss.
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
