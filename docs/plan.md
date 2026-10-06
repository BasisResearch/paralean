# Implementation plan

This delivery covers design, TLA+ checks, Veil/Lean verification and a P1
prototype. The prototype (`impl/p1`, [gate report](p1-gate.md)) runs as a library
and CLI; it passes G1 to G6 on 21 fixture files and an 18-module Mathlib sample, on stock
Lean and on the minimal Paralean fork (`fork/`). P2 storage runs in `impl/p2`. The
distributed service (P3 onwards) is subsequent implementation work.

The abstract protocol gates now include atomic multi-name groups, receipt/session
binding, every required target at durable commit, and checkpoint catalog recovery
after losing the local ID. See the [proof obligations](../verification/PROTOCOL-OBLIGATIONS.md)
and [recorded checks](../verification/results/README.md). These results do not close
the implementation gates below.

Additional protocol proofs tie recovery ancestry exactly to parent paths and permit
alternative checked objects for a fixed target. A concrete two-worker execution
combines atomic helper admission, a dependent target, both receipts, durable task
completion and destruction of an acknowledging replica.

The [joint protocol](../verification/veil/PROTOCOL.md) additionally couples task
completion to a durable catalogue record for the exact snapshot. Publication
retains a distinct discovery marker; scanning a surviving quorum reconstructs
published IDs after every worker index is lost. Implement these guards together.
Payload and manifest persistence alone do not satisfy this protocol.

The [hardened protocol](../verification/veil/HARDENED.md) adds receipt-gated
staging, single-owner target names, fenced catalogue writes and commit
certificates, and per-replica publication certificates. These five guards are
proved on one joint transition. The receipt is bound to the group ID only; binding
it to policy and checker version is an implementation contract. The Lean naming
layer ([LeanNames](../verification/veil/LEAN-NAMES.md)) and the transparent-workspace
model ([Workspaces](../verification/veil/WORKSPACES.md)) are separate refinements of
the Groups registry; `Hardened` imports neither. P1–P3 below carry the resulting
implementation contracts.

## P0 — Pin the baseline and interfaces

Lean: `nightly-2026-10-03`, commit `193c3589a4fc16c4059261ab38cfa365eb24f323`.
Mathlib nightly: `0575336843263378752eeb5f4c75a612327768a2`; matching toolchain and
successful build/test [CI run](https://github.com/leanprover-community/mathlib4-nightly-testing/actions/runs/37115079169).
P0 also rebuilt it locally from scratch with the stock binary and ran its tests
([p0-log](p0-log.md)).

Preserve a stock binary. Freeze encoding, receipts, source capsules, revision rules,
durable acknowledgement and snapshots. Reproduce baseline builds before modifying
Lean. Formal tooling separately pins Veil and Lean 4.32.0.

Choose the store before P2. The models assume replicas the system controls:
per-replica certificates, recovery-quorum enumeration and a fence register checked
atomically with catalogue writes. Two shapes fit. (a) A linearizable replicated
metadata store for markers, certificates, catalogue and fences, with large
immutable payloads in an object store. A committed metadata transaction then
discharges the quorum and certificate layers. (b) Self-managed replicas
implementing the modelled quorum interface directly. Plain S3 alone fits neither,
because its conditional put cannot check a fence held under another key.

[Store choice](store.md) takes (a): FoundationDB for metadata, S3 for payloads,
payload before metadata. It records the refinement argument: one abstract replica
with `W = R = {{σ}}`, each committed transaction as a fixed sequence of model steps,
and paginated scans justified by grow-only key spaces. It also lists what the
argument does not cover (unresolved unknown outcomes, deletion, restore,
cross-region). DynamoDB is the fallback under the same mapping; etcd is rejected on
size.

Gate: baseline Mathlib build, extraction corpus, protocol verification and a
written store choice with its refinement argument (signed off 2026-10-05: self-hosted FoundationDB plus an S3-compatible payload store).

## P1 — Local declaration replay and stock export

Capture completed groups, exact dependencies and frontend capsules. Reconstruct
compatible environments in one process with a local content-addressed store.
Replay using the stock kernel before adding network transport. P1's gate is
reproducible from a clean checkout with `impl/p1/scripts/bootstrap.sh --mathlib`
and `run-all.sh` (elan toolchain checked against 193c3589, Mathlib from the cache,
no full build).

Capture at command granularity. One elaborated command (inductive, structure,
mutual block, recursive `def`, `instance`) is one group holding every `addDecl` it
performs: `casesOn`, `recOn`, `noConfusion`, `below`, `brecOn`, `injEq`, `ctorIdx`,
SizeOf instances, `proof_n`/`match_n` auxiliaries and nested `realizeConst` calls.
Never publish per `addDecl`. Classify names as public, scoped or reserved. Public
names are everything a user can write, including auto-named instances and eager
auxiliaries; only they enter collision checks. Name instances canonically and
injectively, without environment-dependent `_n` suffixes. Disable matcher and
aux-lemma reuse across groups; treat `_hyg` names as scoped. Scoped names (`_private.*`, `proof_n`,
`match_n`, compiler auxiliaries) are keyed by group; the renderer and exporter
mangle them to group-unique Lean names. Reserved names (`eq_n`, `eq_def`,
`unfold`, `induct`, `fun_cases`, `hinj`, match/congruence equations) are never
published; consumers and the validator re-realize them from the pinned base group.
Capture waits for the command's kernel tasks. V1 forces `Elab.async` off
everywhere (capture, validator, export, `remote%` and the interactive server) and
rejects attempts to change it; P1 measured ×1.39 wall time on the Mathlib sample,
×2.2 on the worst file, with lower total CPU. Restoring asynchronous interactive
elaboration is a fork target, conditional on OPEN-14.
See [Lean names](../verification/veil/LEAN-NAMES.md).

Cover theorems, definitions, structures, inductives, mutual groups, well-founded
recursion, private/generated declarations, instances, simp attributes, scoped
notation, macros and initialization effects. Reject changed targets, new axioms,
`sorryAx`, bypass options and transitive version conflicts.

Export two workspaces, including B→A→B dependencies, into a clean stock-Lean build.
Record cases requiring larger source capsules. Keep source/line mappings usable.

Gate: replay and clean export agree with reference behavior. This is the critical
engineering feasibility gate.

The Paralean Lean fork (`fork/`, Lean `193c3589` + 6 patches, commit `dfc13cc6`) implements
the P1 hooks natively: `Elab.async` pinned off, a per-command declaration collector, no axiom
fallback after kernel failures, a `simp` used-lemma record and canonical instance names for
anonymous and derived instances. On the fork the P1 gate gives the same G1–G6 results as on
stock, with 12 more instances named canonically ([fork-log](fork-log.md)).

## P2 — Storage and eventual registry

Implemented in `impl/p2` (Rust): self-hosted FoundationDB 7.3 + Garage, T1–T7,
certificate-based discovery and catalogue recovery, fault injection; gate tests pass
against the live services ([p2-log](p2-log.md)). Not yet: FDB faults within a redundancy
mode, tombstones (§11.4), anti-entropy between deployments.

Implement immutable writes, hash verification, durable acknowledgements, anti-entropy,
recovery, causal revisions and conflict diagnostics on FoundationDB and S3, using the
key layout and transactions of [store.md](store.md). Every transaction is
idempotent, and a writer resolves an unknown commit outcome before it proceeds.

Inject duplicate/reordered/lost messages, partitions, killed workers, incomplete
uploads, corrupt bytes, validator timeouts and allowed disk loss. Add the store
faults of [store.md](store.md#p2-obligations-from-this-choice): unknown commit
outcomes, rotation or reassignment between a read and a commit, S3 PUT timeouts and
killed FoundationDB processes. Convert model counterexamples into protocol
regression fixtures. Keep GC disabled; the bucket denies deletes.

Gate: no unvalidated/under-replicated publication; convergence; checkpoint recovery,
including loss of the desktop's last manifest hash. Exercise storage enumeration
and causal head reconstruction, not only fetch-by-known-ID.

Implement the [hardened protocol](../verification/veil/HARDENED.md) guards with
the storage layer, not after it. The first write of a catalogue record and its
per-replica commit certificates are transactional writes conditional on a fence
held in the same store; repair copies (of existing bytes only) and
acknowledgements are unconditional; rotation is a linearizable write. Recovery
adopts only records whose commit, manifest and payload certificates are held by
every live member of some write quorum. Each
replica keeps acknowledgement certificates separately from marker bytes; discovery
reads only certificates on live replicas. Checkpoint commit waits for the
committer's own certificate quorum, collected from replies over time.
Regression fixtures must include a stale writer after fence rotation, a put before
rotation acknowledged and repaired after it (and never adopted), a repair copy
after rotation, a target published just before a handover without a certificate
quorum, and a surviving
staged marker indistinguishable by bytes from a published one. Under the
single-replica mapping of [store.md](store.md) the per-replica rules hold
trivially; the fixtures still apply, as unknown-outcome retries across a rotation
and markers without certificate keys.

Protocol gates also require admitted ancestor closure, acyclic causal ancestry,
and freshness at each commit, including repeated commits to the same checkpoint.
Remove each admission/freshness guard in a regression model and require the
corresponding property to fail when the guard is independently necessary; record
redundant guards in the [guard matrix](../verification/TLA-GUARDS.md).
Require a full B→A→B dependency-chain witness;
a model that rejects dependent declarations must fail that witness check.

## P3 — Distributed checks and transparent imports

Add immutable job envelopes, trusted validators, compatibility checks and remote
declaration availability. Workers stage a group only while holding a validator
receipt signed over that exact content-addressed group ID, policy and checker
version; they never self-certify. The controller assigns each target an owner and
an epoch held in the store, with the target's latest published proof (head) in
the same record. Only the owner prepares a proof of the target, which must revise
that recorded head; publication is conditional on the epoch and updates the head
in the same write. Reassignment bumps the epoch, so a crashed or partitioned owner cannot
publish afterwards. Parallel attempts at one target stay private until the owner
adopts one. Pin commands; complete kernel checks before publication.
Add retry deduplication, cancellation, memory limits and queue backpressure.

Run ordinary agents across machines/worktrees. B must use A's completed helper while
A continues its file. Change an upstream definition and verify invalidation, stale
response rejection and retained old snapshots.

Gate: unchanged agent workflow, adversarial validation, clean exports, fork Lean/
Mathlib tests and measured transfer/checking costs. The fork passes Lean's own test suite
with its hooks off (4339/4340; the one failure is environmental and also fails on stock); in
Paralean mode the differences are the intended ones plus server tests that need asynchronous
elaboration (OPEN-14).

`remote%` in v1 materializes the published members, theorem proofs included, and
kernel-checks them unless the environment already holds them; it never accepts a
body it cannot fetch (p0-interfaces §11.2). The P1 prototype differs: in working
copies it elaborates only a theorem's statement and adds a receipt-backed
placeholder axiom, never fetching the proof, and its receipts are an HMAC under a
shared key ([p1-transparent.md](p1-transparent.md)). The HMAC stands in for
validator Ed25519 signatures (§6). P3 replaces both: real proofs and signed
receipts.

Agents keep an unchanged workflow through [transparent workspaces](architecture.md#transparent-workspaces):
`remote%` declarations checked by ID, a declaration-level RGA per file, lineage
naming and git histories projected from the CRDT. Gate additionally: rendered
published projections are hash-identical across copies after exchange in any order;
superseded and tombstoned declarations leave the file; revising a collision winner
keeps its name; forged `remote%` is rejected; no placeholder axiom appears in any
working copy's `#print axioms`; B→A→B works through `remote%` without module
cycles; a losing author receives a diagnostic and a Lean rename. A rendered
collision loser elaborates in working copies, but no checkpoint containing either
colliding group commits until a revision or tombstone resolves the registry
conflict (see [architecture](architecture.md#transparent-workspaces)).

## P4 — Distributed LSP

Implement worker routing, URI mapping, search/source aggregation and exact document
version/environment/generation checks. Preserve completion, diagnostics, hover,
goals, rename and cancellation. Keep RPC references session-affine.

Gate: editor tests across death/reconnect; no stale states; measured p50/p95 latency.

## P5 — Autonomous controller

One entry point provisions workspaces, dispatches ordinary agents with fixed targets,
handles conflicts/recovery and exports the final project. AND/OR metadata remains
separate from the reusable library.

Gate: end-to-end multi-agent task, every required contract validated, stock build,
desktop-loss recovery and reproducible scaling benchmarks.

## Implementation obligations from verification

The models assume these. Each one needs an implementation and a test; none is
proved here.

Storage and publication:

- Atomic publish point. The publication marker is durable on a write quorum
  before the epoch-conditional publish write. Publication certificates are
  written only after that write succeeds.
- Replicas enforce repair-means-existing-bytes: a repair copy is accepted only
  for bytes some replica already holds, which signed record bytes make checkable.
- Fence and ownership tokens are signed by the issuer and bound to the holder.
  Each token rank is issued once.
- Catalogue certificates. The record's commit certificate is a conditional write
  on the fence register, written after the writer's own Ack of the record bytes.
  Manifest and payload certificates follow their own Acks.
- Recovery reads the certificates of every live replica and adopts a record only
  when each of its certificates is held by every live member of some write quorum.
- Certificates are signed, so a repair cannot forge one. The Lean model has no
  certificate repair; adding it needs the same existing-bytes rule.
- The target's latest published proof (head) is stored in its owner/epoch record
  and updated by the epoch-conditional publish. Either the owner serializes
  prepare and publish per name, or publish compares-and-swaps the head.

Workspaces and delivery:

- Causal delivery, or records that carry their anchor path. The model takes the
  second: records carry the lineage root's anchor path and a lineage key per name.
- A group is published only after its anchor is known to the publisher.
- Persistent Lamport clocks: a restarted agent never reuses a timestamp.
- Validators reject groups that declare a name in the reserved fresh namespace.

Lean names:

- Place `namespace`, `section`, `open`, `variable` and `attribute` commands so a
  replayed group sees the same scope it was checked in.
- Hierarchical group renaming: renaming a group renames its derived names.
- Disable matcher and auxiliary-lemma reuse across groups, so each group owns its
  generated declarations.
- Treat `_hyg` names as group-scoped, never as public names.
- Injective instance naming. Lean's auto-names read only head symbols, so
  `Foo (∀ x : Nat, P x)` and `Foo (∀ s : String, Q s)` both become `instFooForall`.
- Reject or rewrite cross-group references to `private` declarations.
- Export writes explicit instance names, so the stock build does not re-derive them.

## Deferred changes

Kernel-level lazy body loading needs profiling and a separate correctness argument.
GC, changing membership, shared-writer failover and Byzantine storage change the
protocol assumptions and require new models/proofs. Collaborative text editing is
independent of proof-term representation.

Parallelize storage, indexing and proofs after interfaces freeze. Source/frontend
reproducibility is the critical path, and no protocol proof reduces its risk. Add
no new protocol models until P1 has measured capsule sizes and unsupported
frontend effects, except to restate liveness for the hardened protocol. Estimate implementation time only after P1
measures capsule size and unsupported frontend effects.
