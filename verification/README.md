# Verification scope

The checked subject is the abstract distribution protocol. The production Lean
fork, serializer, validator service, source exporter, object-store adapter and
LSP transport are not implemented or verified here.

## Models

- [Registry](tla/Registry.tla): private preparation; validated publication;
  immutable dependencies; causal name heads; conflicts; compatible checkpoints;
  crash/recovery, partitions and eventual anti-entropy.
- [Durability](tla/Durability.tla): stable object writes, write-quorum acknowledgements,
  permanent replica loss and recovery-quorum intersection.
- [Publication](tla/Publication.tla): composition. Publication requires an acknowledged
  package; checkpoint advancement requires an acknowledged manifest. Storage steps
  leave registry state unchanged and vice versa.

Quorums are sets with a supplied intersection member. No numeric majority formula
is used. TLC instantiates three replicas and intersecting two-member sets; Veil
proofs quantify over abstract quorum and replica types.

The registry's `Decls` are immutable revision/package identities. Separate content
deduplication permits reverts without reusing obsolete revision identities.
Valid ancestry must have the same name and be transitively closed. Legal Lean
mutual groups require an atomic implementation mapping; the formal name model
has one name per record. Overlapping multi-name groups and frontend capsules
remain refinement obligations, not results of the one-name model.

## TLC results

Exhaustive finite-state checks ran on the AWS development box with TLA tools
1.7.4, OpenJDK 25 and eight TLC workers. These are full reachable-state searches
for the listed finite instances, not proofs for arbitrary cluster sizes.

| Scenario | Configuration | Distinct states | Checked properties |
|---|---|---:|---|
| Chain | 2 workers, 3 revisions | 125,232 | Admission, closure, acyclicity, snapshots |
| Collision | 2 workers, 2 conflicting revisions | 15,928 | Safety, fair delivery, convergence, eventual collision |
| Revision | 2 workers, upstream edit and old consumer | 174,512 | Safety and no retargeting |
| Revert | 2 workers, 3 sequential revisions | 99,756 | Revert is a new head; no false conflict |
| Rejected | 2 workers, bad proof and cyclic pair | 17 | Nothing invalid/circular admitted |
| Quorums | 3 storage replicas, 2 objects | 439 | Recovery and no acknowledged data loss |
| Integrated | 1 worker, 3 replicas, package/checkpoint objects | 89,428 | Guarded publication and checkpoint recovery |

The suite explores 505,312 distinct states across separate scenarios. Fingerprint
collision estimates, seeds, timings and state counts are retained in the raw logs.
No symmetry reduction or state/depth constraints hide behaviors.

Five reachability witnesses establish that work can publish/commit, conflicts can
occur, storage can acknowledge and disks can fail. Six deliberate mutations must
fail: unchecked preparation, premature acknowledgement, missing recovery fairness,
publication without storage, checkpoint without storage, and silent winner selection.
The harness requires the intended invariant/temporal error, not merely nonzero exit.

The design iteration caught two specification-level gaps: revisions needed distinct
identity from content; and independent storage/registry models lacked acknowledgement
coupling. Revert and integrated cases cover the repaired design. Syntax/tooling
failures were corrected before accepting runs.

## Veil and Lean proofs

Veil is pinned to `d05518f22076b8cc84fb2d2b74d196aa979bfe8f`, using Lean 4.32.0.
This is independent of the proposed fork's nightly compiler. GPT Sol agents authored
the proof modules; the Lean kernel, not agent or SMT assertions, checks their proofs.

| Module | Guarantees |
|---|---|
| [Registry](veil/Paralean/Registry.lean) | Generated-action preservation, reachable validation/closure, immutable compatible snapshots, acyclicity, conflicts block current selection |
| [Durability](veil/Paralean/Durability.lean) | Generated-action preservation, live quorum intersection retains every acknowledged object |
| [Convergence](veil/Paralean/Convergence.lean) | Delivery and convergence over generated registry traces; fixed unsuperseded conflicting pair eventually diagnoses |
| [Composition](veil/Paralean/Composition.lean) | Actual generated component transitions with storage guards; published packages and checkpoint contents/manifests retain recoverable copies |
| [EndToEnd](veil/Paralean/EndToEnd.lean) | Projection of composed traces into registry traces and transfer of temporal guarantees |

The models use explicit theory parameters/hypotheses. No project axioms, incomplete
proofs or trusted SMT verdicts are used. Final theorem audits permit only `propext`,
`Classical.choice`, and `Quot.sound`. [Audit.lean](veil/Audit.lean) additionally scans
the generated project namespaces. Proofs reason about Veil's generated transitions;
they are not proofs of an unrelated handwritten state machine.

Read the component notes for exact theorem statements and mappings:
[registry](veil/REGISTRY.md), [storage](veil/DURABILITY.md),
[convergence](veil/CONVERGENCE.md), [composition](veil/COMPOSITION.md),
[end-to-end projection](veil/ENDTOEND.md).
The TLA/Veil correspondence is documented, not mechanically translated.

## Assumptions and limits

- `Valid` is the trusted checker/policy interface; `Exportable` is the source-build
  interface. The proofs do not implement or verify them.
- Hash/serialization/receipt correctness and stable-write completion are interface
  obligations. The package includes source, body and metadata; the manifest denotes
  its exact contents. Arbitrary mathematical object mappings do not prove this encoding.
- Crash safety tolerates loss only while a recovery quorum survives. New publication
  also needs a usable write quorum. Repair, changing membership and GC are absent.
- Safety permits permanent partitions/crashes. Temporal proofs assume that workers
  eventually remain alive/connected and continuously enabled receives are served.
  Recurrent brief recovery alone is insufficient. There is no latency bound.
- Per-revision delivery needs no finite universe. One global convergence cutoff
  requires finite worker and revision universes. No claim covers an indefinitely
  growing infinite registry with all indexes equal after a fixed time.
- Eventual collision proves a fixed distinct same-name pair with no published
  descendants. Explicit resolution changes that premise. The index conflict is
  proved; emitting a UI diagnostic is an implementation obligation.
- Already committed snapshots remain valid after becoming stale. The current
  registry may report conflicts while an old stock-buildable snapshot remains usable.
- Recoverability proves surviving bytes for known identities. Latest-checkpoint
  discovery, manifest enumeration and writer fencing need implementation contracts.
- Neither proof search termination, eventual draft publication, performance,
  nor adversarial storage/validator correctness is established.

## Reproduce on Linux/AWS

Install Java, Git, curl, elan, Node/npm and Clang as required by the pinned Veil
checkout. Use this repository as the working directory:

```sh
bash scripts/bootstrap-verification.sh
bash scripts/check-tla.sh
bash scripts/check-tla-negative.sh
bash scripts/check-veil.sh
```

Bootstrap verifies the TLA jar SHA256 and pins Veil. Proof checks compile dependencies
before consumers into `.runs/veil`; they do not use stale source-directory objects.
Logs go to `.runs/`. The archived run and source hashes are in [results](results/README.md).

The separate [Lean experiments](../experiments/run.sh) require an installed Lean
binary. Their recorded run used stock Lean 4.34.1. They are not distributed proofs.
