# W3: store and registry features

Branch `w3-store-features`, based on `fee94d9`. Work began 2026-10-20.
Implementation and tests are delegated to three GPT-6 Sol agents with disjoint
feature scopes; the primary agent reviews and integrates them.

## Decisions

**OPEN-19:** retain author deletion and add controller-authorized deletion.
Controller authorization binds the exact tombstone identity and source fence
rank. The source transaction checks that rank against its current fence.
Historical replication retains the original authorization and source
certificate; a receiver does not reinterpret it against its independent fence.
Agent identity is an explicit controller-signed association between an AgentID
and a workspace signing key, checked at publication/deletion transaction
boundaries, with rotation and revocation.
The issuing controller must be the workspace's pinned home controller. A trusted
peer's controller cannot register or rotate another workspace's author key.
Rotation preserves the old public key for checking historical certificates;
revocation prevents new admissions rather than erasing existing publications.

**OPEN-20:** v0 supports same-file moves: delete an exact insertion position and
insert the same group at a new anchor. Revisions and lineage keys retain their identities.
Among remaining certified positions, the least `(lamport, author, marker ID)`
is selected deterministically. A legacy group-targeted tombstone retains its
old encoding and meaning; a position-specific tombstone appends its marker ID.
New move operations require a certified position-specific deletion.
An author cannot undo a controller deletion by using it as move authorization.
Cross-file moves remain outside this decision: file-scoped tombstone and anchor
authority needs a separate rule. Derived names follow their renamed parent
namespace, using a reserved suffix with the **full** group ID to avoid
truncated-ID clashes.

**OPEN-26 remains closed to unresolved renames:** rendering a collision does not
authorize committing it. Duplicate selected names fail buildability; known live
competing heads fail currentness. Tombstones affect file positions and live name
candidates, not immutable registry objects or historical snapshot contents.

## Models and implementation

- `CheckpointConflicts`: exhaustive finite checkpoint rejection, plus Lean
  theorems over generated group commit steps. The T5 guard reads registry metadata
  in its commit transaction, including calls through `commit_record`. Partial
  selection of an atomic group's revisions is rejected; signed job dependency
  capsules must be represented by completely selected groups.
- `StorePositions`: registry-neutral tombstones, independent per-replica
  certificates, position selection and deterministic rendered names.
- `AgentAuthority`: agent registration, rotation/revocation and fenced controller
  deletion. This finite model abstracts trusted registration and original-source
  evidence; it checks authorization at the admission event. It does not model
  the complete historical T10 relay protocol or cryptographic key encoding.
- `CatalogueExchange`: source-qualified catalogue copies, local payload
  acknowledgement, parent closure, source proof and independent local fences.
  Its fair finite instance checks eventual dissemination.

Inspection found that base `fee94d9` already implements catalogue transfer in the
network anti-entropy service, including relay with the original source proof.
W3 retains that implementation and adds a model, adversarial fixtures and
guard-removal mutations. Foreign catalogue records stay in the source-qualified
`xcatalog` namespace; they never become local commits. In-process legacy
`antientropy::export` is not the network service.

The controller APIs are `Controller::register_agent_key` and
`Controller::revoke_agent_key`; key-file rotation uses
`KeyFile::rotate_workspace_key`, with signed public grants retained in worker
key files. Registration and revocation are per-deployment controller API
operations; peers need the signed grants and public-key history in their
configuration. There is no new agent-registry anti-entropy wire protocol or
standalone register/rotate/revoke CLI. Existing key files must be provisioned
with signed grants before admitting new publications.
The remote CLI exposes controller deletion through
`plr tombstone ... --controller` using a controller key file. Working-copy moves
use `impl/p3-remote/scripts/ws.py move DIR FILE NAME [AFTER]`, with pending
arguments persisted for retry after an interrupted delete/reinsert.
Target-name groups retain P2's `TombstoneOfTarget` rejection for both author and
controller deletion; deleting target ownership requires a separate target-state
transition.

Marker variants converge when their immutable group, revision, author and
lineage fields agree. Each placement/receipt variant retains its own certified
marker identity; incompatible immutable fields still produce a conflict.
Tombstoned positions remain valid RGA anchors.
An already committed move is recognized from its stored marker and verified
local certificate before checking a key's present admission status, so an
unknown-outcome retry still succeeds after revocation. Its certified anchor
remains usable after an anchor tombstone, including on a later retry.

Controller-deletion receive and audit bind the source certificate's writer to
its pinned controller, including legacy `KeyRing::trust` deployments without a
federation roster. A peer-signed grant cannot change that ownership. Deployments
sharing one controller key still have independent fences; historical receive
uses the source authorization rather than the receiver's fence.

## Verification environment

Only W3-owned instances are used: `PARALEAN_INSTANCE=w3` (ports 25300–25350)
and `w3-peer` (25400–25450). TLC and Veil dependencies are private to this
checkout. Builds use a single job/thread where supported. Initial free space
on `/data` was 244 GiB. No shared Mathlib cache is modified.
Both W3 store instances were stopped after the runtime suites completed; their
data is retained. The final two independent TLC cases use three workers each,
with no concurrent build/test processes.

The four new default TLC instances completed with 321 distinct states for
`CatalogueExchange`, 6,065 for `CheckpointConflicts`, 384 for `AgentAuthority`,
and 258,505 for `StorePositions`. The full default positive suite has 25 cases.
The complete 100-case negative suite was followed by the additional
`position_registry_erasure` case against the same frozen TLA sources; the
combined 101-case manifest retains each run's checked-source provenance.
All 29 hardened cases completed with their expected outcomes, including the
last redundant-guard case's 7,628,232 distinct states. Four unchanged wide
results were retained from the base archive; they were not rerun. Their parsed
source/config hashes still match. Both `scripts/archive-verification.sh
--tla-only` and the full archive command succeeded, followed by a passing
`scripts/archive-verification.sh --verify` covering 25 default positive,
101 negative/expected-outcome, four wide and 29 hardened logs.

The T5 implementation deliberately fails closed if a registry prefix exceeds
10,000 metadata rows or contains an offloaded metadata envelope that cannot be
read inside its FDB transaction. This is an availability limitation: it can reject
a valid checkpoint, but cannot let an unresolved checkpoint through. Lifting it
requires a transactional index of certified group names and ancestry. The Lean
theorem concerns generated protocol commit steps; this work does not claim a
machine-checked refinement from the Rust implementation.

## Implementation evidence

- `results/w3/store-tests.log`: 123 passing tests across the P2/workspace test
  binaries, including 17 network, 17 guard, nine authority, six tombstone and
  ten anti-entropy tests. Property tests use their default 12 generated cases.
  A subsequent anchored-move retry regression is included in the final
  11-test position suite (`positions-final.log`).
- `results/w3/control-tests.log`: 37 exercised controller tests pass. Cargo
  reports 38 because the optional fork test returns early without a configured
  fork; the two benchmark tests remain explicitly ignored.
- `results/w3/mutations-{main,extra}.log`: 49 guard-removal cases detected
  (44 in the main run and five added during review). The certified-anchor
  mutation is also rerun after the anchored-retry correction.
- `results/w3/{move-gate,collision-gate}.json`: real working-copy move and guided
  collision-resolution/checkpoint gates pass against W3's own stores, including
  Lean compilation. P1 builds and Python syntax checks also pass.
- All 30 Lean verification modules compile; the audit checks 7,264 project
  declarations using only permitted stock Lean axioms. The new universal
  checkpoint-rejection theorem is included in that audit.

The optional broad stock P1 core export attempted while preparing controller
test inputs did not pass: it reports initializer/generated-name mismatches.
Its diagnostic log is retained as `results/w3/stock-core-export-diagnostic.log`;
no full P1 export or fork validation is claimed. The required controller input
stores were populated, and the controller tests and W3 working-copy gates above
passed.

## Proposed sentences

- `plan.md`: “W3 adds transactional checkpoint collision rejection,
  controller-authorized deletion, agent-key registration, position moves and
  rendered names; its models and guard-removal tests are recorded in
  `docs/w3-log.md`.”
- `README.md`: “Store/registry feature evidence and OPEN-19/OPEN-20 decisions:
  `docs/w3-log.md`.”
