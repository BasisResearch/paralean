# Catalog recovery

`Paralean/Recovery.lean` closes recovery after losing the desktop's last checkpoint
ID. It uses Veil-generated transitions and the actual generated Durability store.
It imports the atomic group registry. Buildability checks validity, dependency
closure, per-name group exclusivity, and exportability.

## Persistent data and volatile state

Immutable catalog records identify a workspace, exact snapshot, causal parents,
transitive ancestry, and rank. The store has distinct typed object roles for group
packages, snapshot manifests, and catalog records. The concrete execution uses
`ParaleanArtifacts.Object.payload`, `.manifest`, and `.catalog`. `ofAdmission`
uses the actual receipt/admission protocol maps; `ofAdmission_objects_separate`
proves role separation for injective encoded catalog IDs.

Desktop loss clears the local known catalog, head set, selected ID, reconstruction
status, and writer authorization. It retains no usable local record ID. Durable
records and acknowledged bytes persist under the existing failure envelope.

`record` denotes decoded, schema-validated metadata. The ancestry assumptions
require decreasing ancestry ranks, parent inclusion, transitivity, and a parent
edge justifying every ancestry edge. `RecoveryAncestry.lean` proves that these
conditions make ancestry exactly nonempty parent-path reachability. Malformed
bytes and malformed ancestry are rejected by the decoder before this domain.
These schema checks remain an implementation interface. They are not inferred
from an arbitrary unvalidated record.

## Physical scanning and adoption

A scan value contains the raw decoded catalog and results of storage readiness
checks. `PhysicalScan` equates the raw catalog with actual record-object presence
in the union of a surviving read quorum. It does not inspect a global committed
bit or infer acknowledgment from staged bytes.

`ReadyScan` equates readiness with actual acknowledgments of the catalog object,
its exact manifest, and every package in the snapshot. The adapter may reestablish
these acknowledgments before adoption. `physical_scan_ready_for_committed` derives
coverage and readiness for all retained records from the maintained storage
coupling and the generated durability quorum theorem.

`admissible` computes the accepted catalog. It checks raw presence, readiness,
workspace identity, buildability, and the same checks for every causal ancestor.
Unready, nonbuildable, and wrong-workspace staged records remain excluded. They
do not block a valid durable checkpoint. `enumerate` adopts exactly this computed
set, including safely reacknowledged staged historical data.

The generated enumeration coverage guard is the scan adapter specification.
`physical_enumeration_enabled` discharges it from actual stored objects and the
complete physical scan, then constructs the generated enumeration step. It proves the exact accepted
output and preserves writer authorization and fence.

## Heads, conflicts, and selection

`reconstruct` computes every maximal causal record in the accepted catalog.
`reconstruction_iff` proves both soundness and completeness.
`conflict_iff` reports exactly the presence of distinct heads.
`reconstruction_parent_iff` and `parent_conflict_iff` state the same guarantees
directly over parent paths. `parentless_records_conflict` excludes fabricated
ancestry hiding a conflict between retained records with no parent edges.

Automatic selection requires a unique head. `automatic_no_silent_winner` proves
that automatic selection cannot conceal a conflict. Explicit historical selection
can choose any accepted checkpoint while preserving the reconstructed head set
and conflict report.

Recovery adoption and historical selection are read operations. They do not
publish a new writer checkpoint, grant a lease, or advance a workspace alias.
Buildable staged data from an obsolete worker may be adopted as historical data
only after its storage readiness is reestablished. Direct checkpoint publication
uses the fenced `commit` action; `stale_writer_rejected` rejects old tokens.

The model has one writer per workspace. `rotateFence` denotes an external atomic
exclusive lease service and accepts only a greater token rank. Recovery does not
supply this service. A replacement lacking it starts with a fresh workspace
identity. Timeout alone does not confer ownership.

## Dynamic composition

`CoupledNext` interleaves generated storage and recovery actions. Record publication
pairs generated recovery commit with generated storage acknowledgment. Payload
and manifest acknowledgments are checked against the actual store. Storage can
stage or acknowledge candidates before recovery adopts them.

`Coupled` requires every retained record, its manifest, and all snapshot packages
to be acknowledged. `Compatible` identifies the exact validity, dependency,
name membership, contents, and exportability interpretations used by recovery and
the atomic group registry. `ObjectsSeparate` prevents storage role aliasing.

Initialization, every generated recovery action, generated `Next`, storage
interleavings, coupled transitions, and coupled reachable states preserve their
invariants. `coupled_selected_has_copies` supplies surviving record, manifest, and
package copies. `coupled_selected_buildable` gives buildability in the actual
group registry's interpretation.

## Execution witness

`coupled_nonempty_lose_id_execution` starts with the actual generated initializers.
It puts and acknowledges package, manifest, and catalog bytes; publishes a fenced
checkpoint; stages an unready second catalog record; destroys a replica; selects
the checkpoint; loses the desktop's ID and local catalog; scans the surviving
quorum; and selects the same nonempty exact snapshot again.

Physical scanning and readiness are proved against the concrete surviving store.
The unready staged record is ignored. Writer authorization remains false after
recovery. This is a complete storage/protocol execution, not an assumed result.

## Implementation boundaries

Hash-verified stable writes, truthful acknowledgments, exact object-to-byte
mappings, complete quorum enumeration, schema validation, and exclusive lease
rotation remain implementation contracts. The failure envelope must leave a
recovery quorum alive. Network progress requires eventual service. Garbage
collection, membership changes, and Byzantine storage are outside this model.

Kernel validation uses Lean 4.32.0 and pinned Veil. Audited declarations must use
only `propext`, `Classical.choice`, and `Quot.sound`. No SMT verdict, native
decision oracle, new axiom, or incomplete proof is accepted.
