# Registry and storage composition

`Paralean/Composition.lean` closes the modeled publication/storage coupling.
Its state is a product of the Veil-generated registry state and storage state.
Its steps invoke the generated component `Next` relations. They do not substitute
an independent handwritten implementation of either component.

The immutable interface maps declaration IDs to stored package objects through
`payload`, and snapshot IDs to stored checkpoint objects through `manifest`.
For TLA `Publication`, instantiate snapshot values as declaration subsets and
use the same `Payload` and `Manifest` functions.

## Coupled transitions

A registry transition leaves storage unchanged. A generated registry `publish`
action additionally requires acknowledgment of `payload d`. A generated `commit`
action additionally requires acknowledgment of `manifest S`. Other registry
actions retain their original guards. A generated storage transition leaves the
registry unchanged. Stuttering leaves both components unchanged.

Initialization invokes both generated initializers. The baseline empty snapshot
has no manifest requirement. Any explicit commit, including an empty-snapshot
commit, requires an acknowledged manifest. Nonempty committed heads always have
an acknowledged manifest.

`Safe` combines the component safety predicates with these two coupling facts:

- Every published declaration's package object is acknowledged.
- Every head differing from `emptySnapshot` has an acknowledged manifest object.

`storage_acknowledged_mono` proves acknowledgment persistence from the generated
storage actions. `registry_preserves_coupling` proves that generated registry
actions maintain coupling when their extra guards hold. `initial_safe`,
`next_safe`, and `reachable_safe` establish the combined invariant for every
finite execution, including arbitrary interleavings and stuttering.

## Recovery guarantees

The following theorems apply to every combined reachable state:

- `published_recoverable`: every published package is stored at the write/read
  intersection in every entirely live recovery quorum.
- `published_has_copy`: every published package has a surviving copy.
- `checkpoint_manifest_recoverable` and `checkpoint_manifest_has_copy`: every
  nonbaseline checkpoint manifest has the corresponding recovery guarantees.
- `checkpoint_declaration_recoverable` and `checkpoint_declaration_has_copy`:
  every declaration selected by any checkpoint has those package guarantees.

The final pair uses the registry invariant that snapshot contents are published.
All dependency-closure members belong to those contents, so their package objects
are covered too. A manifest and different packages may survive on different
replicas; the theorems do not require one replica to hold the entire checkpoint.

## Remaining interfaces

This is a protocol composition proof. It does not verify a storage client,
serialization, package extraction, validator, source exporter, or network stack.
The package mapping must identify the validated declaration, its source capsule,
receipt, and required metadata. The manifest mapping must identify the encoded
snapshot contents. Those representation/refinement contracts remain implementation
gates. Correct object mappings are not established by treating arbitrary mapping
functions as injective, and no cryptographic implementation is proved here.

Recovery is retrieval given an object's identity and the stated quorum interface.
Finding the latest workspace checkpoint after losing the worker, persisting its
mutable head locator, and enforcing fenced workspace ownership remain separate
interfaces. The registry's preserved head value is not a proof of those services.

The surviving-recovery-quorum failure envelope is inherited from the storage
component. No delivery or fairness assumption is required for these safety
results. Continued publication additionally requires a usable write quorum;
repair, membership changes, and garbage collection are outside the model.

## Validation

The source audits initialization, preservation, reachable safety, and every
recovery/copy theorem with `#print axioms`. The proof uses generated component
semantics and their kernel-checked bridges. No SMT verdict is used as a proof.

Checked with Lean `4.32.0` and Veil commit
`d05518f22076b8cc84fb2d2b74d196aa979bfe8f`. Every audited theorem reports only
`propext`, `Classical.choice`, and `Quot.sound`. The generated component bridges
and preservation proofs are covered transitively by these audits.
