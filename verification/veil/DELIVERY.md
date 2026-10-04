# Packet admission and task completion

`Paralean/Delivery.lean` models transport packets, authenticated validation receipts,
worker sessions and completion of pinned target contracts. Veil generates the
initializer, six actions and labelled transitions. Preservation and reachability
proofs use those generated definitions.

## Request and receipt binding

An immutable request identifies the workspace, worker generation, document and
version, exact environment, target contract, checker and policy. `Envelope` gives
a concrete record representation of those fields. A separate per-node epoch
changes on every start and cancellation, including a restart of the same request.
Node identities distinguish different workers. A replacement that loses its epoch
state must use a fresh node identity.

Acceptance checks the packet's request, recipient and epoch.
It also checks that the authenticated receipt binds that same request, object,
recipient and epoch. Changing a packet's epoch cannot make an old receipt current.
An old worker's packet cannot be accepted by a new worker with the same epoch.
The request fixes a target contract, not a result object. `acceptedObject` records
the exact object from the accepted packet. Another object may satisfy the same
request if its own authenticated receipt establishes that contract.

`receipt_sound` is the checker/signature interface: verifying a receipt establishes
validity of its exact object and satisfaction of its exact request. `intact` denotes
successful complete decoding and integrity checking. Those implementations remain
trusted. The protocol proves that their outputs are bound to the object and request
actually being accepted.

`send` permits arbitrary packets and duplicate sends. `drop` removes a packet.
Any queued packet can be selected next, so delivery order is unrestricted.
Neither action changes checked results or completion. Incomplete or corrupt packets,
unverified receipts, objects mismatched with their receipts, mismatched requests, stale epochs and wrong
recipients cannot take the generated acceptance transition.

## Completion

The immutable `required` relation pins all task contracts. A candidate snapshot
must contain some checked result for every required request, every included group
must have been checked, dependencies must be closed, groups must not overlap on a
name, and the exporter must accept the exact snapshot.

`completion_targets` proves buildability and supplies one object per required
target, with snapshot membership, checked status and contract satisfaction under
the same witness.
`empty_cannot_complete` rejects an empty snapshot whenever any target is required.
`SameArtifacts` ties these facts to an existing group theory; it does not invent
another registry with different dependency or naming rules.

The candidate-level completion action is paired with the actual durable group
commit in [Admission](ADMISSION.md). That composition also requires current local
heads and an acknowledged manifest. Worker crashes invalidate the delivery session.

## Checks

- `accept_enabled_iff` and `finish_enabled_iff` establish both directions of
  generated-action admissibility.
- `reachable_safe` covers all six actions, including loss and session changes.
- `old_response_after_restart`, `wrong_worker_rejected` and
  `relabelled_receipt_rejected` cover generation and recipient errors.
- `nonempty_completion_execution` starts at generated initialization, sends the
  same packet twice, accepts it, and finishes a nonempty required target.
- `alternative_results_complete` in `DeliveryAlternatives.lean` gives two
  executions from the same initial state and with the same
  immutable required request. Each accepts and completes a different object.
- `ParaleanArtifacts.Object` separates package, manifest and numeric catalog identities by
  constructors. [Admission](ADMISSION.md) uses those constructors as its actual
  storage mappings and proves injectivity and cross-kind separation.

The proofs establish safety under arbitrary transport loss. They do not promise
progress under permanent packet loss, cancellation or an unfair scheduler.
Group discovery retains the explicit fairness assumptions proved in
[Groups](GROUPS.md). Kernel checking, cryptographic verification, byte decoding,
frontend capture, source export and actual LSP transport remain implementation
interfaces. No source exporter or distributed Lean service is implemented here.
