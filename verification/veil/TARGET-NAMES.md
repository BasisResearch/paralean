# Alternative proofs of one required target

In the joint protocol, two independent proofs of a target are distinct groups that
declare the same name without revising each other, so
`ParaleanGroups.Trace.eventual_name_collision` blocks every commit containing that name, and
`Delivery.realizes` never constrains the name. `Paralean.TargetNames`
(`ParaleanTargetNames`) adds a guard and fenced ownership state to `ParaleanProtocol.Next`.

## Assumptions (`TargetAssumptions a`)

`targetName : request → name`; `pinned`: `realizes o q` with `q` required implies
`member o (targetName q)`. `IsTarget x` means `x = targetName q` for some required `q`.
Ownership is not an assumption: it is state.

## Ownership state (`Extra node group name`)

- `owner x : node` and `epoch x : Nat`, the current owner and owner epoch of each name.
- `head x : Option group`, the latest published proof of `x`. It lives in the same store
  record as `owner x` and `epoch x`.
- `preparedEpoch n d x : Nat`, the epoch of `x` under which the pending bit `(n, d)` was
  created. It is per node because the base protocol lets the same group be pending at
  several workspaces.

`Initial` requires no recorded head (`head = fun _ => none`) and leaves owners and epochs
arbitrary; `initExtra o` (owner `o`, all epochs `0`, no head) is the usual choice.

## Guard

A step satisfies `Guard s e t e'` iff one of:

1. Protocol step: `PrepareOk ∧ PublishOk ∧ e' = update a ta s t e`.
   - `PrepareOk`: if `pending n d` is newly set and `d` declares target name `x`:
     (i) `n = e.owner x`; (ii) `revisions d h x` where `e.head x = some h` and `h ≠ d`;
     (iii) `n` has no other pending `h ≠ d` declaring `x`. It reads the name's store record,
     the immutable theory and `n`'s own pending set. It does not read `published`.
   - `PublishOk` (the fence): if `d` is newly published from `n`'s pending bit and declares
     target name `x`, then `e.preparedEpoch n d x = e.epoch x`. This models the publication
     marker write as a conditional write on the owner epoch held in the store, the same
     primitive as catalogue fencing.
   - `update = advance ∘ stamp`. `stamp` records `e.epoch x` as `preparedEpoch n d x` for
     each newly pending `(n, d)`. `advance` sets `head x := some d` when the step newly
     publishes `d` declaring target name `x` (`NewTarget`): the fenced marker write and the
     head update are one conditional write on the record.
2. Reassignment: `t = s` and `e' = reassign e x n`, which sets `owner x := n` and
   increments `epoch x`; `head` is kept. It may happen at any time; the old owner need not
   be quiescent.

A group declaring several target names must be prepared by the owner of all of them
(`split_owner_unpreparable`). This is a controller constraint: target names declared by
one group are assigned and reassigned jointly.

## Results

- `reachable_inv` (needs `ParaleanAdmission.Assumptions`): inductive invariant over the real
  joint `Next` with arbitrary reassignments. Recorded epochs never exceed the current epoch.
  A *current* pending proof (recorded epoch equals the current epoch) is at the current
  owner, revises the recorded head of its name, and is the owner's only current pending
  proof of it. The recorded head is a published proof of the name, and every published proof
  of the name is the head or is revised by it. Published target proofs form a chain.
  Pending groups are valid, and `valid_ancestry` makes revision transitive for valid groups,
  so revising the head revises everything below it. Reassignment makes every pending proof
  of the name stale, which is why a zombie owner and a new owner never break uniqueness.
  Step facts used: `published_step_shape` (publication is monotone, a step publishes at most
  one new group, a step creating a pending bit publishes nothing; via `groups_pending_source`).
- `recorded_head_tops_chain`: the invariant's head clauses, exported.
- `target_chain`, `realized_chain`: any two published groups declaring a target name (or
  realizing one required request) are equal or one revises the other.
- `target_head_unique` / `no_target_collision`: at most one `isHead` per node and target
  name; `collision_premise_fails` refutes the `unsuperseded` premise of
  `eventual_name_collision` for distinct published target proofs.
- `stale_publication_blocked`: a step newly publishing `d` from a pending bit whose
  recorded epoch is not current fails the guard. Immediate from `PublishOk` (definitional).
- `split_owner_unpreparable`: definitional consequence of conjunct (i).
- `guard_observable`: for a `prepare n d` step, the guard with the updated state is
  equivalent to a check of the store record of each declared name (owner and recorded
  head), the preparer's own pending set and the immutable theory. It has no reachability,
  scan or assumption premise: no published set, scan or ghost acknowledgement is read.
  `common_owner_preparable` is its converse direction: a multi-target group whose names
  share one owner is admitted when that owner prepares it, revising each recorded head.
- `Example.alternatives_complete`: a concrete joint run in which owner `false` publishes
  proof `false` and then proof `true`, which revises it; both get accepted checked receipts
  and the catalogue-guarded finish/commit completes with the unique head `true`.
- `Example.handover_witness`: owner `false` prepares proof `true` at epoch `0`; the
  controller reassigns name `2` to worker `true` (epoch `1`); the record keeps head `false`.
  The old owner's publication is a base joint step but no guarded step admits it. The new
  owner reads the record, receives proof `false`, prepares proof `true` revising the recorded
  head (an existing published proof, `PrepareOk` holds) and publishes it under epoch `1`,
  which sets the head to `true`, while the zombie still holds its stale pending bit; worker
  `true` has the unique head.
- `Example.guard_necessity`: the base `ParaleanProtocol.Next` lets worker `true` prepare and
  publish a second, non-revising proof, giving two heads, failing `current` and blocking
  commit and guarded finish. The guard rejects that prepare under every ownership state
  whose record holds the published proof as head (it violates the revise-head conjunct).
  Per-conjunct necessity is checked in TLA+ (below).
- `Example.scan_check_unsafe` (necessity of the head record): `ScanPrepareOk ids` is the
  previous check with the published set replaced by a scan `ids`. A certificate scan only
  guarantees `CertQuorum ⊆ ids ⊆ published` (`AckCertificates.scan_between`), so before any
  certificate quorum the new owner's scan may be empty. With owner A = worker `false` having
  published proof `false` and the name reassigned to B = worker `true`, `ScanPrepareOk ∅`
  admits B's non-revising proof `true`, and the base protocol reaches two heads. In every
  target-reachable state of that instance in which `false` is published the record holds
  head `false`, and the guard rejects B's preparation for every such record.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.

## Atomicity of the record read

`PrepareOk` reads owner, epoch and head in the same state as the preparation. In a real
store the read comes first. Only current proofs publish and they exist only at the current
owner, so between the read and the preparation the head can move only if the owner itself
publishes another proof of the name, or the name is reassigned. A reassignment makes the
new proof stale and its publication is fenced. The owner's own publication must not
interleave: the owner serializes reading the record, preparing and publishing for one name.
Alternatively the publication is conditional on the head that was read as well as the epoch
(compare-and-swap on the record). Neither variant is modelled separately; the Lean step and
the TLA+ `Prepare` read and prepare atomically.

## TLA+

`verification/tla/Targets.tla`: 2 workers, one target name, 3 proof IDs, up to 2
reassignments (`MaxEpoch = 2`), crash. Ownership and epoch are variables; `Reassign(w)` may
fire at any time. The store record is `owner`, `epoch` and `recHead`. `TargetGuard` =
`OwnerOK ∧ RevisesHead ∧ NoOtherPending`, where `RevisesHead(R)` reads `recHead` only;
`Prepare` also requires `Closed(R)` (revision sets are transitively closed, the TLA
counterpart of `valid_ancestry`). `Publish` requires `EpochOK` and sets `recHead`
(`HeadUpdate`). `TypeOK`, `TargetChain`, `HeadUnique` and `RecordTopsChain` hold (419214
distinct states, the same reachable graph as the earlier global-`published` guard: under
`RecordTopsChain` and closure, revising the head is revising every published proof).
Witnesses (must be violated): `NeverAlternativeCommitted` (two proofs published, a commit
selects the latest) and `NeverHandover` (after reassignment the old owner holds a stale
unpublished proof while the new owner has published a revision under the current epoch).
Mutations, each violating `TargetChain`: `target_no_owner_check` (`OwnerOK` → `TRUE`, two
workers prepare concurrently), `target_no_revise_head` (`RevisesHead` → `TRUE`),
`target_scan_subset` (`RevisesHead` replaced by revising some subset of `published`, i.e.
a scan that may miss proofs without a certificate quorum), `target_no_head_update`
(`Publish` leaves `recHead` unchanged), `target_no_single_pending` (`NoOtherPending` →
`TRUE`), `target_no_epoch_fence` (`EpochOK` → `TRUE`, zombie publishes after reassignment
and after the new owner's proof). No conjunct is redundant.

## Not established

- The controller is trusted to assign jointly the names declared by one group; the model
  only shows that a group with split owners cannot be prepared.
- Owner liveness: nothing guarantees that an owner, or a new owner after reassignment,
  eventually prepares a revising proof. A stale pending proof blocks its holder from
  preparing another proof of the name until it crashes (conjunct (iii) is over all pending
  proofs, not just current ones); this costs liveness only.
- Revisions are immutable theory data. The guard checks only that the declared revision
  edges exist; it does not show that a proof is better than the one it revises.
- Any group declaring a target name is guarded, whether or not it realizes the request.
- The TLA+ model has one target name; multi-name groups are covered only in Lean.
- The record read and the preparation are one atomic step (above); a delayed read is
  argued informally, not modelled.
- Liveness after reassignment: the new owner must know the recorded head to revise it
  (`prepare` requires known ancestors), so it must first receive it. Under the hardened
  receive guard that needs a certificate on a live replica; until one exists the new owner
  is blocked. Safety does not depend on it.
