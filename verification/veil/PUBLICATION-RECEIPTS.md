# Publication gated by validator receipts

`Paralean.PublicationReceipts` (namespace `ParaleanPublicationReceipts`) layers a
guard over `ParaleanProtocol.Next`. In the base model `ParaleanGroups.prepare`
requires the oracle `valid d`, which the publishing worker evaluates itself. A
buggy or Byzantine worker is excluded only by that assumption. The hardened
`Next` alone does not change this, because it still uses base `prepare`. The
untrusted-worker system below removes the validity check from the worker and
shows that the guard plus `receipt_sound` replaces it.

## Guard

`Extra := Unit`. A step that newly creates `pending n d` (present in `t`, absent
in `s`) requires `HeldReceipt a s.admission.delivery d`: some packet `m` is in
flight, `verified m`, `intact m` and `receiptObject m = d`.
`Next (s,e) (t,e') := ParaleanProtocol.Next a r encode s t ∧ Guard a r encode s e t e'`.

## Untrusted workers

- `unchecked th` is the registry theory with `valid` replaced by the constant
  `true`. `UntrustedPrepare a n d s t` is the generated prepare transition under
  `unchecked a.registry`, lifted through the protocol state (delivery, storage
  and recovery unchanged). It keeps every requirement of base `prepare` except
  `valid d`: `alive n`, dependencies and ancestors known, no self edges
  (`untrusted_prepare_enabled_iff`). A worker that skips or misreports validity
  is therefore expressible.
- `UStep := ParaleanProtocol.Next ∨ UntrustedPrepare`, `UNext := UStep ∧ Guard`,
  `UReachable` its reachable states. `RawReachable` is `UStep` without the guard.

## Claims (all proved over the real `Next`, axioms: propext, Classical.choice, Quot.sound)

- `published_receipted`: in every hardened-reachable state, each published group
  and each staged group has a verified, intact receipt whose object is that
  group. No assumptions are used.
- `unreceipted_never_published`: a group with no verified intact receipt is never
  published.
- `receipt_implies_valid`: `receipt_sound` + `Compatible` give `registry.valid d`.
- `invalid_never_published`: from receipts alone (not the registry invariant).
- `prepare_enabled_iff`: a fresh hardened prepare of `(n,d)` is enabled iff the
  worker holds a receipt for `d`, `alive n`, all deps and ancestors are known,
  and there are no self edges. `valid d` is absent from the right-hand side
  because the receipt implies it; base `prepare` still evaluates it.
  `valid_guard_redundant` states the same for any step.
- `untrusted_step_is_protocol_step`: from a state satisfying the receipt
  invariant `Inv`, an `UntrustedPrepare` step that passes `Guard` is a genuine
  `ParaleanProtocol.Next` step. `receipt_sound` recovers the skipped `valid d`
  (a re-prepare of an already staged pair uses `Inv` instead of the guard).
- `ureachable_iff`: under `Assumptions`, `UReachable ↔ Reachable`. Every hardened
  theorem therefore holds with untrusted workers.
- `invalid_never_published_untrusted`: with untrusted workers under the guard,
  every published group and every staged group is valid and receipted.
- `guard_necessary`: for any theory satisfying `Assumptions`, an invalid group
  with no dependencies or ancestors is staged by an untrusted worker in one
  unguarded step from any initial state (`RawReachable`), and is never staged or
  published in `UReachable`.
- `guard_stutter`, `reachable_protocol`: every base theorem transfers.
- `Example.receipted_publication_reachable`: a concrete trace over the
  `CompletionRecoveryExecution` instance. A worker receives a receipt packet for
  the helper group, stages that group under the guard and atomically publishes it.
- `Example.untrusted_publication_reachable`: the same run in `UReachable`, with
  the helper group staged by an `UntrustedPrepare` step admitted by the guard.
- `Example.untrusted_invalid_staged_without_guard`: a theory satisfying all
  `Assumptions` in which group `false` is invalid and dependency-free and the
  validator signs only `true`. The unguarded untrusted system stages `false`;
  the guarded one never stages or publishes it (non-vacuity of `guard_necessary`).
- `Example.base_publishes_unreceipted`: with `verified := false` (all
  `Assumptions` hold) base `Next` publishes the valid helper group with no
  receipt; the hardened model never does.

## Trust boundary

The trust boundary is exactly `receipt_sound`: a verified receipt names a valid
group. Implementations discharge it by an unforgeable validator signature over a
payload that binds the exact group content, with the group ID a content hash.
Receipts are statements about content, not about who presents them: `send m` is
unconstrained, so any actor (including another worker) may put any verified
receipt in flight, and any worker may stage a group using a receipt it did not
request. This is intended, not a gap, since the receipt is valid for that
content whoever holds it.

## Implementation contract

A worker stages a group only while holding an intact, verified validator receipt
for that exact group ID. It checks the signature and need not evaluate validity
itself. The receipt's signed payload must include the policy version and the
checker version used, and the publisher must reject receipts for versions other
than the pinned ones.

## Not established

- Binding to request, epoch, worker, policy or checker version: any intact
  verified receipt naming `d` suffices. Requests are opaque, and the
  version binding above is an implementation obligation that is not modelled.
- Validator signature unforgeability and content hashing are assumed through
  `receipt_sound`, not proved.
- `untrusted_step_is_protocol_step` needs `Inv` on the pre-state; it is used
  only for reachable states, where `published_receipted` supplies it.
- The guard fires only on newly staged entries (re-prepare is safe by `Inv`).
- `HeldReceipt` reads `flight` as the worker's receipt buffer (no per-worker inbox).
- Base `prepare` keeps its `valid d` conjunct; the untrusted system is a
  separate, larger transition relation shown to have the same reachable states.
- Untrusted workers are modelled only at staging. A worker that publishes
  without staging, or corrupts storage, is outside this model.

## TLA+

`verification/tla/Receipts.tla`: 2 workers and groups `a`, `b` (deps `a`) and an
invalid `bad`. Workers are Byzantine in the sense above: `Prepare` checks only
that dependencies are published and that the worker holds a receipt for the
group (the guard), never validity. This matches `UntrustedPrepare ∧ Guard`.
The validator signs only valid groups with published deps. `Publish` requires
the group to be staged by that worker, as base publish does. Receipts are held
per worker and lost on crash, which only restricts the guard relative to the
Lean `flight`.
TLC finds 181 distinct states, depth 15, with `PublishedValid`,
`PublishedReceipted`, `DepsClosed`, `StagedReceipted` and `StagedValid`
holding. The witnesses `NeverValidPublished` and `NeverDependentPublished` are
violated as expected. Mutations: dropping the staging guard violates
`StagedValid` (`unreceipted_staging`: a worker stages `bad`) and, with the
staged invariants and the trivially broken `PublishedReceipted` removed,
`PublishedValid` (`unreceipted_publication`: a worker publishes `bad`).
