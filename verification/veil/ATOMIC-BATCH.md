# Atomic multi-group publication

`Paralean/AtomicBatch.lean` (`ParaleanAtomicBatch`) models a batch (store.md T12) as a
nonempty run of hardened steps (`Run`) observed as one step (`Commit`). Its members are
the T1/T8 bodies a single transaction runs in order; nobody observes the states between
them.

- `run_reachable`, `commit_reachable`, `breachable_iff`: runs whose transactions are
  hardened steps or batch commits (`BReachable`) reach exactly the hardened reachable
  states. A batch refines a sequence of hardened steps, so `hardened_safe` and every
  other hardened theorem hold for runs with batches.
- `batch_published_receipted`, `batch_no_target_collision`: fixes 1 and 2 for such runs.
- `run_published_mono`, `commit_publishes_members`: publication is monotone along a run,
  so every group published by any member is published when the batch commits. Observers
  see the state before or after the commit: none of the batch or all of it.
- `pairs`, `run_pairs_next`, `stale_member_blocked`: every member step is a hardened step,
  so no member newly publishes a target proof from a pending bit prepared under an older
  owner epoch (`ParaleanTargetNames.stale_publication_blocked`).

## Not established

- Readers spanning several transactions (paginated scans, anti-entropy, working copies)
  and the staged protocol for oversized batches are checked only in TLA
  (`verification/tla/AtomicBatch.tla`).
- The single-transaction guard of T12 is not derived from Rust; the argument is store.md's
  "Atomic transactions as step sequences".

Axioms: `propext`, `Classical.choice`, `Quot.sound` only (Audit).
