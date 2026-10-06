# Protocol proof obligations

This extension addresses the protocol gaps identified in the review of the
README and implementation plan. Each completed claim requires a checked consumer
over the actual generated transitions, an explicit assumption boundary and a
nonempty execution or enabledness theorem.

| Obligation | Proof or check |
|---|---|
| Atomic groups with overlapping name sets | `Groups`: membership, per-name causal heads, closure and group commit |
| Preserve storage and convergence when using groups | `ParaleanGroupComposition`: generated component transitions and trace projection |
| Reject corrupt, stale, misaddressed and mismatched responses | `Delivery`: exact packet/receipt/request/node/epoch checks |
| Reject empty or incomplete task completion | `Delivery`: every immutable required contract must have a selected checked result |
| Allow different proofs of one fixed target | `DeliveryAlternatives`: two distinct accepted objects complete the same required request |
| Bind completion to actual durable/current commit | `Admission`: paired finish and guarded group commit |
| Require a discoverable catalogue entry before completion | `CompletionRecovery`: same-store catalogue guard, exact image/workspace, required-target recovery after failures |
| Rediscover publications after every worker index is erased | `PublicationDiscovery`: durable typed markers, physical quorum scan, guarded generated receive |
| Enforce catalogue and discovery guards together | `Protocol`: shared-store composition of both extensions |
| Exercise both guards before loss and recovery | `ProtocolExecution`: joint initial state, helper/target publication markers, matching catalogue, completion, disk/desktop loss and exact recovery |
| Record the cases the new guards reject | `ProtocolGuardChecks`: missing catalogue, mismatched image and absent publication-marker cases. These restate the guards; they are not necessity proofs |
| Invalidate pending responses on actual worker crash | `Admission`: paired group crash and delivery cancellation |
| Prevent package/manifest object aliasing | Typed constructors consumed by `Admission.protocolTheory` |
| Lose the local checkpoint ID and recover through a catalog | `Recovery`: physical quorum scan, candidate validation, causal reconstruction and selection |
| Handle staged catalog entries and stale writer tokens | `Recovery`: admission/re-acknowledgement and fencing. Its readiness test reads ghost acknowledgement; see `CatalogCertificates` |
| Reconstruct history from recorded parents | `RecoveryAncestry`: exact parent-path ancestry, head and conflict equivalences |
| Combine receipts, group admission, completion and disk loss | `AdmissionExecution`: connected two-worker execution, dependent target, two-name helper group and surviving copies |
| Exercise failure after useful work | `CheckpointReuse`: acknowledge, commit, destroy an acknowledged replica, crash/recover and recommit |
| Gate publication on a validator receipt, not the publisher's validity claim | `PublicationReceipts`: receipt guard on staging; untrusted workers that skip validity (`untrusted_step_is_protocol_step`, `ureachable_iff`, `invalid_never_published_untrusted`, `guard_necessary`); TLA `Receipts` with Byzantine staging. The receipt is bound to the group ID only; `HeldReceipt` reads global flight, so the guard is reachably equivalent to static `Receipted`, and the content rests on `receipt_sound` |
| Keep alternative proofs of one target from colliding, across owner failure | `TargetNames`: owner/epoch record holding the latest published proof, prepare revises that recorded head, epoch-fenced publish updates it; `guard_observable` (no ghost read), `target_chain`, `recorded_head_tops_chain`, `no_target_collision`, `handover_witness`, `scan_check_unsafe` (a scan-based check admits two heads); TLA mutations per guard conjunct plus `target_scan_subset` and `target_no_head_update` |
| Fence catalogue first writes against stale writers | `CatalogFencing`: `present_fenced`, `selected_not_stale`, `completion_not_stale`; unfenced repair and acknowledgement (`repair_put_enabled`, `ack_unfenced`, `late_ack_and_repair_execution`) show first-write fencing alone does not fence adoption |
| Recover catalogue records from physical evidence, and adopt only records committed under the fence | `CatalogCertificates`: fenced commit certificates and manifest/payload certificates; `committed_fenced`, `selected_fenced`, `stale_stays_uncertified`, `uncertified_not_committed`, `catReady_storageReady`, `certified_recovery` (scan built by `certScanValue`, no assumed scan); TLA `Fencing` with re-acquisition, commit-certificate and byte-scan mutations |
| Discover publications without the ghost acknowledgement flag | `AckCertificates`: certificates plus writers' reply logs; `reply_survives`, `scan_complete`, `scan_between`, `checkpoint_contents_discoverable`; commit after a replier is lost; TLA `Certificates` |
| Match group membership to real Lean names | `LeanNames`: command capture; public names include instances and eager auxiliaries; `render_clash_iff`, `derived_collision_iff`, `scoped_render_distinct`; re-realized reserved names |
| Keep every agent's published files identical | `Workspaces`: lineage-keyed winners, live heads render and hold names (`partial_revision_frees_name`), anchoring through own pending groups (`own_pending_anchor`, `publish_guard_needed`), carried anchor paths (`view_carried`, `render_reads_unknown_anchor`), reserved fresh namespace (`fresh_not_declared`, `reserved_check_needed`); see [notes](veil/WORKSPACES.md) for which theorems are definitional; TLA `Workspace` and `WorkspacePending` (pending state, `PublishGuard`, receive before the anchor, carried paths; mutations `workspace_no_publish_guard`, `workspace_anchor_published_only`, `workspace_render_tree_order`, `workspace_known_clock`) |
| Enforce all hardening guards together | `Hardened`: `hardened_safe` (five guards), cross-guard `hardened_certified_recovery` and `recorded_head_receivable`; `HardenedExecution`: one trace through every guard, with a fenced catalogue write at fence 1 |
| Test the original registry's effective admission/freshness guards | [Guard matrix](TLA-GUARDS.md), including independent closure/exporter oracles |

The README distinguishes abstract protocol proofs from implementation correctness.
The remaining implementation contracts are the Lean checker and exporter,
signature/integrity verification, canonical encoding and ancestry-schema decoding,
receipt signing over exact group IDs and policy versions, target owner/epoch
assignment with epoch-fenced publication that updates the recorded head,
transactional fenced catalogue first writes and commit certificates, per-replica
certificate storage with persisted replies, the Lean name classifier and
injective instance naming,
complete physical catalogue/marker enumeration, stable writes and exclusive ownership service. Receipt binding to
policy and checker version is also an implementation contract; the model binds
only the group ID. Those contracts must be implemented and tested before applying
these results to a distributed service. [store.md](../docs/store.md) maps the
storage contracts to FoundationDB and S3 operations; that mapping is an argument,
not a proof.

The failure envelope still requires a surviving recovery quorum; the loss budget
is lifetime-cumulative because nothing repairs or replaces a lost replica. New
acknowledgements need a usable write quorum. Eventual delivery requires eventual
permanent stabilisation (`heal`) and fair receive service. Finite global convergence requires finite worker and revision
universes. Liveness is not restated for the hardened protocol. Proof search termination, speedup, Byzantine storage, dynamic membership
and garbage collection are not established by these protocol extensions.
