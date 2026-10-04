# Recorded verification run

Date: 2026-10-04 UTC. Execution host: AWS Linux development box, 32 CPUs.
TLC used eight workers and a 12 GiB heap limit. Negative cases used one worker.

All nine finite TLC scenarios passed. Their distinct-state counts sum to 549,222.
Eight reachability witnesses and twenty deliberate protocol mutations passed their
expected-outcome checks. The work witness commits the full B→A→B dependency chain.
The combined failure witness acknowledges and commits a checkpoint, destroys a
replica in both acknowledgement quorums, crashes and recovers the worker, then
recommits the same nonempty checkpoint. Guard mutations use independent closure
and exporter oracles. Rejecting dependent work or blocking post-acknowledgement
disk loss defeats the corresponding witnesses. Raw traces are in
[tlc/negative](tlc/negative); the [guard matrix](../TLA-GUARDS.md) explains coverage.

All twenty Veil/Lean proof modules compiled from the final sources in an isolated
scratch directory with an initially empty project output directory and pinned
dependencies. The final generated-namespace audit checked **4,859 declarations**
and allowed only `propext`, `Classical.choice`,
and `Quot.sound`. [Audit output](lean/Audit.log).

Commands:

```sh
bash scripts/check-tla.sh
bash scripts/check-tla-negative.sh
bash scripts/check-veil.sh
bash scripts/archive-verification.sh
```

The modules cover atomic multi-name groups, packet/receipt binding, completion
paired with actual durable commits, lost-ID catalog recovery, and general recovery
adequacy. Concrete Veil executions cover overlapping group resolution, duplicate
delivery with nonempty target completion, and actual storage writes/acknowledgements,
disk loss, local-ID loss and recovery despite an unready staged catalog record.
The general recovery theorem extends any reachable prefix to selection of each
previously committed record, given a complete surviving-quorum scan.

The strengthened proofs equate ancestry with recorded parent paths and allow
distinct checked objects to complete the same fixed request. Required-target
completion uses one group witness for membership, checking, contract satisfaction,
publication, acknowledgement and a surviving copy. A connected two-worker execution
admits a two-name helper group and its dependent target through receipt acceptance,
durably commits the checkpoint, then destroys a replica holding both payloads and
the manifest. The other replica retains all three objects.

The joint protocol closes the completion/discovery gaps. Completion requires a
retained catalogue record for the exact snapshot and workspace. Publication
atomically acknowledges a separate discovery marker. Receives require physical
scan evidence; accepted marker IDs are exactly the published IDs. Fair delivery
and convergence hold over the joint trace with these guards.

A connected joint execution publishes a two-name helper and dependent target,
accepts their receipts, retains payloads, publication markers, manifest and
catalogue, then completes the required target. It destroys a replica and erases
an actually selected catalogue ID. Three actual joint recovery transitions select
the same snapshot from the surviving store. A separate initial-state execution
erases every worker index before rediscovering a publication. Guard checks reject
missing catalogue evidence, a mismatched image and absent publication markers.

The final archive compared every TLA model/configuration and both check scripts
byte for byte with the checked inputs before reusing their logs. The source hashes
identify final verification models, proofs, component notes and scripts. They
exclude this results document and the research prose.

- [TLC logs](tlc)
- [Lean proof and axiom logs](lean)
- [Pinned tool versions](toolchain.txt)
- [Verification source SHA256s](source-sha256.txt)

TLC's state fingerprints have a small collision probability; each log records its
estimate. Formal Lean proofs cover the abstract protocol beyond these finite
instances. Neither technique proves the future production implementation.

The separate local boundary experiments passed with stock Lean 4.34.1. They confirm
definition-body invalidation, old-snapshot preservation, target-policy and axiom-policy
boundaries, and nine private AND/OR graph cases. Their earlier conditional-proof
example is not permission to publish unfinished library lemmas.
