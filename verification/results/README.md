# Recorded verification run

Date: 2026-10-05. The TLC logs come from a later run than the Lean logs.

TLC: macOS 26.5.1 on an Apple M4 (10 cores, shared with other jobs), OpenJDK
17.0.18 ([tlc/toolchain.txt](tlc/toolchain.txt)). Positive scenarios used four
workers and a 6 GiB heap; negative cases used four workers.
Lean: host `aws-dev`, Linux 7.0.0-1012-aws x86_64, 32 cores, OpenJDK 25.0.4.1
([toolchain.txt](toolchain.txt)).

All twenty finite TLC scenarios passed. Their distinct-state counts sum to 5,526,366.
Six of them check liveness (`Collision`, `Workspace`, `WorkspacePending`,
`TargetsLive`, `FencingLive`, `CertificatesLive`); the rest are safety +
reachability only (see the liveness table in the
[guard matrix](../TLA-GUARDS.md#liveness)).
The four larger-scope scenarios (`check-tla.sh --wide`, logs in
[tlc/wide](tlc/wide)) also passed; see the scope table in the
[verification README](../README.md#larger-scopes).
The opt-in combined hardened suite (`check-tla-hardened.sh`, logs in
[tlc/hardened](tlc/hardened)) made 29 runs on `Hardened.tla`, all with their
expected outcome: the `Hardened` (3,104,542 distinct states) and
`HardenedReacquire` (280,614) instances passed, 8 coverage witnesses and 16
single-guard mutations reported their named violations, and 3 redundancy probes
passed. Four workers, 6 GiB heap; the suite took 44min 29s. See the
[guard matrix](../TLA-GUARDS.md#combined-hardened-model).
The negative suite made 81 runs, all with their expected outcome: 26 reachability
witnesses, 47 protocol mutations (44 distinct source edits; three deletions are
checked against two oracles each), 2 runs of the original design that must fail
the new liveness properties (the stranded head and the stranded publication), 3
over-restrictive models that must lose a witness, and 3 deletions that must pass
(redundant checks). Each temporal mutation checks exactly one property.
The work witness commits the full B→A→B dependency chain.
The combined failure witness acknowledges and commits a checkpoint, destroys a
replica in both acknowledgement quorums, crashes and recovers the worker, then
recommits the same nonempty checkpoint. Guard mutations use independent closure
and exporter oracles. Rejecting dependent work or blocking post-acknowledgement
disk loss defeats the corresponding witnesses. Raw traces are in
[tlc/negative](tlc/negative); the [guard matrix](../TLA-GUARDS.md) explains coverage.

All twenty-nine Veil/Lean proof modules compiled from the final sources against
pinned dependencies. The final generated-namespace audit, which also matches
private declarations by their user name, checked **7,060 declarations**
and allowed only `propext`, `Classical.choice`,
and `Quot.sound`. [Audit output](lean/Audit.log).

Commands:

```sh
bash scripts/check-tla.sh
bash scripts/check-tla.sh --wide                 # larger scopes, optional
bash scripts/check-tla-negative.sh
bash scripts/check-tla-hardened.sh               # combined hardened model, optional
bash scripts/check-veil.sh
bash scripts/archive-verification.sh             # or --tla-only, as for this TLC run
bash scripts/archive-verification.sh --verify    # re-check archived TLC provenance
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

The hardened protocol was revised after review. Revising a collision winner keeps
its name, and only live heads render. Workers that skip validity checks are
modelled. Target ownership is reassignable and epoch-fenced. Only first catalogue
writes are fenced. Certificate quorums come from each writer's own replies,
collected over time.

A second revision of the TLA models closes a liveness gap: discovery
certificates were written after publication by nodes that know the group, so a
publisher that crashed first stranded its publication, and a stranded target
head blocked its name forever. Publication now writes the publisher's
certificate quorum in the same metadata-store transaction (`AtomicCert`), the
Fencing commit certificate requires committed parents, and recovery counts a
record as committed only on a fully live write quorum, restored after a loss
by certificate repair. The Lean modules do not yet model these changes; their
logs are from the earlier run against the unchanged Lean sources, with the Veil
build started from an empty output directory.

Every TLC log ends with a provenance block: the SHA256 of each file TLC parsed
and of the configuration, taken from the run directory TLC actually read, and,
for a negative case, the SHA256 of every pristine source it was derived from.
`scripts/archive-verification.sh` archives only complete suite runs (the wide
and hardened logs only when their own run is complete, removing their directory
otherwise), checks
each block against the current sources before copying, archives exactly the
current case list (deleting logs of retired cases), and re-checks the archive;
`scripts/archive-verification.sh --verify` repeats that last check. The source
hashes identify final verification models, proofs, component notes and
scripts. They exclude this results document and the research prose.

- [TLC logs](tlc)
- [Lean proof and axiom logs](lean)
- [Pinned tool versions](toolchain.txt) (Lean run) and [TLC tool versions](tlc/toolchain.txt)
- [Verification source SHA256s](source-sha256.txt)

TLC's state fingerprints have a small collision probability; each log records its
estimate. Formal Lean proofs cover the abstract protocol beyond these finite
instances. Neither technique proves the future production implementation.

The separate local boundary experiments passed with stock Lean 4.34.1. They confirm
definition-body invalidation, old-snapshot preservation, target-policy and axiom-policy
boundaries, and nine private AND/OR graph cases. Their earlier conditional-proof
example is not permission to publish unfinished library lemmas.
