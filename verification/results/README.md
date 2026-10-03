# Recorded verification run

Date: 2026-10-03. Execution host: AWS Linux development box, 32 CPUs.
TLC used eight workers and a 12 GiB heap limit. Negative cases used one worker.

All seven finite TLC scenarios passed. Their distinct-state counts sum to 505,312.
Five reachability witnesses and six deliberate protocol mutations produced the
required counterexamples. Raw traces are in [tlc/negative](tlc/negative).

All five Veil/Lean proof modules compiled. The final generated-namespace audit
checked **1,434 declarations** and allowed only `propext`, `Classical.choice`,
and `Quot.sound`. [Audit output](lean/Audit.log).

Commands:

```sh
bash scripts/check-tla.sh
bash scripts/check-tla-negative.sh
bash scripts/check-veil.sh
bash scripts/archive-verification.sh
```

The scenario suite was also run incrementally as the design changed; each archived
scenario log comes from its final accepted source. The source hashes identify the
final model/proof/script inputs. These hashes cover verification inputs, not this
results document or the research prose.

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
