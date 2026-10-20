# P5 verification evidence

The final report is in [docs/p5-log.md](../../../docs/p5-log.md).

- `environment.json`: implementation, upstream branches, compilers, CLIs and resource cap.
- `latest-gate.json`: real CLI workers, ten fixed contracts, sixteen checked dependency edges,
  controller death, complete desktop deletion, store enumeration/recovery and stock export.
- `latest-adversarial.json`: ten live rejection, retry, checkpoint and completion checks.
- `latest-unit.txt`: twenty-eight local regression tests, including the real contract compiler,
  journal integrity, recovery races and worker cleanup.
- `recovery-fault.json`: publication committed before its journal acknowledgement, obsolete
  fence intent, full desktop deletion, adoption without another proof, repeated recovery,
  stale receipt rejection and idempotent fence retry.
- `federation-home-fault.json`: accepted local-home fence and rejected foreign-home fence.
- `native-client-lifecycle.json`: twenty-five short bridge invocations with orderly FDB shutdown.
- `benchmarks.json` and `benchmarks.csv`: 1, 2, 4 and 8 logical-worker trials; at most four
  CLI workers run simultaneously. JSON includes model identities, task hash and host load.
- `latest-export/`: ordinary Lean source produced by the final recovery gate; `lake build`
  uses its pinned stock toolchain and needs no Paralean store or API credentials.
- `latest-isolated-stock.json`: a fresh build of those ten modules with no Paralean
  environment or copied build cache.
- `benchmark-exports/`: the stock sources produced by each measured worker count;
  `manifest.json` records their hashes, published groups and target checks.

Transfer figures are logged workspace payload bytes and operation milliseconds,
including workers' demand fetches. They exclude validator downloads, journal IO and
protocol overhead. Validator RPC, export build and final stock-build attestation
times are separate. These are single-trial measurements on a shared host, not a
controlled throughput claim. Agent proof choices and API latency are nondeterministic.
The 8-worker row does not mean eight simultaneous CLIs.

`baseline-benchmarks.*`, other earlier JSON files and `list-export/` retain earlier checkpoints. Their embedded
commit hashes and compiler versions describe those runs; they are not substitutes
for the final integrated evidence above. Agent transcripts and private keys remain
outside the repository.
