# Merged P2 scoped fault gates (2026-10-20 UTC)

Runtime source checkpoint `5179bcd26d4858b6e8ebea80ac9a24c2ba4acad6`
(checkout subsequently received documentation-only checkpoint `811e68c`).
Prebuilt debug `paralean-p2` SHA-256
`a1a654143258a25bf927e9173e99970318f3b010c32f1396ab493c291cdca503`.
The pinned FDB and Garage binaries are 7.3.79 and 2.4.1. The release proxies
were prebuilt; no build was run while the FDB stress phase was active. All phases
use fresh private `mp2-*` instances and `ulimit -c unlimited`. `/data` had 239 GiB
available before FDB provisioning. Background netsplit and s3-guard are idle
proxy processes. The test shapes intentionally split FDB and Garage faults to
stay within about eight heavy data/workload processes.

## FDB scope (`mp2-fdb-gate`, port base 24800)

Provisioned with six FDB processes in distinct zones, five coordinators,
`triple` redundancy, FDB netsplit, one Garage node, replication 1 and s3-guard.
Exact first-start command, from `impl/p2`:

```sh
PARALEAN_INSTANCE=mp2-fdb-gate PARALEAN_PORT_BASE=24800 \
  PARALEAN_FDB_PROCS=6 PARALEAN_FDB_REDUNDANCY=triple \
  PARALEAN_FDB_COORDINATORS=5 PARALEAN_NETSPLIT=1 \
  PARALEAN_GARAGE_NODES=1 PARALEAN_GARAGE_REPLICATION=1 \
  PARALEAN_GARAGE_NETSPLIT=0 scripts/up.sh
```

Provisioning passed; raw output: `results/p2/mp2-fdb-gate-provision.log`.
For each phase, the command from `impl/p2` was
`PARALEAN_INSTANCE=mp2-fdb-gate FAULT_SCOPE=fdb STRESS_WORKERS=1 SKIP_BUILD=1 CARGO_BUILD_JOBS=1 RUST_TEST_THREADS=1 PHASE=<phase> scripts/fault-redundancy.sh`,
preceded by `ulimit -c unlimited`. The fixture phase additionally set
`FIXTURE_ROUNDS=20 PROPTEST_CASES=8 SKIP_AE=1 SKIP_MULTIPROCESS=1`; the final
data-loss phase additionally sets `I_KNOW_THIS_DESTROYS_THE_INSTANCE=1`.

| Phase | Time UTC | Outcome and evidence | Raw results |
|---|---|---|---|
| Stress | 04:29:30–04:34:46 | **PASS.** All eight FDB kill/pause/partition and single/double disk-loss stages reached. Full write availability and fault tolerance 2 returned after every stage; double disk-loss recovery took 100 s. 1,339 acknowledged effects; `verify-acks` lost 0; audit ok (494 certified groups, 306 records, 89 tombstones); no worker-error file. Serial probe: 188/203 successes, four sampled failure windows, longest five failed probes, successful latency p50 73 ms/max 3,756 ms. | `results/p2/faults-mp2-fdb-gate/fdb/stress/20261020T042930Z-2587860/` |
| Fixtures, first attempt | 04:34:54–04:49:36 | **FAIL/aborted after round 9.** A setup transaction in `guards::paginated_scan_follows_partial_batches` returned FDB's ambiguous commit error under chaos, and the test unwrapped it before any scan assertion. 28 test summaries (one failed), 65 injected faults. Stopped the known-failed attempt; all own processes and the partition were healed, FDB reported availability/tolerance 2, and a fresh write/read passed. A test-only retry fix is pending a fresh full 20-round gate. | `results/p2/faults-mp2-fdb-gate/fdb/fixtures/20261020T043454Z-2668337/` |
| Fixtures, second attempt (test source `a271510`) | 04:50:44–05:26:16 | **FAIL after complete 20 rounds.** The pagination setup retry fixed the earlier failure. Of 62 test-result summaries, 61 passed; `t8_tombstone_guards` failed in round 19 because its first tombstone call returned `false` under chaos. The fault and eight-case property tests passed. There were 152 injected faults; anti-entropy and multiprocess were explicitly skipped in this scope. All own services were up, partition healed, FDB available/tolerance 2, and fresh write/read succeeded after exit. `meta.rs:t8_body` returns `false` only when it reads both the matching tombstone key and the same writer's certificate key, consistent with an ambiguous commit followed by idempotent retry; exact failed test deployment was dynamically generated and was not separately audited. This remains a failed gate pending test/semantic review and a fresh full rerun. | `results/p2/faults-mp2-fdb-gate/fdb/fixtures/20261020T045044Z-2948158/` |
