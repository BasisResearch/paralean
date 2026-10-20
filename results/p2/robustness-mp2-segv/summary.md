# Stress-worker SIGSEGV follow-up (2026-10-20 UTC)

The run-1 fault log records worker 3, seed 3045 exiting with status 139. Its
`events.log` shows the fdbserver-3 plus fdbserver-5 double disk loss, but records
worker errors only at the end of the entire run. Thus the committed log does not
establish the instant of the crash or a stack trace. Commit `667dcf6` added
`meta::shutdown()` in the CLI's `main` and changed the FDB network guard to be
explicitly dropped and joined before process exit. That is a plausible teardown
fix, but the original run did not capture a core with which to prove causality.

We used the pinned FDB 7.3.79 client (`libfdb_c.so` SHA-256
`4d808af6dce1e5876d59bd8db691820096f206c3870e770fefac98a10b30aa40`)
and the exact `origin/p2-rest` source commit
`b2056d208520f3db19660e4d972aa703b4fa3d04`. The private `mp2-segv`
instance had six FDB processes in distinct zones, triple redundancy, five
coordinators, one Garage node, and a lightweight S3 guard on ports 24400–24450.
The same process indices 3 and 5 were killed, their data dirs wiped, and they
were restarted after five seconds. Each GDB-managed worker ran 25 operations,
seeded 1–10, with fault probability 0.02 and an acknowledgement log; the child
process was alive at disk wipe. The harness waited for committed writes and FDB
fault tolerance 2 between attempts. `ulimit -c unlimited` was set; GDB caught
SIGSEGV before apport and was instructed to write a core and all-thread stack
trace if one occurred. No SIGSEGV was observed, so no core was generated.

| CLI | SHA-256 | Valid double-loss attempts | Normal GDB exits | SIGSEGV | Acknowledged effects | Checks |
|---|---|---:|---:|---:|---:|---|
| Fixed CLI (`meta::shutdown`) | `7bec6304e7310f0590cfdd6f377f0e0af2eec033ce4cd67accb89d73440401bb` | 10 | 10 | 0 | 250 | 10/10 `verify-acks` lost 0; 10/10 `audit ok` |
| Identical source except one removed shutdown call | `ea8f4e748352e2e2fdd3bb85ffc0e64ea66c2f7a821aad7af3f1af633cb19238` | 10 | 10 | 0 | 250 | 10/10 `verify-acks` lost 0; 10/10 `audit ok` |

The exact one-line variant is [no-shutdown.patch](no-shutdown.patch). Both builds
used one Cargo job and debug symbols. Raw `events.log`, `gdb-*.log`, `acks.log`,
`verify-*.log`, and `audit-*.log` are in `segv/` (fixed) and
`no-shutdown/segv/` (variant). The GDB log for each of the 20 attempts says the
inferior exited normally. The instance was fully stopped and its ports were
clear after the study. `/data` had at least 249 GiB available.

This does **not** reproduce or definitively explain run 1's SIGSEGV. The original
had six concurrent stress workers, three Garage nodes, and many preceding faults;
this bounded comparison had one worker, one Garage node, only the repeated 3+5
disk-loss schedule, and GDB changes timing. The explicit network-thread join
remains a reasoned candidate fix, not a demonstrated fix for that crash. A full
concurrency replay would exceed this shared box's eight-heavy-process budget.
