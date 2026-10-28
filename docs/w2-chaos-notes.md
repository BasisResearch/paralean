# W2 chaos and stress-worker crash investigation

## Evidence at handoff

The workstream prompt calls the last 61/62 fault run a round-15 pagination
failure. The retained run does not support that description. In
`results/p2/faults-mp2-fdb-gate/fdb/fixtures/20261020T045044Z-2948158/`,
`events.log` reports `fast suites round 19 FAILED`, and `tests.log` identifies
`t8_tombstone_guards` as the sole failure. The assertion at the historical
`tombstones.rs:147` expected a first T8 call to return `true`; an FDB commit
with a lost reply can durably publish T8 and resolve to `false` on its
idempotent retry. `docs/p2-log.md` describes this same failure and the later
test correction, which now checks the exact tombstone and certificate and
requires a recorded real ambiguous commit if a first call returns `false`.

An earlier fixture attempt, retained at
`results/p2/faults-mp2-fdb-gate/fdb/fixtures/20261020T043454Z-2668337/`,
did fail in `paginated_scan_follows_partial_batches`: its raw setup commit
returned FDB's ambiguous-commit error before the scan assertion. The test's
fixed-key setup now retries idempotently through `on_error()`. Neither
retained failure demonstrates a production pagination bug. A later 20-round
run is reported as passing in `docs/p2-log.md`, but its uncommitted artifacts
are absent from this checkout, so it is not independently counted here.

The prior SIGSEGV evidence is `results/p2/robustness-mp2-segv/summary.md`:
worker 3, seed 3045 exited 139 in the original six-worker stress run. Ten
GDB-managed 3+5 double-disk-loss replays with explicit FDB network shutdown
and ten without that call each exited normally. No core or original crash
stack exists. Thus the FDB network-thread join remains a plausible fix, not
a demonstrated root cause.

## W2 isolated verification

`w2-chaos` is the only instance operated by this investigation. It uses ports
29400–29450, six FDB processes with triple redundancy and five coordinators,
one Garage node, and the delete-denying S3 guard. `df -h /data` showed 243 GiB
available before the run. The FDB fault scope needs only this one Garage node.
The fixture harness now accepts and logs `CHAOS_SEED`, seeding Bash `RANDOM`
inside the fault loop for replay of fault choices. FDB timing and scheduling
remain nondeterministic.

### First full FDB fixture gate

Command:

```sh
PARALEAN_INSTANCE=w2-chaos FAULT_SCOPE=fdb PHASE=fixtures CHAOS_SEED=3045 \
  FIXTURE_ROUNDS=20 SKIP_BUILD=1 SKIP_AE=1 SKIP_MULTIPROCESS=1 \
  PROPTEST_CASES=8 impl/p2/scripts/fault-redundancy.sh
```

**PASS**, 2026-10-20 15:48:21–16:13:03 UTC. All **62/62** test suite
summaries passed: 20 repetitions each of fixtures (9 tests), guards (13),
and tombstones (6), then faults (10) and property (one test with eight
randomized cases). The harness logged **103 injected FDB faults** and no failed
test or fault command. The log is in
`results/p2/faults-w2-chaos/fdb/fixtures/20261020T154821Z-2337715/`.
At completion, all six FDB processes, Garage, the gateway and netsplit were
up, the split state was empty, and `phase fixtures: PASS` was recorded.
This run used the original TCP-upstream S3 guard.

After that gate, only this instance's Garage and S3 guard were stopped. A
fresh `PARALEAN_INSTANCE=w2-chaos impl/p2/scripts/up.sh` restarted them with
the hardened gateway connected to Garage over its private Unix socket at
`garage/n0/s3.sock`; the gateway command line and listening socket were
checked. The second full gate uses `CHAOS_SEED=7001` and the same other
parameters. Its artifact directory is
`results/p2/faults-w2-chaos/fdb/fixtures/20261020T161335Z-2888120/`.

### Second full FDB fixture gate

The same command with `CHAOS_SEED=7001` **passed**, 2026-10-20
16:13:35–16:32:55 UTC: **62/62** suite summaries, including all 20 fast
rounds, the ten fault cases and eight property cases. The harness logged
**86 injected FDB faults**. Every own FDB process and Garage was up and the
split state empty at completion. This run exercised the hardened gateway
using Garage's private Unix socket. Its raw evidence is in the directory
above. A third full gate with `CHAOS_SEED=11939` began at 16:33:05 UTC; its
directory is `results/p2/faults-w2-chaos/fdb/fixtures/20261020T163305Z-3316713/`.

### Third seeded run, mixed build

`CHAOS_SEED=11939` also ended **PASS**, 2026-10-20 16:33:05–16:58:57 UTC:
**62/62** suite summaries and **106 injected FDB faults**. Every own service
was up and the split state empty at completion. This run spans two test
builds because shared P2 security changes landed during it: the fixtures
binary changed from `fixtures-9781335334ad89c6` in round 1 to
`fixtures-5c0980e580d550d5` in round 2. Its results are useful coverage
of the evolving code but do not certify one fixed source revision. A further
20-round gate is needed after P2 edits stabilize.

### Scoped FDB stress

Command:

```sh
PARALEAN_INSTANCE=w2-chaos FAULT_SCOPE=fdb PHASE=stress STRESS_WORKERS=1 \
  SKIP_BUILD=1 impl/p2/scripts/fault-redundancy.sh
```

**PASS**, 2026-10-20 16:59:30–17:07:35 UTC, with CLI SHA-256
`21d8d2e70367c0108146d43e5feeaef85aef7fc9d29165d5486dffda728d6cce`.
All eight FDB kill, pause, partition, single disk-loss and double disk-loss
stages completed. Full reported tolerance 2 returned 91 seconds after the
single disk loss and 100 seconds after the double loss. The one stress worker
recorded **2,285 acknowledged effects**; `verify-acks` found **zero lost**.
The final audit found 825 certified groups, 526 committed records and 163
tombstones, with no violation. The final probe had 334/353 successful samples;
these samples do not establish continuous availability. Raw logs are in
`results/p2/faults-w2-chaos/fdb/stress/20261020T165930Z-3891893/`.

### GDB crash replay

Command:

```sh
PARALEAN_INSTANCE=w2-chaos SEGV_WORKER=3 SEGV_SEED_BASE=3045 \
  SEGV_ATTEMPTS=10 SEGV_MAX_STARTS=30 \
  impl/p2/scripts/robustness-study.sh segv
```

This ran against the exact debug CLI SHA-256
`21d8d2e70367c0108146d43e5feeaef85aef7fc9d29165d5486dffda728d6cce`
and FDB 7.3.79. From 2026-10-20 17:07:56–17:10:30 UTC, GDB launched
worker 3 with seeds **3045–3054**. On every attempt, the worker was alive
while fdbserver 3 and 5 were killed and wiped; both restarted after five
seconds and committed writes plus tolerance 2 recovered. GDB was set to stop
on SIGSEGV and write an all-thread backtrace and core. It recorded **10/10
normal inferior exits** and no SIGSEGV, so there is no core to inspect.
The 226 acknowledged effects were all present, and **10/10 audits passed**.
Raw GDB, verify-acks, audit and fault logs are in
`results/p2/robustness-w2-chaos/segv/`. The original six-worker crash remains
unexplained: this bounded replay uses one worker and GDB perturbs timing.
It establishes that the exact original worker/seed and fault indices did not
reproduce the crash in this schedule; it does not prove the explicit FDB
network-thread shutdown was its cause.

### Fixed-tree final fixture gate

After the P2 security edits ceased, the CLI rebuilt successfully from
`HEAD=aae9b0156dc857bd856c3a89471b1ed89ff250db` plus the working tree.
The new CLI SHA-256 is
`64f493ba8b5c4201aa8fd6df7cc11e8594fe6827a6ed5e05f4c829086e4e3bad`.
The binary diff for `impl/p2` at gate launch hashes to
`005edf0ea9092ae7c2b7e72f360f21225312611c0c9a3f8280a456a0a85d9e3f`;
the then-untracked crypto and strict-signature test file hash list hashes to
`adf4e2594198c7593967b06d1c657acc1f0adf105cd300bfd95583a912646583`.
A fourth full run, seed **22021**, began at 17:12:43 UTC. Its artifact
directory is `results/p2/faults-w2-chaos/fdb/fixtures/20261020T171243Z-4162870/`.

This fixed-tree run **passed**, 2026-10-20 17:12:43–17:33:23 UTC:
**62/62** suite summaries, **87 injected FDB faults**, all own services up,
and the split state empty at completion. The `impl/p2` diff fingerprint above
was identical at the start and end. Each suite kept one executable identity
through the run: fixtures `5c0980e580d550d5`, guards
`b1b1242a46c4aba8`, tombstones `7cc30b530e4c3159`, faults
`b89115c960f2686b`, property `fa9e5090d37057ce`.

There is no demonstrated production pagination bug in the retained failure
or the four W2 fault runs. The retained pagination failure was a test setup
commit with an ambiguous outcome, and the retained 61/62 failure was a
tombstone freshness assertion under the same class of outcome. The prior
test-only fixes preserve exact durable-state checks. No protocol guard was
added or relaxed here, so there is no new guard-removal mutation or model
change for this W2 investigation.

### Rebuilt-CLI GDB replay and disposition

The exact GDB command above was repeated with `OUT` set to the separate
`results/p2/robustness-w2-chaos-fixed/` directory, against CLI SHA-256
`64f493ba8b5c4201aa8fd6df7cc11e8594fe6827a6ed5e05f4c829086e4e3bad`.
From 17:33:46–17:39:53 UTC, seeds **3045–3054** again produced **10/10
normal inferior exits**, no SIGSEGV and no core. All **226 acknowledged
effects** were present and **10/10 audits passed**. The first and final
double-loss recoveries took 102 and 101 seconds to regain writes and reported
tolerance 2; the intervening recoveries were shorter. The private `w2-chaos`
cluster was fully stopped afterward, with no active partition.

Across the prior investigation and W2, there have now been 40 bounded GDB
double-loss replays: 20 earlier A/B runs on the older source and 20 W2 runs
on two recorded CLI builds, with zero reproduced SIGSEGV. This is a
non-reproduction, not a root-cause proof. The original run had six workers,
three Garage nodes and preceding faults, and left no core or crash timestamp;
the W2 replay used one worker, one Garage node and GDB timing. A definitive
native crash fix would require a captured stack or a reproducer. The explicit
FDB network-thread join is retained as a plausible teardown mitigation.

## Finish-branch crash evidence (2026-10-21 UTC)

The worktree's later uncommitted gate, salvaged at `6f5cfe3`, used seed **77003**,
the fixed CLI SHA-256 `548712d0673056cadd13d95c63c944b665ba47ea9a094ad490fd61e7762cda5f`,
and one unchanged source tree. It passed **150 fast rounds** and logged **428 FDB
faults**, from 2026-10-20 23:29:58 to 2026-10-21 01:13:23 UTC. The raw
`events.log`, `tests.log`, `probe.log`, and console log are under
`results/p2/faults-w2-chaos/fdb/fixtures/20261020T232959Z-1106477/` and
`results/p2/faults-w2-chaos/console-pagination-77003.log`.

The salvaged six-worker stress campaign (`results/p2/faults-w2-segv/campaign.log`)
contains seven passing runs: one no-shutdown build, three intermediate builds,
and three final builds, with zero signalled workers and zero lost acknowledged
effects. `results/p2/exit-race-w2-chaos/` records **6,000 faulted CLI exits
with shutdown disabled** (136 FDB faults) and **6,000 with shutdown enabled**
(73 FDB faults), with no signal or other nonzero exit in either arm. A further
400 quiet exits on the disabled arm also passed. The old CLI SIGSEGV remains
unreproduced: these comparisons do not prove that its cause was network
teardown. The handler-check `SIGSEGV` is a synthetic signal with `si_code=0`,
not a captured native fault.

On a new `w2b-chaos` instance (ports 30400–30450), a three-round fixture run
under seed **77003** failed once in an especially informative way. The first
`fixtures` test process printed `test result: ok. 9 passed` and then Cargo
reported its exit as signal 11. The remaining two fixture rounds, guards,
tombstones, faults, and the eight-case property test passed. The run logged
**18 FDB faults** and ended `phase fixtures: FAIL`. Its CLI SHA-256 was
`154c0794fbcf140dd511d87d9863930083f09c7666952a7477091207a9e6892b`,
and the crashing fixture binary SHA-256 was
`8c06817573466b0a5df1461e76fe8ea5dc4cea53af91a54f157a4ef348775971`.
Raw logs and the pinned binary are in `results/w2/finish/chaos/seed-77003/`
and `results/w2/finish/chaos/gdb-fixtures/`. The log has no core or fault
stack; two GDB runs of that same fixture binary without concurrent faults
exited normally.

The FoundationDB Rust crate 0.11.0 says its `NetworkRunner` must be stopped
before process exit; `NetworkAutoStop::drop` invokes `fdb_stop_network()` and
joins the thread. P2's global network guard had no normal-exit owner in stock
Rust integration-test binaries, so their test process could exit with the FDB
network thread still running. That is an evidence-backed **candidate** for the
new post-result SIGSEGV, not a stack-confirmed cause of that particular fault.
An attempted C `atexit` fallback was rejected: a minimal child that booted
FDB and stopped it from `atexit` crashed deterministically in
`fdb_stop_network()`; GDB shows `shutdown()` under glibc's
`__run_exit_handlers` while the network thread was still in
`fdb_run_network()`. The rejected implementation is absent from the tree;
its stack is retained in `results/w2/finish/chaos/network-shutdown/gdb-child.log`.

The test-process fix is an explicit end-of-suite harness for the five
chaos suites. It runs all selected tests, then calls `meta::shutdown()` while
Rust and the test runner are active and before `Conclusion::exit()`. The helper
also stops FDB if the runner unwinds. A subprocess contract test verifies the
explicit stop/join: normal build passes; `mutate-no-network-shutdown` fails
because the network guard remains present. Run it with
`impl/p2/scripts/check-network-shutdown.sh`; its logs are in
`results/w2/finish/chaos/network-shutdown/`. This checks the teardown
contract, not the origin of the old stress-worker SIGSEGV. The exit-race
harness now fails on any nonzero CLI status or incomplete run count, in
addition to signalled exits.

### Focused replay of the post-result crash

With the explicit fixture harness, the same seed **77003** passed three
fixture-only rounds (**27/27** test executions) under **four injected FDB
faults**, ending 2026-10-21 02:11:57 UTC. The binary SHA-256 was
`5f06496a1f6f514e387a1089b0da4b7f47ed34afa67c08e4b2371163f2abfc69`.
Raw results are in `results/w2/finish/chaos/fixture-harness-77003/fixtures/`.
This bounded replay tests the corrected process-exit path; it does not prove
the original worker SIGSEGV or the one new fixture SIGSEGV cannot recur.

### Full seeded gate on the explicit-harness tree

Seed **22021** passed a full FDB-scoped fixture gate, from 2026-10-21
02:13:40 to 02:19:48 UTC: three rounds each of fixtures (9), guards (14),
and tombstones (6), then faults (10) and the property test (eight cases).
All **11 suite summaries** passed under **26 injected FDB faults**; the
instance was healthy and the split state empty at completion. The CLI SHA-256
was `154c0794fbcf140dd511d87d9863930083f09c7666952a7477091207a9e6892b`.
Raw logs are in `results/w2/finish/chaos/full-22021/fixtures/`.

The known-crash seed **77003** passed the same full gate, from 02:20:06 to
02:25:07 UTC: **11/11 suite summaries**, including all nine fast-suite
repetitions, the fault suite, and an eight-case property test, under **20
injected FDB faults**. It had no signalled or failed test process. Raw logs
are in `results/w2/finish/chaos/full-77003/fixtures/`.

Seed **99173** passed the same full gate, from 02:26:27 to 02:29:49 UTC:
**11/11 suite summaries** and **15 injected FDB faults**. Its raw logs are
in `results/w2/finish/chaos/full-99173/fixtures/`. Together the three
post-fix full gates passed **33/33 suite summaries** (nine fast rounds,
three fault-suite executions, and three eight-case property executions)
under **61 injected FDB faults**, on one unchanged P2 tree and the same
`w2b-chaos` instance. They are bounded evidence for the corrected test
process lifecycle; the old stress-worker SIGSEGV still has no crash stack.

`libtest-mimic` initially caused proptest's source-relative failure
persistence to warn that it could not locate a Rust `main.rs` or `lib.rs`.
After the full gates, the property suite was given an explicit regression
file path. The finish pass points it at the existing
`impl/p2/crates/store/tests/property.proptest-regressions`, so its three
recorded shrunk cases still run first.
A one-case property smoke passed without the warning
(`results/w2/finish/chaos/property-persistence-smoke.log`). The mutation
checker was updated to recognize padded libtest-mimic verdicts; two
`mutate-no-owner-check` cases correctly reported `detected` in
`results/w2/finish/chaos/mutation-parser-smoke.log`. Those two tooling edits
do not change the store guards or the chaos harness's fault schedule.

## Root cause of both SIGSEGVs (2026-10-28 UTC, `w2c-chaos`)

**Cause.** A process that leaves `main` while the FoundationDB network thread
still runs `fdb_run_network()` races libfdb_c's own exit-time destructors.
glibc's `exit()` runs `_dl_call_fini` for libfdb_c, whose `__cxa_finalize`
destroys and frees the client library's global objects. The network thread
keeps executing in the same library and dereferences what was just freed.
The crash needs no FDB fault. It needs only (a) no `fdb_stop_network()` and join
before exit, and (b) the network thread busy at that moment. In practice (b) is
the asynchronous destruction that dropping a `Database` queues on the network
thread.

**Reproducer.** `impl/p2/crates/store/examples/exit_race.rs` boots FDB exactly as
P2 does (`meta::boot`), issues read-version requests from four threads for 50 ms
and leaves `main` in one of four ways. `impl/p2/scripts/exit-race-repro.sh` runs
it sequentially and captures a GDB backtrace from apport's core immediately after
a crash, because apport keeps only its latest few cores. All runs used FDB client
7.3.79 (`libfdb_c.so` SHA-256 `4d808af6…0aa40`) on a healthy six-process
triple-redundant cluster with no injected fault.

| Exit shape | Runs | SIGSEGV | Evidence |
| --- | ---: | ---: | --- |
| `idle`: drop the database, return without stopping FDB (the stock libtest harness after its last test; the pre-`667dcf6` CLI) | 1000 + 1000 (+1000) | **11 + 6** (+10) | `exit-race-repro/`, `exit-race-repro-healthy2/`; the bracketed run was an earlier, identical run whose directory the clean rerun replaced |
| `keep`: as `idle`, but the database is leaked, so no destruction is queued | 1000 | 0 | `exit-race-repro/` |
| `busy`: return with requests still in flight, database alive | 1000 | 0 | `exit-race-repro/` |
| `idle+gap`: as `idle` with 20 ms between the drop and the return | 1000 | 0 | `exit-race-repro-gap20/` |
| `stop`: drop, then `meta::shutdown()` (stop and join; the fix) | 1000 | **0** | `exit-race-repro/` |
| `idle` / `idle+gap` with fdbserver 3 and 5 killed | 500 / 500 | 0 / 0 | `exit-race-repro-2down/` |

The `idle` rate is about 1% (27/3000) with one sequential lane. Four parallel
lanes crashed 0/400 times; the scheduling changes the window. The first
exploratory run (2/100 sequential, then 2/200) is in this text only. The
degraded-cluster rows do not show a wider window: 0/500 is weak evidence of a
narrower one, so this note does not claim that faults raise the rate.

Every captured core has the same two-thread shape (`exit-race-repro/idle-bt-*.txt`):

```
network thread: fdb_run_network → … → SIGSEGV at one fixed libfdb_c offset (…fcf6)
main thread:    _dl_call_fini → libfdb_c fini → __cxa_finalize(libfdb_c) → destructor
                → free()/_int_free_chunk (or a libfdb_c destructor frame)
```

The earlier rejected `atexit` fallback (`network-shutdown/gdb-child.log`) shows
the same ordering from the other side. By the time any exit handler runs,
libfdb_c's state may already be destroyed, so stopping FDB from an exit handler
crashes in `fdb_stop_network()` itself. The stop must happen before `main`
returns.

**The 61/62 fixture failure.** The `seed-77003` fixture process printed
`test result: ok. 9 passed` and was then killed by signal 11. That is this race:
the stock libtest main drops each test's `Env` (and its `Database`), prints the
summary and returns into `exit()` with the network thread running. It is not a
store or pagination defect. Every FDB-using P2 suite now has an explicit
`libtest-mimic` main that runs every trial, then calls `meta::shutdown()` before
exiting (`tests/common/mod.rs::run_tests`). The 61/62 `t8_tombstone_guards`
failure and the round-9 pagination setup failure are the separate ambiguous-commit
test bugs described at the top of this file. Both were fixed earlier.

**The stress-worker SIGSEGV (p2-rest run 1).** No core of that process exists,
so its stack cannot be shown. Its binary predates `667dcf6` and had the `idle`
exit shape: `#[tokio::main]` dropped the store, then returned into `exit()`
without stopping FDB. The reproduced mechanism is therefore the precise
explanation of the crash class, and `667dcf6` (now `crash::Teardown`) removes
it. It also explains why 12,000 CLI exits with the stop removed did not crash:
the current CLI drops its multi-threaded Tokio runtime (joining its worker
threads) between destroying the database and exiting. The 20 ms gap row shows
that such a gap closes the window. The historical crash happened during
double disk-loss recovery; this investigation found no evidence that recovery
was necessary rather than coincidental.

**Remaining binaries.** The P3 controller/validator (`impl/p3/crates/control`),
`p3-remote` and their FDB test suites also return from `main` without stopping
FDB. They are fixed with the same pattern after the origin/main merge (see
w2-log.md).
