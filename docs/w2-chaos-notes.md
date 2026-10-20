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
