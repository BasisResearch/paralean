# Controlled Paralean scaling study

## Preregistered design (2026-10-28, before heavy runs)

Question: does distributing a fixed Lean proof task reduce time to all required
contracts validated, relative to one scripted worker on stock Lean? Separately,
does it scale relative to one Paralean worker? Neither result establishes faster
LLM proof discovery. Starting revision: a5dfc5c6eb83981156e2b456ff0465f4088b47b3.

Workloads: (1) the existing ten-target List reverse/map-length DAG, a generic
map-length lemma, eight specializations using it and List.length_reverse, then a
conjunction using all eight. These are real checked dependency edges, but this
is a small base-library API task, not a full Mathlib workload. (2) the analogous
Nat commutativity fork/join DAG, with deterministic repeated Lean tactic work
inside each branch, allowing parallel work to be increased without sleeps or
changing the dependency graph. Freeze proof scripts and task hashes before the
series. Pilot success/failure and tuning are reported separately. If resources
permit, run a Mathlib corpus materialization profile using existing read-only
build artifacts. Do not relabel the List task as Mathlib.

Baselines: stock Lean with one scripted worker, normal async setting; stock with
async disabled as a diagnostic; Paralean with 1, 2, 4, 8 logical workspaces and
matching simultaneous-worker caps. Stock builds one source in dependency order
using the same scripts, with all target bodies kernel checked. Paralean uses the
actual P5/P3/P2 path and frozen contracts. Stock has no durability, receipt or
publication equivalent; report that semantic difference. Measure validation
completion separately from final clean stock export. No artificial API delays.

Run at least three successful repetitions per workload/configuration; retain all
failed attempts. Use three blocks, alternating order across blocks to reduce
host drift. Fresh deployments/workspaces; shared compiler and OS caches warm
(no cache dropping on this shared host). Report every sample, arithmetic mean,
standard deviation, and Student-t 95% CI of mean (df=2 with three samples).
Speedup ratio intervals use endpoint ratios of positive 97.5% mean CIs
(Bonferroni joint coverage at least 95%, assuming normal sampling);
if those intervals are nonpositive, report ratio uncertainty as unbounded.
These intervals reflect observed run variability, not generalization to tasks.
Do not silently exclude outliers or mix pilot and confirmatory results.

Metrics: external monotonic wall time through all-target validation and through
export; child CPU seconds (controller tree, separately service CPU deltas where
available); workspace transferred bytes and operation milliseconds with existing
benchmark scope exclusions; cumulative validator RPC latency; controller/backend
phase timings; remote% per-element timing logs; source/capsule/kernel replay
profiles. Queue time requires server-side timestamps: RPC minus checker time is
not pure queue time and must be marked unavailable if not independently measured.
CPU and overlapping phase sums are not elapsed-time decompositions. Record exact
commands, source/toolchain/binary identities, task hashes, load averages, memory,
process/thread budget and return codes in results/scaling. Never archive keys,
credentials, full environments or authenticated worker transcripts.

Profile a representative pilot separately: async on/off, capture, working-copy
remote% checking, publication/validator kernel and capsule replay, final contract
validation, and export. Historical x2.06 all-remote elaboration, x1.39 async-off
wall cost and x2.07 warm RPC throughput are context, not new controlled samples.
Attempt a smaller real-agent confirmation after deterministic runs, conditional
on available CLI authentication/process budget; it is descriptive and not pooled
with scripted trials.

Resource policy: only this checkout and owned .runs/scaling artifacts; private
p5-scal-* service instance (P5 requires p5- prefix), dedicated ports. Read-only
reuse of built fork/Mathlib artifacts is permitted. No writes to other worktrees
or w2*/w2c-* instances. Check load before every heavy run, wait while one-minute
load exceeds 24. LEAN_NUM_THREADS=1, bounded build jobs, no more than eight workers.
Keep owned disk below 60 GB. Stop exact owned service PIDs; remove owned build
intermediates after archiving evidence. Commit design before starting services.

## Results

**Incomplete: no controlled speedup claim is established.** The repeated N=1/2/4/8
series and real-agent confirmation did not run. The ordinary-tactic synthetic
pilot remained behind the shared-host load gate; the waiting suite was stopped
and all three owned services were verified down. Do not interpret staging
folders or the implemented runner as completed measurements.

| Completed pilot | Work / workers | Validated? | Wall s | Child CPU s | 95% CI |
| --- | --- | --- | ---: | ---: | --- |
| Stock List, corrected proof script | ten fixed proofs / 1 | yes, stock kernel | 0.252 | 0.278 | unavailable, n=1 |
| Paralean List | ten fixed proofs / 1 | all ten frozen contracts | 65.792 | 35.398 | unavailable, n=1 |
| Separate clean List export | same Paralean pilot | yes | 5.854 | 4.182 | unavailable, n=1 |
| Stock synthetic, earlier metaprogram | 2,000 iterations / 1 | yes, stock kernel | 4.264 | 26.555 | unavailable, n=1 |
| Paralean synthetic, metaprogram | 20,000 iterations / 8 | **no**, heartbeat failures; aborted | 2888.236 | 9221.433 | excluded |
| Paralean synthetic, metaprogram | 100 iterations / 8 | **no**, capsule replay rejected | 73.908 | 57.300 | excluded |

The tiny List pilots show a large absolute slowdown, not a demonstrated benefit.
They were single runs at different host loads and are not a controlled speedup
estimate. Their wall-time ratio is approximately 262:1, but there is no repeated
estimate or confidence interval. The fixed proofs were already supplied: the
stock pilot had no LLM reasoning or API wait to parallelize. This does **not**
measure whether eight agents discover proofs faster than one agent. No claim of
flat scaling, successful eight-way scaling, or general slowdown on larger proof
development is justified. The earlier synthetic stock sample uses a different
work parameter and must not be compared to either synthetic Paralean failure.

| Required production configuration | List completed repetitions | Ordinary-tactic synthetic completed repetitions |
| --- | ---: | ---: |
| Stock, async on | 0/3 | 0/3 |
| Stock, async off | 0/3 | 0/3 |
| Paralean N=1 | 0/3 | 0/3 |
| Paralean N=2 | 0/3 | 0/3 |
| Paralean N=4 | 0/3 | 0/3 |
| Paralean N=8 | 0/3 | 0/3 |

### Where the successful pilot spent time

The [raw List phase trace](../results/scaling/pilot-list-p1-r0/phases.jsonl)
and [derived phase summary](../results/scaling/pilot-list-phase-summary.json)
show setup at 26.505 s, including a 24.042 s interpreted `lean --run Contract.lean`
call. Across ten publications, capture calls total 10.336 s. The complete
publication methods total 23.060 s, including capture, validation and nested sync
and contract verification; these figures must not be added together. Scripted
worker bodies total 10.046 s; the controller's guard-inclusive worker metric is
10.648 s. Other backend sync methods total 3.525 s, and journal save methods
2.079 s. Export is outside the 65.792 s validation measurement.

Ten validator requests measured 0.000079 s total semaphore queue wait,
0.113976 s input fetching, and 2.635934 s checker subprocess execution. The
controller recorded 6.431 s cumulative validator RPC latency. Their difference
includes request preparation, authority/store/signature work and transport; it
is **not** a queue-time estimate. With serial controller publication, the queue
was effectively empty. Single-slot validator capacity alone does not explain
this pilot's wall time.

Workspace transfer was 36,811 payload/capsule/metadata bytes in 168.830 ms of
logged operations. This excludes validator downloads, P5 journals, FDB/S3
protocol overhead and failed operations outside those logs. Storage service CPU
deltas were FDB 0.92 s, Garage 0.28 s and the S3 guard 0.03 s, separately from
35.398 child CPU seconds. These are scoped byte/CPU measures, not a complete wire
traffic or machine-wide energy account.

The representative same-host remote/local and separate source/kernel replay
profiles were prepared but did not execute before shutdown. Therefore this run
has no new isolated remote% ratio, async-off ratio, or kernel-vs-capsule timing.
The [historical remote study](p3-remote-log.md#measured-costs) measured aggregate
all-remote command elaboration at 2.06 times local on seven Mathlib modules;
M18 included 0.54 s fetched-proof loading and 0.65 s receipt checking. The
[async gate](p1-gate.md) measured 1.39 times wall time with async disabled on its
Mathlib sample, while total CPU decreased. The [M14 warm/cold pair](m-targets-log.md)
measured 2.07 times validation RPC throughput. These are earlier experiments,
not repeated samples or additive multipliers for this pilot.

### Improvements supported by the available evidence

1. **Compile the P5 contract and snapshot helpers.** The interpreted contract
   helper alone took 24.042 s before dispatch, versus a 65.792 s total validation
   run. This is the clearest first optimization for short tasks. It has not been
   implemented or timed here; eliminating the whole call would be an upper
   bound, not a promised saving. Long tasks amortize this fixed startup cost.
2. **Pipeline controller coordination and publication.** P5 calls backend
   publication/validation synchronously and records 23.060 s inside publication
   methods for ten tiny proofs. Separate worker concurrency cannot remove that
   serial critical path. A change must preserve owner/epoch fencing, frozen
   contracts and durable journal ordering. This study has not measured the
   resulting speedup.
3. **Reuse the validator's pinned base environment.** Checker subprocess time
   was 2.636 s across the List requests; the existing M14 warm checker pair
   provides stronger, separate evidence (2.07 times RPC throughput) for
   import-heavy workloads. Reusing immutable base state should preserve fresh
   per-job checks. Kernel validation must not be disabled to improve a benchmark.

Safe async restoration remains a larger Lean engineering task (OPEN-14). It
could matter on heavier files, but the present tiny pilot cannot quantify it.
Even removing all measured setup time would leave this pilot far slower than
its stock check. Faster than stock is not a supported promise for fixed, already
written tiny proofs with additional publication guarantees.

### Resource block and remaining scope

The first load-gated suite waited until a brief low-load window and then stopped
on the metaprogram capsule rejection. The corrected ordinary-tactic suite waited
from 18:27:25 to 19:10:55 UTC; its 88 recorded checks never opened the load gate.
Its last one-minute load was 44.85 against the threshold of 24. The
[resource logs](../results/scaling/resource-block/suite-r2.log) retain these checks.
Shutdown used only exact owned PIDs and the ownership-checked service wrapper;
no other workspace or instance was modified. Approximate peak owned build and
runtime footprint was 1.6 GB. Build intermediates were removed after archiving.

Remaining work is substantial: pass the ordinary-tactic pilot; run all 36
production samples; execute same-host remote/local and source/kernel profiles;
run the actual-agent pair; and compute the preregistered intervals. No full
Mathlib task was run. N>8 was not attempted: the DAG width is eight and shared
load provided no headroom. The selected fork/Mathlib artifacts were read-only.

See [the result archive](../results/scaling/README.md) for exact commands and
resume instructions. Production sampling must retain failures and use fresh
IDs; it must not relabel any of these pilots as a three-repetition result.

### Pilot decisions

The initial List stock script used two incorrect implicit-argument applications;
that failed pilot is retained, and the corrected script passed. The initial
synthetic stock pilot used 2,000 tactic iterations per branch. The eight-worker
pilot increases that to 20,000 so worker checks can overlap the serial dispatch
path. Production synthetic samples use 20,000, recorded explicitly in each row.
The List Paralean pilot passed all contracts and clean export. Production wall
time ends after all-target contract validation; the representative pilots measure
clean export separately. Production proof scripts will remain fixed.

Pilot amendment before production: the 20,000-iteration pilot exceeded worker
heartbeats and drove load above 24; it was aborted by exact owned PIDs and is
excluded from inference. It exposed that ws-check can report JSON errors with a
zero process exit code; the scripted worker now checks that JSON explicitly.
Reduce production synthetic work to 100 iterations per branch and impose a
180-second worker timeout. A new eight-worker pilot must pass before production.
This reduces the attainable compute/coordination ratio; report it as a limitation.

Confirmation specification before production: one actual Claude CLI List trial
at N=1 and one at N=8 (rather than pooling agent and scripted repetitions).
This is a small descriptive pair with no distributional speedup claim. Record
reported model identities and actual CLI worker wall intervals where available;
keep authenticated transcripts private. If CLI credentials, budget, or runtime
limits prevent completion, report that failure explicitly.

Second pilot amendment: the 100-iteration `run_tac` pilot passed workspace checks
but failed independent source replay (`Lean.Elab.Tactic.TacticM` unavailable).
No production trials had begun. Replace the metaprogramming loop with 100 ordinary
`have hscal : (1 : Nat) + 1 = 2 := by decide; clear hscal` tactic pairs in each
branch, importing only Init. Keep the rejected pilot as a compatibility failure,
not a timing sample. Validate this ordinary-tactic variant in a third pilot.
