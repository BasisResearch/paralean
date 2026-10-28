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

Pending. No controlled speedup claim yet.

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
