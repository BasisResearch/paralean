# W4: control-plane scale

Branch `w4-scale`, starting at `fee94d9` (`origin/main` checked on 2026-10-20).
The parent delegated disjoint protocol models, controller implementation, and
GC/guard implementation and tests to three `gpt-6-sol` agents, and owns review,
integration, independent checks, benchmarks and the verification archive.

## Protocol scope and design

The existing P3 controller has a global 8 MiB snapshot and local-clock leader
and worker deadlines. W4 replaces authority timing with store-ordered logical
versions, keeps transactionally checked term/holder fences, and partitions
controller state and elections into fixed shards. Cross-shard dependency safety
continues to require the authoritative P2 publication/certificate checks.
The implementation and its bounded verification evidence are recorded below.

GC is a new protocol, not removal of existing grow-only assumptions. The initial
implementation targets obsolete controller metadata. Store objects, publication
certificates, catalogue records and P5 recovery journals must remain retained
unless a complete root and retirement protocol establishes safe deletion.
The collector is disabled by default. Logical grace, retained roots, concurrent
snapshot loading and anti-entropy are explicit review obligations.

## Isolation and resources

The W4 instance uses `PARALEAN_INSTANCE=w4-scale`, ports 29500 (FDB), 29520
(Garage S3), 29530 (Garage RPC), 29540 (Garage admin), and 29550 (S3 guard).
Data lives under `/data/home/kirancodes/paralean-p2/inst/w4-scale`. Tests use
fresh deployment prefixes within this instance. No other instance is modified.
Initial `/data` availability was 244 GiB. Builds use one Cargo job; positive and
negative TLC suites use one worker. The final hardened archive refresh uses four
TLC workers in one JVM. Shared binaries and
fixture files are read-only inputs; all new build products are local.
The W4 FDB, Garage and S3-guard processes were stopped after the final live tests
and benchmark. Their instance data is retained for reproduction.

## Evidence and checkpoints

Checkpoint `128cf15` implements the GC-principal S3 boundary and its encoded-query
guards; pushed to `origin/w4-scale`. Three unit tests, three guard-removal
mutations and seven signed live checks passed. The controller/model integration
checkpoint and final archive results follow below.

### Logical authority and shard ownership

Each shard has its own FDB `controller/shard/<n>/clock`, lease, state head,
chunks and retired-snapshot index. A clock advance is a serializable increment;
only committed increments age leases. Leader and worker leases last eight
increments. `--lease-ms` now controls the monitor's scheduling interval
(`lease-ms / 8`, at least 20 ms), not an authority deadline. More replicas can
advance logical time faster. A stopped store stops logical expiry. Availability
requires a surviving replica to advance the clock and run recovery; there is no
wall-time takeover guarantee. Tokio skips missed timer events after a pause.

Lease acquisition/renewal and every fenced metadata write read the shard's
counter and lease transactionally. A change of holder, or reacquisition after
expiration, increments the term. Dispatch retains its starting term rather than
adopting a later one. FDB conflicts serialize a racing advance, takeover and write.
Wall clocks are not read by the controller authority code; transport deadlines
and benchmark durations still use local monotonic timers.

Clock skew can change when a process attempts an operation, but cannot change
the lease predicate evaluated inside its FDB transaction. For one shard, a
takeover changes the lease key read by every fenced controller write, so a competing
old-holder transaction conflicts or fails its holder/term/expiry check. Different
shards may legitimately have different leaders. Handover reloads the durable head
and shard-local J1 index rather than depending on the old process's memory.

Run replicas with `controller --shard N --shards K`. The fixed shard count is
stored transactionally and inconsistent configurations fail closed. A target's
default shard is a stable hash of its canonical name; immutable target claims
record group colocation and prevent another shard from taking queued targets.
Work request and validation request routing records preserve identity across
retries. A fresh multi-name group can be colocated atomically; combining names
already assigned to different shards is refused. Workers race initial registration
across endpoints, heartbeat each endpoint independently, and register on demand
when polling a new shard. Cross-shard **dependencies** remain
supported through the existing global P2 T1 certificate/publication checks.

There is no deployment-wide 8 MiB snapshot limit: four independent heads holding
12 MiB were written and recovered in the live benchmark. **Each shard still has
an 8 MiB snapshot cap**, and topology is fixed; this is not unbounded single-shard
storage or online resharding. Existing legacy controller state/lease keys cause
startup refusal. An offline migration tool and rolling mixed-version upgrade
protocol are not implemented; do not mix legacy and W4 controller binaries.

### GC protocol and scope

`GcConfig::default()` disables collection. The controller's explicit `--gc`
flag enables bounded sweeps; `--gc-grace-ticks` defaults to eight and
`--gc-scan-limit` to 128. The collector library default grace is two ticks.
Grace must be positive. The monitor schedules its next sweep by a logical
deadline, so interleaved replica ticks cannot make it miss every sweep. A test
feeds only odd ticks to reproduce the former modulo-scheduling starvation;
its mutation is detected. A live monitor test witnesses automatic reclamation
when enabled, retention when disabled, and queued-work preservation in both.

Snapshot saves atomically write chunks and replace the
head; replacing different content records the former snapshot's generation,
size, chunk count and retirement tick. Identical content saves do not retire
their current chunks.

A candidate becomes collectable only when its retirement is old enough, its
exact retirement record still matches the scanned incarnation, it is not the
current head, and it has no explicit retention marker. The collector reads
these conditions and the current leader fence in the same FDB transaction that
clears the chunks and retirement record. Concurrent retention, reactivation,
resave or handover conflicts with deletion. Retention is an explicit policy bit,
not a reference count; releasing it ends that retention obligation.

Loads read the head and every chunk in one FDB read transaction. Thus collection
cannot splice two snapshot generations into one read; a transaction that ages
out fails rather than returning incomplete state. A later authorized save may
reuse a content hash by rewriting its bytes as a new generation. This is not
anti-entropy resurrection of a collected incarnation.

The implemented root inventory is the current shard head and explicit retention
markers. No other protocol record references superseded controller chunks.
P3's current snapshot carries scheduling state; global J1/J2, assignments and
request descriptors remain retained. P5 task heads, encrypted recovery blobs,
journals and catalogue records remain untouched. Fresh readers and new controller
processes recover from the current FDB heads without desktop files. Explicit
retained snapshots prevent their old chunks from being removed. The broader
model includes pending jobs, checkpoints, catalogues, demands and dependencies as
root obligations; enumerating those roots in production is required before
extending collection beyond controller snapshots.

History compaction is a separate protocol from deleting retired chunks. Its
design moves terminal work descriptors and stable poll outcomes into durable
replay records, atomically with pruning those entries from the current snapshot.
Logical grace starts when a record becomes eligible. Queued/running work,
pending assignment intents and current group ownership remain live. Replay
records retain request identity and the first poll selection indefinitely;
turning GC off cannot disable reads of those records. A later cancellation
continues to affect a compacted job's duplicate response through the durable
cancellation record. The bounded `W4History` model passed before implementation;
integration and crash-boundary evidence are recorded in the final summary.
Retained snapshots are readable historical roots, not an API for rolling the
authoritative head backward. Recovery follows the current head; promoting an
old snapshot would require a separate reconciliation protocol.
Compaction shares the opt-in GC configuration and scans both work and poll
history fairly, including a scan limit of one. Individual replay records above
90 KiB remain in the snapshot; they cannot block smaller eligible records.
One compaction pass budgets at most 200 KiB of replay values, and the durable
write API enforces a 256 KiB aggregate bound alongside the 8 MiB snapshot bound.
`Status.work` reports active and recent uncompacted jobs; cumulative
`history_compacted_work` and `history_compacted_polls` counters report retired
entries. Retry lookup remains available for compacted IDs.

This distinguishes compatible compaction from forgetting historical IDs.
Deleting the last replay record would permit an arbitrarily delayed retry to
create new work, contradicting the existing unlimited-retry contract. Such
deletion requires a defined retry horizon or non-reusable request namespace.
Current live state can still reach a hot shard's 8 MiB limit; fixed sharding and
terminal-history compaction do not eliminate that limit. Stamping previously
unstamped records also needs snapshot headroom; a shard already at the limit
fails closed rather than bypassing grace. P2 S3 objects and certificate/catalogue history remain grow-only:
the existing anti-entropy scans and desktop recovery can still demand them.
Safe object GC is blocked on a complete distributed root/retirement protocol,
including stale advertisements and disconnected peers. No such object-GC safety
claim is made here.

The bucket boundary has an opt-in `s3-guard --gc-access-key KEY`. Only object
DELETE with that SigV4 identity can reach Garage, which verifies the signature.
The key selector is not authentication by itself. Default configuration denies
all deletes; bucket/configuration deletes and bulk deletes remain denied even
for GC. Query keys are decoded before enforcing the denylist; malformed or
ambiguous nested encodings are rejected. The live test grants a fresh GC key on the W4 instance, deletes only its
test object, and revokes that key's bucket permissions afterwards.

### Verification and measurements

The new `W4Scale` model passed 428,800 distinct states at its bounded scope:
two shards, two holders, three snapshot incarnations and two logical versions.
Its six witnesses cover takeover, publication after takeover, cross-shard
publication, reclamation, recovery fetch and retention. Ten guard mutations cover
term, expiry, dependency closure, pending/demand/checkpoint/catalogue/retained
roots, grace and unsolicited fetch. All sixteen produced their expected
counterexamples. The recovery witness explicitly requires a fetch, desktop loss,
and a subsequent requested fetch; an earlier witness that could succeed before
desktop loss was strengthened during review. This is bounded safety/reachability evidence, not a temporal
proof of eventual takeover under every schedule. The model abstracts each shard
as one authoritative holder/term; FDB conflict serialization and live tests,
rather than this abstraction alone, support the leader-uniqueness argument.
Its cross-shard dependency is one fixed edge, with P2 certificate enforcement
tested separately. Recovery checks fetching a live root after loss, not discovery
of an unknown head. Snapshot incarnations are distinct from reusable byte hashes.

`verification/veil/Paralean/ControllerGc.lean` proves local transition lemmas:
collecting an unreachable incarnation preserves reachable and recovery roots;
stale terms cannot satisfy the write guard, including after term increment.
Two further lemmas establish that an atomic batch move from current history to
replay storage preserves retry coverage and that selecting only terminal records
preserves pending work. These assume atomicity and unchanged record contents.
`scripts/check-w4-lean.sh` checks these using `Std` only and a private output path.
The standalone check passed on Lean 4.32.0; its log is archived as
`verification/results/lean/ControllerGc.log`. Existing Veil archive logs are
preserved by `--tla-only`; the full Veil dependency suite was not rerun. These
lemmas do not establish a Rust refinement or full-system liveness.

`W4History` separately checks the local history-compaction transition with two
holders, two request payloads, one work ID, one poll token and two logical ticks.
Its positive run explored 3,780 distinct states. Seven witnesses and eleven
mutations check compaction, late replay, handover, GC-disabled replay,
cancellation overlay, terminal-only selection, marker creation, identity/worker
binding, logical grace and fencing. It abstracts a batch as one atomic store
transition; multiple-key crash/unknown-commit behavior must also be tested in
the implementation. Old retained snapshot bytes are an assumption of this
model, separately guarded and checked by `W4Scale` and snapshot-GC tests.

Initial live evidence: logical lease/shard tests, GC root/grace/retention tests,
concurrent load/collection, new incarnation reuse, and cross-shard dependency
publication passed. The dependency test also tries the adversarial staging-bypass
entry point before the prerequisite publishes. The real process test injects
`CLOCK_REALTIME` skew of +100 and -100 days through a compiled preload shim,
verifies that injection independently with `date`, then uses SIGSTOP/SIGCONT.
The focused timing run preserved the queued request in 1.440 s and the other shard remained
leader. No Lean validator runs in this timing test.

Integration review also fixed a failover edge: if a worker expired before its
replacement registered, the target was fenced to the unowned sentinel but the
job stopped being proactively assignable. The controller now retains that
durable unowned state, resumes its assignment intent, and lets either the
monitor or a later poll assign it. Poll retries preserve the same assignment.
A deterministic test detects removal of the poll handoff guard. Another
regression covers replaying an existing P2 assignment: the transaction must
commit a newly created shard claim even when no target epoch changes.

The final focused run passed 20 tests (11 durable, four GC integration tests,
two GC library/scheduler tests, and three cross-shard/process/worker tests). Broader checks passed
auth 2, controller 6, process 4, target 5 and adversarial 13, for **50 distinct P3
tests**, plus the separate benchmark. Nine controller mutation cases and six GC
mutation cases were detected; the S3 guard adds three unit tests, three mutation
cases and seven live checks. Logs are under `impl/p3/results/w4-*.log`.
The initial adversarial transcript retains a missing-fixture failure. The later
combined run in `impl/p3/results/w4-final-tests.log` passed all 61 selected P3
tests, including all thirteen adversarial cases with matching fixtures.
The final history suite separately passed twelve tests, adding one same-worker
epoch regression to that combined run for **62 distinct P3 tests** overall.
All **33 implementation mutation cases** were detected: nine controller,
six snapshot GC, fifteen history and three S3-guard cases. The controller and
snapshot-GC mutations were rerun after the final history integration.

`impl/p3/results/w4-scale.json` records a debug-build, direct-controller-API sample
against W4's real FDB instance. No validation RPC or Lean compilation is included.

| Shards | Queued jobs | Submissions/s | Store-tick failover + recovery |
| --- | ---: | ---: | ---: |
| 1 | 512 | 61.29 | 0.043 s |
| 2 | 512 | 99.57 | 0.109 s |
| 4 | 512 | 169.97 | 0.331 s |

Every shard recovered all its queued jobs. The GC leg wrote four generations of
3 MiB per shard, reclaimed twelve obsolete snapshots (36 MiB), and recovered all
four current snapshots (12 MiB) through fresh reader objects. The reclaimed count
is deleted logical payload, not a measurement of FDB's allocated disk footprint.
Writing, collection
and recovery took 2.551 s. The history leg compacted 256 terminal work records and
128 poll outcomes, reducing the current snapshot from 47,121 to 349 bytes in
0.199 s. A fresh controller with GC disabled still rejected recreation of an old
work ID and kept an old NoWork token from taking new work. Durable replay records
remain stored, so the snapshot-size reduction is not a claim of deleting those
identities from FDB. These are shared-host single samples, not production
capacity estimates or controlled speedup distributions.

`impl/p3/results/w4-guard.json` records live gateway checks:
application denial, forged GC signature denial, GC denied by default, bucket
and bulk denial (including encoded query keys), and authenticated GC object deletion. P5's local Python suite
ran 28 tests: 26 passed, two environment-dependent tests skipped.

Broader P3 regressions use a privately rebuilt pinned stock P1 checker and fresh
matching fixture captures. Earlier copied binaries/fixtures had a different
Lean base and were discarded as test inputs. The fixture capture's independent
whole-corpus check reported 95/97 source-replay groups, 97/97 kernel-replay groups,
and four export mismatches in F10/F13; this is not a passing whole-P1 claim.
All P3 inputs, including F01/F05 and the four rejected negative captures, were
captured with the matching checker. No shared Mathlib or toolchain cache was
rebuilt.

The complete TLA refresh passed 23 positive scenarios, 119 negative-suite
expected outcomes and 29 hardened cases. Re-archiving with
`scripts/archive-verification.sh --tla-only` and then `--verify` passed; the
verification transcript is `impl/p3/results/w4-archive.log`.

Four existing wide TLC logs are preserved from the base archive after checking
every parsed source hash against the current files; those models are unchanged
and were not rerun. The default positive/negative suites and hardened suite are
fresh runs for this workstream. The older full Veil logs are also retained, with
the new standalone W4 Lean log added separately.

## Reproduction

```sh
source impl/p3/scripts/w4-env.sh
bash impl/p2/scripts/up.sh
cargo test --manifest-path impl/p2/Cargo.toml -p paralean-control -j1 \
  --lib --test durable --test gc --test w4_history --test w4_dependencies --test w4_processes --test w4_workers \
  -- --test-threads=1
W4_SCALE_REPORT="$PWD/impl/p3/results/w4-scale.json" \
  cargo test --manifest-path impl/p2/Cargo.toml -p paralean-control -j1 \
  --test w4_scale -- --ignored --nocapture --test-threads=1
bash impl/p3/scripts/check-w4-mutations.sh
bash impl/p3/scripts/check-w4-gc-mutations.sh
bash impl/p3/scripts/check-w4-history-mutations.sh
bash impl/p2/scripts/check-s3-guard-mutations.sh
cargo build --manifest-path impl/p2/Cargo.toml -p s3-guard -j1
python3 impl/p3/scripts/w4-guard-test.py
bash scripts/check-w4-lean.sh
bash scripts/check-tla.sh
bash scripts/check-tla-negative.sh
TLC_WORKERS=4 bash scripts/check-tla-hardened.sh
bash scripts/archive-verification.sh --tla-only
bash scripts/archive-verification.sh --verify
```

The process test needs `cc` and the pinned installed Lean toolchain for controller
checker-identity setup, but uses `/bin/true` as the hashed checker file because no
validation job is requested. The gateway test needs boto3 and requests.

## Proposed plan.md and README.md sentences

Plan: “W4 replaces controller authority deadlines with per-shard store counters
and term fences, and adds fixed controller shards, opt-in history compaction
with durable replay records, and collection of superseded controller snapshot
generations. Per-shard snapshot limits, online resharding, retirement of replay
IDs and protocol-object GC remain separate work.”

README: “Controllers support independent fixed shards, store-ordered leases and
disabled-by-default history compaction and snapshot GC. Protocol objects and
durable replay records remain retained; the optional GC S3 principal is authenticated by Garage. See
docs/w4-log.md for checks, scale measurements and remaining limits.”

## Final summary — 2026-10-20

Verified implementation commit:
`296e08b9a6d32dc9258f7a1d71268444461b7a24`, pushed to `origin/w4-scale`.
The preceding S3-principal checkpoint is
`128cf15db8fc4a6e046fce10cbbabceb95e143fb`. This summary and the consolidated
verification report are recorded in a subsequent documentation commit.
`origin/main` remains `fee94d9`; no rebase was needed.

| Item | Result and evidence |
| --- | --- |
| 1. Logical leases | Implemented shard-local store counters and transactional holder/term/expiry fences. The live process test injects opposing 100-day wall-clock offsets and a paused leader, preserves queued work through takeover, and leaves the other shard's leader active. `W4Scale` checks bounded fencing/handover behavior and its guard mutations fail as expected. |
| 2. Controller sharding | Implemented fixed target-key routing, separate FDB heads and elections, shard-local validation recovery indices, and worker polling/heartbeats across shards. Cross-shard prerequisite publication is tested. Four current shard snapshots totaling 12 MiB recover successfully, exceeding the former global cap. |
| 3. GC protocol | Disabled by default. Logical grace, atomic replay-record creation and history pruning, current-head/pin protection, incarnation revalidation and fenced deletion are implemented. Twelve history tests include crash-boundary recovery, late retries with GC disabled, cancellation overlay, epoch-bound poll tokens and bounded-scan progress. S3 guard admits only authenticated GC-principal object deletion; default, application, forged, bucket and bulk deletes are denied. |
| 4. Scale tests | Completed on the private W4 instances. One/two/four shards measured 61.29/99.57/169.97 submissions per second, with all 512 jobs recovered in each sample. GC deleted 36 MiB of superseded snapshot payload. History compaction moved 256 work and 128 poll records to replay storage and reduced the current snapshot from 47,121 to 349 bytes. |

Final evidence: **62 distinct P3 tests**, one explicit live benchmark, **33
implementation mutation cases**, three S3-guard unit tests and seven signed live
gateway checks passed. P5 ran 28 local tests: 26 passed and two environmental
cases skipped. The final combined P3 run passed 61 tests; the final twelve-test
history run overlaps eleven of them and adds the epoch regression.

TLA passed **23 positive scenarios, 119 negative-suite expected outcomes and 29
hardened cases**. The two new models explored 428,800 and 3,780 distinct states;
their 13 witnesses and 21 mutations produced the required counterexamples.
Six standalone Lean transition lemmas passed. Four unchanged wide-model logs
were retained after source-hash verification, and existing full Veil logs were
preserved; those suites were not rerun. Both re-archiving with `--tla-only` and
the final `scripts/archive-verification.sh --verify` passed.

Remaining scope is explicit: topology is fixed, each shard retains its 8 MiB
active-state cap, and online resharding/legacy migration are not implemented.
Oversized replay records remain in the current snapshot, and grace stamping
requires headroom. Replay IDs and global protocol/routing records remain
retained because forgetting them would break unlimited retry, anti-entropy or
recovery semantics. Physical P2/S3 object GC requires a distributed retirement
protocol covering disconnected peers and stale advertisements; it is not
enabled or claimed safe here. The models and Lean lemmas are bounded/local
evidence, not a Rust refinement or full-system liveness proof.

The private W4 services are stopped, their data is retained, and no shared
instance or Mathlib cache was modified. Detailed commands, transcripts and
measurements are above and in `impl/p3/results/w4-verification.json`.
