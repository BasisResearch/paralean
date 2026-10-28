# Scaling archive — incomplete study

No production N=1/2/4/8 samples or actual-agent confirmation completed. Do not
use this archive as a controlled speedup result. See [the report](../../docs/scaling-study.md).

- `pilot-list-stock-r0`: rejected proof-script pilot; compiler errors retained.
- `pilot-list-stock-r1`: corrected stock pilot (single sample).
- `pilot-list-p1-r0`: successful ten-target Paralean pilot, phase trace, validator
  queue/fetch/checker timestamps, scoped transfer totals, contract checks and export log.
- `pilot-synthetic-stock-r0`: earlier 2,000-iteration metaprogram, stock only.
- `pilot-synthetic-p8-r0`: 20,000-iteration metaprogram; heartbeat failures and exact
  owned-tree termination. Failed/aborted, excluded from performance inference.
- `pilot-synthetic-p8-r1`: 100-iteration metaprogram; worker checks passed but the
  independent validator rejected capsule replay. Failed, excluded.
- `pilot-synthetic-p8-r2`: ordinary-tactic task staging only, stopped at load gate;
  `blocked.json` is explicit that no measurement ran.
- `pilot-list-phase-summary.json`: derived from that pilot's raw trace, with nested
  phase scopes. `summary.json`: empty production summary, retained to show no samples.
- `provenance.json`, `setup/`, `setup-commands.txt`: binary hashes, compiler versions,
  machine metadata, build logs and commands. No keys or full environments.
- `resource-block/`: complete suite/load wait logs and ownership-checked shutdown.

`result.json` in each completed pilot contains exact argv, source revision, task
hash, process wall/CPU time and start/end host load. The earliest stock pilots
have a null UTC field because of an initial harness bug. The r1 synthetic pilot
recorded staging UTC before its long load wait; its actual controller event times
are in `run.json`. Production code now timestamps subprocess starts after the load
gate. Timing instrumentation changed while that pilot waited, so pilot revision
metadata does not represent a production freeze. Proof generators for its
metaprogram were unchanged. All pilots remain outside production inference.

The stock baseline is one source file containing all targets in DAG order.
Paralean additionally freezes contracts, provisions private workspaces, captures,
independently validates and durably publishes. Stock provides no matching storage
or receipt guarantees. This is an overhead comparison on supplied proof scripts,
not a proof-search benchmark. The old synthetic stock and Paralean parameters
differ and must not be compared.

The controller tree's child CPU seconds exclude the long-lived storage services;
per-run service CPU deltas are separate. Workspace transfer bytes exclude validator
fetches, task journals and transport overhead. RPC latency is not checker CPU or
queue wait. Validator logs measure semaphore queue time directly.

## Resume when the shared host is available

From the repository root, with access to the same read-only fork and install:

```sh
bash scripts/scaling/run.sh > .runs/scaling/resumed-suite.log 2>&1
python3 scripts/scaling/summarize.py
```

`run.sh` rebuilds removed intermediates using `build.sh` if necessary, with load
gates and two build jobs. It uses fresh pilot r3, requires successful independent
validation **and clean export**, then executes three blocks of all six
configurations for each workload (36 production runs). It performs the List
remote/local/replay profile and the one-sample N=1/N=8 actual-Claude pair. It stops
only the owned `p5-scal-20261028` services through an EXIT trap. Existing completed
run directories are never overwritten. If a further attempt creates these same
IDs, choose a new series/pilot ID before resuming again.

Production synthetic work is 100 ordinary `have`/`decide`/`clear` pairs per
branch. This variant has not yet passed the pilot. Preserve that fact until it
does. There is no artificial LLM delay. The real-agent pair remains descriptive,
with reported model IDs and CLI overlap recorded; transcripts remain private.

The previous successful List pilot's runtime cache and private instance data
remain locally under `.runs/scaling/` for the representative profile; they are
not committed. Build products under `impl/p1/.lake`, `impl/p2/target` and the
pilot export `.lake` were deleted. About 128 MB of owned runtime evidence remains.
