# P4: distributed LSP and interactive workspace follow-up

Workstream `m-p4`, starting at `7df9ace`. Implementation and tests were delegated
in disjoint scopes, then reviewed and integrated by the primary agent. The
requested `gpt-6.1-sol` model was rejected by the subagent tool as unavailable;
the available `gpt-6-sol` was used.

This log is in progress. Gate completion is recorded below only after the
corresponding runs finish.

## Isolation and baseline

All service writes use `PARALEAN_INSTANCE=m-p4`, the `.runs/m-p4-cluster`
directory, FoundationDB port 4799, Garage ports 18639–18641 and S3 gateway 18633.
The validator uses port 18691. Existing fork and Mathlib artifacts were initially
read from the previous P3 checkout; the modified fork uses a private copy.
The fork build is limited to two jobs.

The unchanged P3 remote gate passed on this cluster in 180.9 seconds:
helper sharing, B→A→B, invalidation and stale response rejection, retained
snapshots, random-order projection convergence, supersession/deletion, collision
rename, winner revision, forgery rejection, clean export and the axiom audit.
This baseline uses the old `dfc13cc6` fork; it is not evidence for the P4 changes.

## Components

- `impl/p4/lsp.py`: persistent Lean workers, URI routing, exact response stamps,
  source/search aggregation, cancellation and RPC session affinity.
- `impl/p1/Paralean/Interactive.lean`: a persistent capture protocol over JSON
  lines. `Capture` and `Driver` retain complete command continuations and resume
  the unchanged prefix. Base imports are cached.
- `impl/p1/Paralean/Remote.lean`: capsule scope isolation and live receipt checks.
- `impl/p4/workspace.py`: guided author-owned tombstones, history-preserving
  projection branches and tags reconstructed from certified snapshots.
- `fork/patches/0007-*`: interactive import and imported-environment hooks,
  gated on Paralean mode and a configured working-copy store.

## Editor transport checkpoint

The real JSON-RPC client passed two-workspace routing, virtual and remapped
worker URIs, search/source, hover, goals, completion and resolution, rename,
cancellation, rapid ranged edits, watchdog death/reconnect and environment
replacement. RPC calls to `Lean.Widget.getInteractiveGoals` work on their
own document; references sent to another document or workspace are refused.
Old RPC sessions and completion items expire after replacement.

The primary agent independently reran three edits with worker-root remapping
and death/reconnect: PASS, with 379 ms reconnect-to-diagnostics. An earlier
independent run caught a `/Users` versus `/data` URI alias regression; both the
ordinary and remapped tests passed after normalization was fixed.

Ten-sample ordinary-source runs (milliseconds, p50 / p95) are stored in
`impl/p4/results/editor-{init,mathlib}.json`:

| Request | Init, all 10 | Mathlib, all 10 | Mathlib, 9 warm |
|---|---:|---:|---:|
| edit → error diagnostics | 214 / 263 | 214 / 1000 | 213 / 223 |
| edit → clean diagnostics | 211 / 225 | 216 / 269 | 214 / 263 |
| hover | 4.8 / 7.1 | 6.4 / 74 | 6.9 / 78 |
| goals | 5.5 / 10 | 4.3 / 7.1 | 4.1 / 7.1 |
| completion | 69 / 172 | 253 / 931 | 229 / 341 |

The Mathlib test imports `Mathlib.Order.Basic`; it does not load all Mathlib.
Its first error-producing edit took 1.63 s in this run (28.1 s in an earlier
colder run on the shared box). The warm figures exclude the first request.
These transport measurements use ordinary Lean source on the previous fork;
the `remote%` measurements require the new hook and are recorded separately.
No network speedup is claimed: remote-root mapping was tested with a local
mirror directory, and the SSH transport command itself has not been exercised.

## Sentences for plan.md and README.md

Proposed plan.md P4 text, to be finalized after the gate:

> P4 implements persistent Lean worker routing and a scripted JSON-RPC editor
> gate in `impl/p4`, with version, environment and generation checks and
> session-affine RPC references. See [p4-log](p4-log.md) for measured latency,
> death/reconnect results and remaining limitations.

Proposed README.md text:

> Interactive workspaces use persistent Lean servers and incremental capture.
> `impl/p4` adds distributed LSP routing, collision-resolution tooling and
> history-preserving Git projections; see [docs/p4-log.md](docs/p4-log.md).
