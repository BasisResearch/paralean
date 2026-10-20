# P4: distributed LSP and interactive workspace follow-up

Workstream `m-p4`, starting at `7df9ace`. Implementation and tests were delegated
in disjoint scopes, then reviewed and integrated by the primary agent. The
requested `gpt-6.1-sol` model was rejected by the subagent tool as unavailable;
the available `gpt-6-sol` was used.

The completed gates below use real Lean processes and a framed JSON-RPC client.
Results distinguish ordinary-source transport, published `remote%` loads and
the separate incremental capture protocol.

## Isolation and baseline

All service writes use `PARALEAN_INSTANCE=m-p4`, the `.runs/m-p4-cluster`
directory, FoundationDB port 4799, Garage ports 18639–18641 and S3 gateway 18633.
The validator uses port 18691. Existing fork and Mathlib artifacts were initially
read from the previous P3 checkout; the modified fork uses a private copy.
The fork build used at most four jobs; simultaneous build/test work was kept
below the eight-heavy-process budget. Disk space was checked before large runs.

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

The private `fork/build.sh` rebuild passed at
`99967f1ee50a1ee82bb178359ad95b723c8196a2`; the primary agent independently
checked that the built `lean --githash` matches `fork/GITHASH`.
The full P1 build passed 80/80 targets. The five Paralean fork tests passed,
and the mode-off `server` / `server_interactive` regression subset passed 158/158 in
286.2 seconds. Evidence is in `fork/results/p4-*.txt`.

The fresh P3 gate on this fork passed in 195.2 seconds, including clean export
(11/11 groups re-encoded identically), forged-remote rejection and the axiom
audit. Its evidence is `impl/p4/results/p3-regression.json`. One earlier run
was invalidated by a concurrent library rebuild; subsequent runs used frozen
binary/library directories. The broader P1 test also found a numeric-name
panic in the new field collector and an invalid UTF-8 slice before identifiers;
the collector now pattern-matches names and checks the preceding raw byte.
The final P1 core run reproduces the baseline: source, kernel and isolated
replay each pass 103/103 groups, and the exported package builds. Export identity
verification remains 81/85 declaration groups plus 18 build-checked effect
groups, with the same four initializer mismatches at F10SimpAttrDecl:4 and
F13InitDecl:6/8/10 as `impl/p1/results/fork/core.log` and
`docs/p1-gate.md`. Consequently that script exits 1; it is not an all-green
export-identity gate. No new mismatch or capture panic remains.
The negative suite matches the baseline too: N1–N6 reject, the malicious
captures stage no new publishable groups, N3's audit fails kernel checking,
and concurrent version/instance conflicts prevent export. N5 retains its three
previously valid groups. Logs are `fork/results/p4-p1-{core,negative}-v3.txt`.

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

## Interactive measurements

Compiled persistent capture, ten suffix edits, milliseconds:

| Base | First capture | Edit p50 | Edit p95 |
|---|---:|---:|---:|
| Init | 1898 | 125 | 259 |
| Mathlib.Order.Basic | 6093 | 177 | 287 |
| Init, published `remote%` prefix | 1378 | 370 | 647 |
| Mathlib.Order.Basic, published `remote%` prefix | 1838 | 399 | 442 |

Each run reused the unchanged command prefix and produced the same package,
group and capsule IDs as a separate clean capture. It also rejected stale
document/environment/generation stamps, removed a deleted unpublished
declaration and published no records. The published-prefix runs reuse six
commands and elaborate two suffix commands. The other rows use two local
declarations. These are separate fixtures, not a comparison of identical work.
The previous P3 figure of about 700 ms per Init step included process startup;
these warm edits reuse a process and imported base, with different fixture sizes.

The actual `remote%` LSP gates passed ten edits after the initial file load.
Init additionally checks local-instance isolation and rejection of a same-name
declaration replacing a previously verified constant. Latencies in milliseconds:

| Request | Init p50 / p95 | Mathlib.Order.Basic p50 / p95 |
|---|---:|---:|
| edit → error diagnostics | 213 / 235 | 212 / 218 |
| edit → clean diagnostics | 211 / 218 | 213 / 217 |
| hover | 5.5 / 8.4 | 7.1 / 11.5 |
| goals | 6.0 / 9.5 | 8.2 / 11.8 |
| completion | 193 / 550 | 232 / 631 |
| completion, 9 warm | 191 / 253 | 223 / 264 |

Single watchdog reconnects took 1824 ms and 2037 ms respectively.
See `impl/p4/results/remote-{init,mathlib}-final.json`; these ten-sample
percentiles are descriptive measurements on a shared machine.

The primary agent independently repeated three `remote%` edits and reconnect:
PASS (error diagnostics 212/219 ms, hover 6.2/9.4 ms, goals 6.4/8.0 ms,
completion 191/766 ms including an 829 ms first completion; reconnect 1819 ms).
It also independently killed the native Lean file worker: the router advanced
generation 1 → 3, replayed an edited `Bool` declaration, returned a `Bool` hover,
and refused the previous RPC session. This caught and fixed both a kill/ack race
and Lean's stale-version fatal notification leaving its file worker crashed.
On the final compiled runtime it also exercised incremental capture of the
published OPEN-17 fixture: three edits reused seven commands and captured two,
matched fresh-process IDs, rejected stale stamps and left the record log
unchanged (`capture-open17-review.json`). This larger fixture took 3518 ms on
first capture and 664/694 ms p50/p95 for suffix edits.

## Interactive correctness

The isolated real-LSP fixtures in `impl/p4/fixtures/interactive.py` passed:

- A root-scope local instance returning 999 cannot poison a capsule whose pinned
  global instance returns 41; an editor proof checks the value 41.
- Two published `Foo.field` declarations collide. A published dependent
  `Foo.use` retains its intended losing dependency: source projection rewrites
  `x.field` to `x.«field✝plaaa22b5e»`, preserves unrelated `y.field`, and
  an editor proof checks the result 2. Both payload verification and elaboration
  succeed.
- After signed validator-key revocation, a second `remote_decl%` in the same
  open document rejects the previously cached group as revoked. Advancing the
  environment policy epoch and replaying the original document rejects it too.

Evidence is in `impl/p4/results/interactive-*-final.json`. The final ordinary
editor smoke also cancels a request, sends an inactive duplicate cancellation,
then successfully reuses the numeric request ID for hover. It repeats routing,
search/source, rename, completion resolution, RPC affinity and reconnect.
The router removes completed requests from its cancellation bookkeeping.

The projection gate passed with 17 records, including insertion of a late
lower-Lamport record. Previous commits remain ancestors, repeated projection is
idempotent, and opposite record delivery orders produce identical full-source
trees. HEAD, staged changes and a dirty draft remain unchanged. Recovering a
certified snapshot twice produces the same immutable tag and source without
`remote%` stubs (`projection-final.json`).

The fresh OPEN-26 gate takes the guided tombstone path, revises the affected
draft, checks it, and issues an authority checkpoint for exactly the resolved
file's two live revision heads. Its certified snapshot retains the winner,
excludes the loser and compiles as full Lean source with Paralean mode off.
The tool's returned `checkpointFiles` and revision list match the tested
selection. Evidence is `collision-fresh-final.json`; catalog
`15037978e0f352722d2c20fbc182023e651b966150a962bbd4b8c392ca3e7411`,
snapshot `ca8508654e1b1937779e7d39e6057106748324e11d0725c8b56b86205dd4e3bb`.

## Integration boundaries

The router accepts a worker command, worker filesystem root, environment
variables and a controller-provided environment identity for each workspace.
The transport wrapper must provision the remote source tree and environment.
The capture daemon is a separate persistent process per document, exposing
stamped JSON lines for the controller; the LSP router does not publish editor
buffers automatically.

`remote%` checks the store's current receipt policy on load and cached reuse.
The capture daemon also rechecks retained packages before each capture.
An already elaborated LSP prefix is a snapshot: the controller must advance
the workspace environment identity when revocation policy changes to invalidate
it. This workstream does not add a store-to-editor policy push feed.

OPEN-26's guided tool takes the author-owned tombstone path, then allows the
ordinary checkpoint workflow. The baseline P2 checkpoint implementation does
not enforce the model's complete `buildable` / `current` conflict rule.
That backend rule belongs to m-p2; the P4 test must not be read as evidence
that the backend rejects every unresolved collision before resolution.

Git projection branches retain arrival history and use full capsule source,
including captured scopes. Different delivery orders can produce different
commit histories; after the same records arrive, source trees converge.
Snapshot tags are immutable. These source views do not replace the existing
dependency-closure export and its stock-build checks.

For old capsules without resolved field references, a dependency rename that
requires generalized field rewriting is refused with a recapture diagnostic.
New captures record the resolved declaration and byte span for field notation;
rewritten capsules still undergo payload and kernel checks.
This tests relocation of an already resolved generalized field reference.
Discovering a previously unloaded method solely from arbitrary `x.field` syntax
is not implemented; the fixture explicitly loads the unrelated method.
Registry search locations use captured capsule positions and may be approximate
after projection rendering; source text and response stamps remain exact.

## Sentences for plan.md and README.md

Proposed plan.md P4 text:

> P4 implements persistent Lean worker routing and a scripted JSON-RPC editor
> gate in `impl/p4`, with version, environment and generation checks and
> session-affine RPC references. See [p4-log](p4-log.md) for measured latency,
> death/reconnect results and remaining limitations.

Proposed README.md text:

> Interactive workspaces use persistent Lean servers and incremental capture.
> `impl/p4` adds distributed LSP routing, collision-resolution tooling and
> history-preserving Git projections; see [docs/p4-log.md](docs/p4-log.md).
