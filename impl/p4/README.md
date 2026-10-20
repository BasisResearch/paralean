# P4 interactive workspaces

`lsp.py` is a stdio JSON-RPC router for persistent Lean servers. Each workspace
has its own process, store, environment identity and generation. Use
`python3 impl/p4/lsp.py --help` for routing and worker environment configuration.
The underlying command can be a local Lean executable or a transport wrapper
that provides a remote worker's stdin/stdout. For example, use
`--worker-command 'alice=["ssh","host","/path/to/worker-wrapper"]'` with
`--worker-root alice=/remote/workspace`. The wrapper must set the remote
environment and make the remote source tree available. Per-workspace
`--workspace-env NAME=JSON_FILE` configures local worker environment variables.
`--environment NAME=ID` pins the base and policy identity supplied by the controller.
Registry and trust changes additionally invalidate the worker automatically.

The P4 fork automatically imports `Paralean.Visibility` when Paralean mode and
`PARALEAN_STORE` are enabled. Put the built P1 library on `LEAN_PATH`. The
editor's source text and positions remain unchanged.

For a local worker after sourcing the P1/P3 environment:

```bash
LEAN_PARALEAN=1 LEAN_PATH="$PARALEAN_LIB${LEAN_PATH:+:$LEAN_PATH}" \
  python3 impl/p4/lsp.py --workspace alice=/path/to/alice
```

Include the pinned Mathlib library paths in `LEAN_PATH` when the copy imports
Mathlib. A remote wrapper must set these variables on the worker host.

The router supports ordinary LSP hover, goals, completion (including resolve),
rename, diagnostics and cancellation. `paralean://NAME/path.lean` addresses a
workspace without exposing its worker path. `workspace/symbol` and
`paralean/search` combine worker symbols with published registry names;
`paralean/source` returns the current buffer or source file with its stamps.
RPC sessions and completion items are bound to their original document,
environment and worker generation.

## Incremental publication capture

Run one `paralean ws-capture-server --dir COPY` per document with the copy's
`PARALEAN_STORE`, `PARALEAN_TRUST` and `PARALEAN_PLR` environment. Send JSON lines:

```json
{"file":"Example.lean","text":"def a := 1\n","version":1,"environment":"base-and-policy-id","generation":1}
```

The response includes the exact input stamps, the registry digest, elapsed
milliseconds, reused/new command counts, and the ordinary `ws-capture` package
list. Imports are retained in the process. An edit resumes at an unchanged
command boundary and captures the changed suffix. Changes to registry records or
trust invalidate command snapshots. A changed document, base environment or
worker generation requires a new process; non-increasing versions are refused.
This worker stages capture artifacts; publication still goes through the
validator, planner and store.

## Collision resolution and Git projection

`workspace.py resolve COPY FILE RENDERED_NAME` follows the tombstone option in
§11.5. Give the exact losing name printed by the collision diagnostic. The
store enforces that only the losing declaration's author can delete it. The tool
pulls, advances the persisted Lamport clock, sends the signed tombstone, pulls
again and updates the working copy. Publish a replacement under a new ordinary
name if needed, then use the checkpoint workflow. A rendered collision name
alone does not resolve the conflict.
The result includes candidate `checkpointArgs` and `checkpointFiles`, selecting
only the resolved file's live revision heads. After checking the revised drafts
and exporting that selection, submit those arguments to `plr` in the controller's
authority context. The per-agent key used for the tombstone cannot issue the
controller's checkpoint token. Recompute the selection if more records arrive;
`paralean ws-live` exposes all live heads for a broader snapshot plan.

`workspace.py project COPY` creates `paralean/projection` and
`paralean/agents/<author>` branches using Git plumbing. Each new record adds a
commit whose parents preserve both the previous projection and that author's
history. A late record therefore never rewrites a published commit. Each tree is
rendered from full capsule source by Lean's canonical RGA for the records applied so far,
with each capsule's captured scope. Commit history
reflects arrival order; the final Lean source bytes converge. The tool does not
modify HEAD, the working files or the user's index.

`workspace.py snapshot COPY --workspace NAME --catalog CATALOG_ID` recovers the
certified snapshot from the store and renders it in an isolated cache. It creates
the immutable tag `paralean/snapshot/<snapshotID>`. Repeating the operation is
idempotent; a tag already naming different source bytes is an error.

Source `scripts/env.sh` only for this workstream's isolated test cluster.
Gate results and limitations are recorded in `../../docs/p4-log.md`.

## Reproducing the editor gates

Build the pinned fork with `fork/build.sh` and P1 with that fork, then prepare the
P3 services under `PARALEAN_INSTANCE=m-p4`. Source `impl/p4/scripts/env.sh` from
the repository root. Set `PARALEAN_BIN` and `PARALEAN_LIB` to a matching built
runtime; keep those artifacts unchanged while a gate is running.

```bash
export LEAN_PARALEAN=1
export LEAN_PATH="$PARALEAN_LIB${LEAN_PATH:+:$LEAN_PATH}"
python3 impl/p4/tests/editor.py --samples 10 --kill-worker --label Init
python3 impl/p4/tests/native_restart.py
python3 impl/p4/tests/capture_test.py --samples 10
python3 impl/p4/tests/capture_test.py --samples 10 --label Mathlib
```

`remote_editor.py COPY --extra-checks` uses the published Bob copy from the P3
remote gate. Add `--mathlib` for `Mathlib.Order.Basic`. The capture gate accepts
`--published-copy COPY --file Shared.lean` for the same remote prefix.
`projection_test.py COPY --workspace bob --catalog CATALOG_ID` checks full
source history and an existing certified snapshot.

For isolated correctness fixtures, use a new output directory for every run:

```bash
python3 impl/p4/fixtures/interactive.py instances .runs/p4-instances-new
python3 impl/p4/tests/interactive_editor.py .runs/p4-instances-new/manifest.json
```

Repeat with `open17` and `revocation`. The revocation test intentionally revokes
that fixture's validator key. For a fresh collision resolution, generate
`collision` and pass its `bob` subdirectory to `tests/collision_test.py`.
Fixture generation and collision/revocation tests write only to the configured
isolated deployment; run fixture generators sequentially because their temporary
validator uses port 18691.
