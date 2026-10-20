# P4 interactive workspaces

`lsp.py` is a stdio JSON-RPC router for persistent Lean servers. Each workspace
has its own process, store, environment identity and generation. Use
`python3 impl/p4/lsp.py --help` for routing and worker environment configuration.
The underlying command can be a local Lean executable or a transport wrapper
that provides a remote worker's stdin/stdout.

The P4 fork automatically imports `Paralean.Visibility` when Paralean mode and
`PARALEAN_STORE` are enabled. Put the built P1 library on `LEAN_PATH`. The
editor's source text and positions remain unchanged.

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

`workspace.py project COPY` creates `paralean/projection` and
`paralean/agents/<author>` branches using Git plumbing. Each new record adds a
commit whose parents preserve both the previous projection and that author's
history. A late record therefore never rewrites a published commit. Each tree is
rendered by Lean's canonical RGA for the records applied so far. Commit history
reflects arrival order; the final Lean source bytes converge. The tool does not
modify HEAD, the working files or the user's index.

`workspace.py snapshot COPY --workspace NAME --catalog CATALOG_ID` recovers the
certified snapshot from the store and renders it in an isolated cache. It creates
the immutable tag `paralean/snapshot/<snapshotID>`. Repeating the operation is
idempotent; a tag already naming different source bytes is an error.

Source `scripts/env.sh` only for this workstream's isolated test cluster.
Gate results and limitations are recorded in `../../docs/p4-log.md`.
