# P5 autonomous controller

P5 drives ordinary coding CLIs in private Lean workspaces. Its task graph and
frozen contracts are stored separately from the published declaration library.
P3 supplies capture, `remote%`, validator receipts and export; P2 supplies
FoundationDB metadata and Garage payloads. P5 adds a small store adapter rather
than modifying those implementations.

```sh
export PARALEAN_INSTANCE=p5-m-p5
source impl/p5/scripts/env.sh
impl/p5/scripts/cluster-up.sh

# With the pinned P1/P3 binaries built:
CARGO_TARGET_DIR="$PWD/impl/p2/target" \
  cargo build --release --locked --manifest-path impl/p5/store-bridge/Cargo.toml -j2
python3 -m unittest discover -s impl/p5/tests -v

export PARALEAN_DEPLOYMENT=p5-example
python3 impl/p5/paralean.py run impl/p5/tasks/list_reverse_map_lengths.toml --worker claude

# On a replacement desktop, with deployment credentials configured:
python3 impl/p5/paralean.py list
python3 impl/p5/paralean.py recover list-reverse-map-lengths-v1
```

The environment script selects P5's own cluster, a pinned read-only fork compiler
and the unmodified stock compiler for exports. On another box, override
`PARALEAN_FORK_PREFIX`, `PARALEAN_P2_BIN_PREFIX` and the P5 port/prefix variables.
Build P1/P3 using their README instructions before running P5. Python 3.11 or newer
and `cryptography` are required. Workers use the box's existing CLI authentication;
do not put API secrets in task files or command arguments.
The deployment recovery secret must be kept separately from worker credentials.
The provided cluster environment derives it from the existing Garage
administration credential and excludes it from worker environments.

`--workers N` selects logical workspaces. `--parallelism N` bounds simultaneous
worker CLIs and defaults to at most four. On the shared box, budget for the store,
validator and checker as well as the workers. Task metadata supports explicit
dependencies and fixed owners. A worker writes an ordinary Lean file; the
controller captures and validates its completed declarations before making them
available to successors.

Run the live recovery gate and scaling suite against a cluster you own:

```sh
python3 impl/p5/scripts/gate.py .runs/p5-gate --worker claude \
  --task impl/p5/tasks/list_reverse_map_lengths.toml
python3 impl/p5/scripts/adversarial.py .runs/p5-adversarial
python3 impl/p5/scripts/benchmark.py .runs/p5-bench --worker claude --repeats 1 \
  --task impl/p5/tasks/list_reverse_map_lengths.toml
impl/p5/scripts/cluster-down.sh
```

Each benchmark uses a fresh deployment and records 1, 2, 4 and 8 logical workers,
the physical concurrency cap, completion time, transfer and checking costs.
Command-worker replay is explicitly distinguished from actual coding-agent runs.
The recovery gate kills the controller during a partial task and removes the
desktop's state before resuming from the store.

A task uses `[task]`, `[controller]`, `[worker]`, and `[[targets]]` tables.
Each target has a unique `name`, a Lean type expression in `statement`, a relative
`file`, and a `deps` array of required target names. The task compiler freezes
the P1 type hash before dispatch. This version supports contracts expressed over
the pinned Lean base and one target declaration per publication; target types
depending on newly defined local types are rejected during contract compilation.
Use `worker.kind = "codex"` or `"claude"` for the built-in adapters, or `"command"`
with an argument array in `worker.command` for a configured CLI invocation.

Implementation evidence and limitations are recorded in
[docs/p5-log.md](../../docs/p5-log.md). Treat that log's measured results, rather
than the presence of a driver script, as the gate status.
