# P3 transparent remote imports

`plr` (this crate) moves packages, receipts, publication records and tombstones between a
working copy's cache and the P2 store, and drives P3 control's validators. The Lean side
(`remote%`, the RGA, working copies) is in `impl/p1`. Log, gate results and costs:
[docs/p3-remote-log.md](../../docs/p3-remote-log.md).

```sh
(cd impl/p2 && cargo build --release -p paralean-remote -p paralean-control)   # plr, paralean-p3
PARALEAN_LEAN=fork impl/p1/scripts/bootstrap.sh                                # paralean on the fork
source impl/p3-remote/scripts/env.sh        # store instance, fork Lean, binaries
impl/p3-remote/scripts/gate.py RUNDIR       # the P3 gate scenario (RUNDIR/gate.json)
impl/p3-remote/scripts/gate-costs.py RUNDIR # per-step costs of a gate run
impl/p3-remote/scripts/corpus-cost.py RUNDIR [M14 …]   # Mathlib corpus costs
impl/p3-remote/scripts/ws.py init|publish|sync|delete|hash|check DIR …   # one working copy
```

| File | Role |
|---|---|
| `src/main.rs` | `plr` commands: `keys-init`, `stage`, `validate`, `publish`, `tombstone`, `pull`, `fetch-group`, `fetch-pkg`, `checkpoint`, `snapshot-get`, `check-receipt`, `forge` (tests) |
| `src/receipt.rs` | job envelopes signed by the copy's issuer key; calls to the validator service |
| `src/cache.rs` | the cache layout a working copy shares with `impl/p1` |
| `scripts/` | `env.sh`, `ws.py`, `gate.py`, `gate-costs.py`, `corpus-cost.py` |
| `results/` | the recorded gate run and costs |
