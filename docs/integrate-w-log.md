# Integration of W1, W3, W4 and W5

Branch `integrate-w`, started 2026-10-20 at `origin/main` `fee94d9`. The four
workstream branches were merged one at a time, in order, with `--no-ff`:

| Merge | Branch head | Merge commit |
|---|---|---|
| W1 Lean replay and identity | `w1-lean-bugs` `52b3667` | `79cbe84` |
| W3 store and registry features | `w3-store-features` `8a87270` | `84e677f` |
| W4 control-plane scale | `w4-scale` `02a74ba` | `8ff9cb9` |
| W5 LSP to controller wiring | `w5-lsp-wiring` `5f69145` | `64e5083` |

`w2-security` is not merged. Each branch's own log remains the record of its
work: [W1](w1-log.md), [W3](w3-log.md), [W4](w4-log.md), [W5](w5-log.md).

## Conflicts and their resolution

Only shared verification scripts and generated results conflicted textually.
The `impl/p1` (`Main.lean`, `Copy.lean`) and `impl/p4/lsp.py` files changed by
both W3 and W5 merged cleanly, as did `verification/veil/Paralean.lean`.

| File | Branches | Resolution |
|---|---|---|
| `scripts/tla-common.sh` | all four | Union of the positive scenario lists: W1 `ReplayIdentity`, `ExportLookup`, `ExportLookupResidual`; W3 `CatalogueExchange`, `CheckpointConflicts`, `AgentAuthority`, `StorePositions`; W4 `W4Scale`, `W4History`; W5 `EditorPublication`, `EditorRename`, `CapsuleReplay` (all on `EditorWiring`) |
| `scripts/check-tla-negative.sh` | W1, W3, W4 (W5 merged cleanly) | Union of every branch's witnesses and mutation cases; nothing was renamed or dropped |
| `scripts/check-veil.sh`, `scripts/archive-verification.sh`, `verification/veil/Audit.lean` | W1, W3, W4 | Union of module lists (`InitializerIdentity`, `CheckpointConflicts`). W4's standalone `ControllerGc` check (`scripts/check-w4-lean.sh`, called from `check-veil.sh`) is folded into the normal Veil module loop, `Paralean.lean` and the axiom audit, so it is archived and audited like every other module. `check-w4-lean.sh` remains for standalone use |
| `verification/TLA-GUARDS.md` | W1, W3 | Both new sections kept |
| `verification/results/**`, `source-sha256.txt` | all four | Not hand-merged. The pre-merge side was kept during each merge and everything was regenerated from the integrated sources at the end |

## Design interactions

### W4 garbage collection and W3 tombstones and moves

The rule is that nothing reachable from a live head, checkpoint or tombstone
lineage is ever collected.

- W4's two FoundationDB collectors cannot reach W3 state. Snapshot GC clears
  only `controller/shard/<n>/{chunk,retired,retained}` keys. History
  compaction only writes immutable replay rows and prunes the controller
  snapshot. W3's tombstones, position certificates, marker variants, controller
  deletion grants, agent-key grants and revocations all live under separate P2
  key heads. None of them sits in the controller snapshot.
- **Changed:** the S3 GC principal. In W4 it could delete any object key once
  enabled, including tombstones, markers and blobs that hold spilled FDB values.
  It now needs an explicit `--gc-delete-prefix BUCKET/KEYPREFIX` allowlist,
  which is required with `--gc-access-key`. Deletes must be path-style. No
  decoded key containing `obj/` is ever deletable, because every P2 content kind
  lives there.
  - Encoded, dot-segment, empty-segment and virtual-hosted forms fail closed.
  - Today no P2 bucket key is a legitimate GC target, since W4's GC is entirely
    in FDB. Retiring content would need a distributed retirement protocol.
  - Evidence: a new unit test and the mutation `mutate-no-gc-prefix-check`. The
    live gateway test now also shows protected kinds and unlisted prefixes being
    refused.
- **Changed:** `W4Scale.tla` adds tombstone lineage to the GC root set, with a
  `Tombstone` action. Its witness is `w4_tombstoned` and its mutation is
  `w4_no_tombstone_root` (which violates `RootsLive`). `ControllerGc.lean` now
  states the root inventory explicitly, tombstone lineage included, and proves
  that a collection preserves a tombstoned record and its anchors.
- Moves and their retries need no controller metadata. The move tombstone and
  marker are deterministic, and the pending arguments live in the working copy.
- The stale "no code clears a key" comment in `meta.rs` now names the
  anti-entropy work-queue clears and W4's controller-only clears.

### W4 shards and logical leases, W5 controller wiring, W3 controller deletion

- W5's P5 path never starts the P3 controller. It runs only
  `paralean-p3 validator` and checks P2 T4 target epochs, never a W4 term. So
  W4's startup refusal, the `--shard` flags and the new `--lease-ms` meaning do
  not affect it.
- **Changed (exclusive ownership):** the P5 bridge called P2 T4 directly. On a
  deployment that also runs W4 shards, a shard and a P5 task could silently take
  a target from each other.
  - Both now share W4's per-target claim key. P5 writes the claim
    `p5-task` before any T4 write, in `assign`, and inside the
    `fence-unfinished` transaction. It refuses a target that a shard has
    claimed, and a shard refuses a P5-claimed target.
  - Evidence: test `p5_claims` and the mutation `mutate-no-task-claim-check`.
- **Changed:** a superseded assignment no longer aborts the remaining handovers
  of a monitor tick. Before, a resumed intent could wedge every later handover.
- **Changed:** `Registered` now advertises one monitor interval instead of the
  whole lease. The old value was safe with one ticking replica per shard; with
  three or more, logical expiry outran worker heartbeats. Heartbeats now outpace
  expiry for up to 23 ticking replicas per shard.
- **Changed:** `plr` registers and heartbeats with every controller endpoint.
  With several fixed shards, a target owned by another shard would otherwise
  refuse an unregistered worker.
- **Unchanged by decision:** W3 controller deletion stays bound to the P2 T3
  fence and the controller key. It is not bound to a W4 shard term.
  - The T3 fence is global, ordered by the store and checked inside T8, and it
    is independent of topology and resharding.
  - Groups have no shard, and a W4 lease holder is an FDB string, not a
    credential, so binding to a term would add coupling without
    authentication.
  - If the P3 controller later issues deletions itself, the lease read should be
    added to T8 as an extra conflict read alongside the fence.

### W3 agent-key registry and W5 buffer publication

- Every W5 publication path authors as `AgentId(workspace)`. `plr keys-init`
  grants that ID, and every key-file copy is byte-for-byte, so no grant is lost.
- **Changed:** W5's policy feed could not see agent-key revocation. A revoked
  workspace stayed "current", spent validator work, and failed only inside T1.
  Now:
  - `MetaStore::agent_key_state` is a read-only mirror of T1's admission rule.
  - The bridge's `policy-state` reports each workspace's grant and revocation,
    so a revocation changes the policy identity and expires sessions and
    captures.
  - `validate-target` refuses before any validator work.
  - A new authority-only bridge command, `revoke-agent-key`, revokes a key.
  - The editor bridge refuses `paralean/publish`, and its pre-commit guard,
    while the workspace's agent key is revoked or unregistered. Read-only
    elaboration continues. T1 remains the authoritative check.
  - Evidence: a unit test, two editor-bridge mutants, and an
    `agent_key_revocation` check in the live LSP gate. That check shows that a
    worker key cannot revoke, that the authority's revocation reaches the editor
    through the feed, and that publication is refused.
- **Not changed (limit):** key rotation does not propagate to worker key files.
  W3 has no rotation command, and worker `keys.json` files are written once.
  Rotating a workspace key therefore also needs a re-split of the worker key
  files, which is a deployment step.

## What the merge broke

The merged tree built without changes:

- the Rust workspace, release and all test targets;
- the P5 store bridge;
- P1 on stock and on the fork;
- every Veil module.

With W1's lookup fix, the stock core export that W3 and W4 had recorded as
failing (F10/F13) now verifies 85/85. Problems found during verification:

1. **A latent W5 test-fixture bug.** W5's editor-bridge test opened a document
   without the `public_uri` that the router records on `didOpen`.
   `test_router_defers_worker_output_during_policy_probe` passed only when the
   temporary root failed to resolve to the workspace, so it depended on
   `TMPDIR`. Elsewhere it raised `KeyError`, including on W5's own tree. Fixed
   in the fixture.
2. **W4's GC and history mutation scripts selected W4's private `w4-scale`
   instance.** They did this through `w4-env.sh`. The first integration run
   therefore waited on that stopped cluster until it was stopped; no file of
   that instance changed. Both scripts now require the caller's isolated
   cluster, like `check-w4-mutations.sh`.
3. **An integration-only routing gap.** The new `revoke-agent-key` bridge
   command first lacked a route in the bridge's dispatch. The live gate's new
   check found this. It also showed that re-capturing an already published
   declaration is rejected, so the check uses a fresh draft.
4. **The fork moved, so the fork Mathlib closure had to be rebuilt.** W5's
   eighth fork patch changes the fork to `bd122768`, so W1's fork Mathlib
   closure (built by `99967f1`) was stale. A gate run then rebuilt modules with
   Paralean mode on and hit W1's documented `OrderDual`/`ExtraRecognizers`
   failure. The closure was rebuilt from a fresh copy with bd12276 and mode off,
   then the fork gate was rerun. This is an environment step for anyone moving
   to bd12276.
5. **A fresh-clone setup step was missing.** G4's reference fixture build
   (`corpus/fixtures`, normally made by `bootstrap.sh`) was missing on the first
   stock run, which made the core axiom dump fail. G4 was rerun after building
   it.

## Verification

All suites ran on the integrated tree, on private instances only. Logs are
under `results/iw/`, and the TLC and Veil archive is under
`verification/results/`.

| Suite | Result |
|---|---|
| Veil (`scripts/check-veil.sh`) | 32 modules, including `ControllerGc` and its tombstone-root lemma; axiom audit **7,359 declarations**, stock axioms only |
| TLA default / negative / wide / hardened | **33** positive scenarios; **179** negative and expected-outcome cases; **4** wide; **29** hardened (1,312 s) |
| `archive-verification.sh` and `--verify` | pass: 33 + 179 + 4 + 29 logs, `source-sha256.txt` regenerated |
| W4Scale with tombstone roots | 856,832 distinct states (W4 alone: 428,800); `w4_no_tombstone_root` and `w4_tombstoned` produce their counterexamples |
| P2 workspace tests (`iw-a`, peer `iw-b`) | **127 passed**, 0 failed |
| P2 anti-entropy network suite | **17/17** (within the workspace run) |
| P2 guard-removal mutations (`check-mutations.sh`) | **49/49 detected** |
| S3-guard unit tests / mutations / live gateway | 4 passed / **4/4 detected** / **10/10 checks**, including protected-kind and unlisted-prefix refusals |
| P3 tests (`impl/p3/scripts/test.sh`) | **70 passed**, 0 failed, 3 ignored benchmarks; includes the fork validator test and `p5_claims` |
| W4 controller / GC / history mutations | **10/10**, **6/6**, **15/15** detected |
| P3-remote gate (`remote-gate.py`) | **15/15 PASS** with the W4 controller (98.7 s) |
| P5 tests | **51 passed**, no skips |
| P5 editor-bridge mutants / revoke-guard mutant | **33/33** detected / killed |
| P4 rename unit / mutants / real-Lean | 25 passed / **18 killed** / **3 passed** |
| P5 integrated gate (Claude workers, SSH LSP worker) | **9/9 checks**: all 10 contracts, partial before loss, desktop removal, store discovery and recovery, dependency closure, stock export, `remote%` helpers, and the SSH LSP worker with every W5 check plus `agent_key_revocation` |
| P1 G1–G6, stock | 1225/1225 source, kernel and isolated replays; 22/22 export builds; G2 1122/1127, 78 canonical instances; G4 **1121/1142** exact identity, core 85/85, axioms 1445/1448 with 0 differing, mappings 5/5; G5 negative diagnostics identical to W1 (6/6 rejected). Every count matches W1 |
| P1 G1–G6, fork `bd122768` | 1225/1225 source, kernel and isolated replays; 22/22 export builds; G2 1122/1127, 90 canonical instances; G4 **1121/1142**, core 85/85, axioms 1445/1448 with 0 differing, mappings 5/5; G5 identical to W1. Every count matches W1's fork run on `99967f1`, after the Mathlib closure rebuild described above |

Two earlier P5 gate runs passed all 8 recovery checks. Their LSP worker
stopped at the new agent-key check, because of the routing gap and the
re-capture issue described above. The third run, against the final code, passed
all 9 checks.

## Environment

Private services only:

| Service | Instance / port | Notes |
|---|---|---|
| P2 instances | `iw-a` 26100 to 26150 and peer `iw-b` 26200 to 26250 | |
| P3 tests | `iw-a` | |
| P5 instance | `p5-iw` 26400 to 26450, validator 26491 | P5's `env.sh` accepts only instance names beginning with `p5-` |
| SSH daemon | 127.0.0.1:26555 | private keys and pinned host key |
| P3-remote gate | validator 26191, controller 26192 | |

Toolchains and dependencies:

- The fork is the bd12276 installation that W5 built, copied with reflinks.
- P1 was built from this tree twice: once on stock (`impl/p1/.lake`) and once on
  the fork (`.runs/iw/p1-fork`).
- Veil and TLA dependencies are copies of W3's. Stock Mathlib is a copy of W1's
  private stock build.
- No shared service, cache or other checkout was modified.
