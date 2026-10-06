# P3 log: transparent remote imports (`remote%` v1)

Branch `p3-remote`. This replaces the shortcuts of the P1 prototype
([p1-transparent.md](p1-transparent.md)) with the v1 design of
[architecture.md § Transparent workspaces](architecture.md#transparent-workspaces) and
p0-interfaces §11:

- working copies fetch real proof terms and kernel-check them; no placeholder axiom exists;
- receipts are validator-signed (Ed25519), bound to a signed job envelope, and checked in
  the working copy itself;
- declarations travel through the P2 store (FoundationDB + Garage), never through files;
- each file is a declaration-level RGA with lineage naming and collision renames, as in
  `verification/tla/Workspace.tla` and `verification/veil/WORKSPACES.md`.

Receipts, job envelopes and validators are P3 control's (branch `p3-control`, merged at
`99987f8`; [p3-log.md](p3-log.md)). All results below come from this branch's own cluster
instance on aws-dev: FoundationDB 7.3.79 on port 4789, Garage 2.4.1 on 18539–18541 behind
`s3-guard` on 18533, data under `/data/home/kirancodes/paralean-p3-remote-cluster`.
Lean is the Paralean fork (`fork/`, `dfc13cc6`) throughout (`PARALEAN_LEAN=fork`).

## Components

| Where | What |
|---|---|
| `impl/p1/Paralean/Remote.lean` | `remote%` v1: fetch, receipt check, loading, content check, invalidation |
| `impl/p1/Paralean/P3.lean` | records in a copy's cache, receipt and job-envelope parsing, the staging rule checked in Lean |
| `impl/p1/Paralean/Ed25519.lean` | Ed25519 verification and SHA-512, pure Lean (checked against RFC 8032 §7.1 and 22 ed25519-dalek triples; 1.8 ms per verification) |
| `impl/p1/Paralean/Rga.lean` | per-file RGA, liveness, lineage naming, fresh names, canonical projection (§11.3) |
| `impl/p1/Paralean/Copy.lean` | working copies: capture, placement of new records, sync with git projection, drafts, renames, invalidation diagnostics, check, export |
| `impl/p1/Paralean/Visibility.lean`, `Crdt.lean` | name-resolution hook over the live view; working-file draft helpers |
| `impl/p1/Paralean/Forge.lean` | test only: a package whose proof is ill-typed |
| `impl/p3-remote` (`plr`) | the bridge to the store: stage, validate (job envelope + validator), publish (T1), tombstones, pull (anti-entropy), on-demand fetch, checkpoints and snapshot restore |
| `impl/p3-remote/scripts/ws.py` | one agent's working copy: `init`, `publish`, `sync`, `delete`, `hash`, `check` |
| `impl/p3-remote/scripts/gate.py` | the gate scenario |
| `impl/p3-remote/scripts/corpus-cost.py`, `gate-costs.py` | cost measurements |

Removed: the prototype's HMAC receipts (`Receipt.lean`), file-copy anti-entropy and the
`copy-*` commands (`Workspace.lean`), the placeholder axiom path, and the prototype scripts
`run-transparent{,2}.sh`, `remote-forgery.sh` and `remote-cost.sh`. Their logs stay in
`impl/p1/results/` as history.

## How it works

**A copy** is a directory: `work/` (a git repository with the agent's files), `cache/`
(its cache of the store, in P1's store layout plus `p3/`), `state.json` (agent, Lamport
clock, applied records, hidden elements, applied renames) and `keys.json`. The key file
holds only that agent's workspace seed and job-issuer seed; every other key is public.
Copies share nothing but the store and a validator service. Every step is a separate
process.

**Publishing** (`ws.py publish DIR FILE`):

1. Capture the working file in remote mode. `remote%` elements are references;
   teammates' declarations resolve by name through the visibility hook.
2. Per new group, in file order:
   - `plr stage`: put the payload and capsule in S3.
   - `plr validate`: issue a job envelope signed with the copy's job-issuer key (p3-control
     `99987f8`). It pins the group, its capsule, the capsules of its exact dependency
     closure, the base, policy v1 and the pinned checker. Store the envelope (`jobreq/`)
     and send it to the validator, which replays the closure and signs a receipt.
   - `paralean ws-plan`: compute the record's placement and revisions.
   - `plr publish`: T1 with the marker, the revisions, the receipt and the envelope.
   - `plr pull --only` the new record.

   Groups are published one at a time because a validator only accepts dependencies that
   are already published.
3. `ws-sync` rewrites the working file: the published text becomes elements, and the
   drafts that followed it follow its element.

**Placement** (`Copy.plan`):

- Lamport time: `max(own clock, every known record) + 1`. It is persisted before the plan
  is written.
- Anchor: the lineage root of the nearest element or earlier record of the batch above
  the group.
- `rootPath`: the anchor's carried path plus the new key. `lineageKeys`: the own key for
  each name.
- Revisions: a new group that declares a name rendered in this file revises that name's
  live head. It carries that head's root path and lineage key, and the anchor is the file
  start. An author edits a declaration by replacing its element block with new text. The
  element stays hidden in that copy until the revision publishes.
- A group without public names gets one revision for its anchor name
  `Paralean.anchor.g<32 hex>` (§3.5).

**Anti-entropy** (`plr pull`):

- Discovery reads certificates (P2 `discover`) and scans tombstones, which are
  writer-signed and author-checked.
- Each newly delivered record brings its revisions with their ancestry, the receipt, the
  job envelope and the capsules of the closure the envelope pins. All of this is metadata.
- Payloads (proof terms) are fetched only on demand, by `remote%`.
- `--seed/--max` deliver a random subset in random order (tests). `--save/--replay` serve
  an earlier response, as a lagging replica would.
- A response that lacks a record the copy already knows is rejected as stale.

**Rendering** (`Rga.View`) reads only fields the records carry:

- *Live*: known, not tombstoned by its author, and not revised by any known group (for
  any name, transitively).
- *Order*: by the lineage root's carried path. A proper prefix comes first; otherwise the
  newer key at the first difference comes first. Then by own key, oldest first.
- *Names*: candidates for a name are the live groups declaring it. The least
  (lineage key, own key) keeps it; every other candidate gets the fresh name. Renaming is
  hierarchical.
- The published projection is §11.3's canonical text: imports, scope runs, and
  `<header> :=\n  remote% "<group>"` or `remote_decl% "<group>"`.
- The working file is the same elements, each wrapped in its own scope between marker
  comments, with the drafts between them.
- One git commit per record, in (Lamport, author) order, authored by the record's author.
  The commit holds the projection, so `git diff` shows only the agent's drafts.

**`remote% "<group>"`** (`Remote.lean`), in order:

1. *Publication record*: from the cache, else `plr fetch-pkg`, which requires a
   certificate.
2. *Capsule*: re-hashed, and its package ID recomputed from its contents.
3. *Receipt*, checked in Lean with P3 control's staging rule:
   - the validator key is trusted and the signature verifies;
   - the verdict is accepted;
   - the receipt answers a job envelope signed by the controller or a listed job issuer;
   - that envelope is for exactly this group and capsule;
   - base, policy and checker repeat the envelope's and are pinned;
   - the axioms are within the policy.
4. *Invalidation*: a group this copy knows to be superseded is never loaded.
5. *Closure*: loaded first, by group ID, independent of imports.
6. *The group itself*:
   - **Theorems** are elaborated from the capsule's statement with the body
     `remote_value% "<package>"`. That elaborator decodes the fetched payload, adds the
     auxiliaries the proof uses through `addDecl` (kernel-checked), and returns the
     published proof. `addDecl` then kernel-checks the theorem with that proof.
     Attributes run as written, so `@[simp]` and `@[to_additive]` act on the fetched proof.
   - **Definitions, instances, structures and inductives** are elaborated from the capsule,
     since compilation, equation lemmas, structure info and instance search need the
     elaborator.
   - Every member is then compared with the decoded payload:
     - statements always;
     - bodies of non-Prop definitions always;
     - theorem proofs when they were fetched (they are equal by construction).
7. *Header*: the written header must mean the published statement where it is written.
8. *Failure*: a failed load restores the environment. Otherwise Lean's error recovery
   would leave the declaration behind, proved by `sorryAx`.
9. *Bypass options*: a capsule that sets `debug.skipKernelTC` or another bypass option is
   never elaborated.

## Gate results

`impl/p3-remote/scripts/gate.py RUNDIR` ran on 2026-10-06. All checks passed in 112.5 s on
deployment `p3gate1791330190`. Results are in `impl/p3-remote/results/gate.json` and
`gate.log`.

There are nine working copies in separate directories, each driven by separate processes:

- the agents alice, bob and carol;
- observers o1, o2 and o3;
- a snapshot restore;
- eve, a malicious replica;
- mallory, a compromised publisher.

There is one validator service (`paralean-p3 validator`, fork mode).

| # | Gate item | Result | Evidence |
|---|---|---|---|
| 1 | B uses A's completed helper while A keeps editing | PASS | bob publishes `Cross.helper_c`, which uses alice's `Cross.helper`. At that moment alice's `Cross.wip := sorry` is still a draft: capture rejected it, it is absent from bob's copy, and `git diff` in alice's copy shows only her draft. Alice finishes and publishes it later |
| 7 | B→A→B through `remote%` without module cycles | PASS | `B.helper_c → A.helper → B.helper_b`. No file imports another. `A.lean` and `B.lean` elaborate with no errors in alice's, bob's and carol's copies. The export lays the chain out as `B`, `A`, `B.Part1` |
| 2 | Invalidation reaches B; B rejects stale responses; old snapshots stay retrievable | PASS | See below |
| 3 | Rendered projections hash-identical after exchange in any order | PASS | Observers o1–o3 received the 15 records one at a time in three different random orders. Anchors and ancestors often arrived after their dependents. All six copies (alice, bob, carol, o1–o3) end with identical `A.lean`, `B.lean` and `Shared.lean` projection hashes |
| 4 | Superseded and tombstoned declarations leave the file | PASS | After alice revises `Cross.size` and tombstones `Cross.tmp`, no copy's projection contains the old `Cross.size` group or `Cross.tmp` |
| 5 | Revising a collision winner keeps its name | PASS | bob's `Shared.dup` (key 13) won against alice's (key 13, author tie-break). bob revised it, and the revision's own key is 14. The revision keeps `Shared.dup` in every copy through its lineage key (13). An own-key rule would have handed the name to alice's group |
| 8 | A losing author receives a diagnostic and a Lean rename | PASS | The loser's sync prints `rename: your declaration Shared.dup (…) lost the name to bob's (…, older lineage); it is now Shared.«dup✝pl8feff7bc» …`. The loser's own drafts are rewritten to the fresh name, and the loser's file elaborates |
| 6 | A forged `remote%` is rejected | PASS | 10 forgeries rejected, the genuine use accepted (table below) |
| — | No placeholder axiom in any working copy's `#print axioms` | PASS | Over 21 files in 7 copies, 93 constants were loaded by `remote%`, and Lean's `collectAxioms` on them gives only `propext`. No file declares an axiom. 142 theorem loads used fetched proofs |
| — | Clean export (plan's P3 gate) | PASS | Alice's copy exports 6 modules (`B`, `A`, `B.Part1`, `Shared`, `A.Part1`, `B.Part2`). It builds with the pinned Lean in 3.2 s, and 11/11 groups re-encode identically from the built modules |

**Item 2 in detail.**

- *Stale validator response.* bob validates `Cross.size_le` against `Cross.size := 3`. The
  run pauses after the validator answers, and alice publishes the revision
  `Cross.size := 5`. When bob resumes, his plan rejects the response: `stale response:
  validated against #[Cross.size] (390999a6d17a), which is no longer a live head here`.
  Nothing is published.
- *Invalidation reaches B.*
  - bob's next sync reports `invalidated: #[Cross.size_pos] in B.lean (6c3b6064e579)
    depends on #[Cross.size] (390999a6d17a), superseded by b5066ebcf873 (alice)`.
  - In bob's copy the `size_pos` element now fails with `remote%: invalidated: …`, so no
    name in that file can bind to the superseded version.
  - bob repairs it by revising `size_pos`, after which `size_le` publishes.
- *Stale replica.* A pull served from a response saved before the revision is rejected:
  `response lacks 1 record(s) this copy already knows`.
- *Old snapshot.* bob committed a checkpoint (P2 T3/T5: snapshot, manifests, fenced
  catalogue record and certificates) before the revision. Afterwards a fresh copy recovers
  that catalogue record with `plr snapshot-get` (P2 `recover_catalog`). It fetches the
  6 groups (21 KB in 89 ms), renders the old `A.lean`/`B.lean` (with `Cross.size := 3`)
  and elaborates both with no errors.

**Item 6 in detail** (`gate.json` → `6`):

| Forgery | Rejected by |
|---|---|
| unknown group ID | `plr fetch-pkg`: not published |
| real ID, edited statement | the written statement is not the published one |
| real ID, same statement under another name | the written declaration is not a member of the group |
| real ID, header inside `namespace Foo` | name check (`Foo.Cross.helper_b`) |
| real ID, `+` reinterpreted by a local instance | statement check (the published statement does not elaborate to itself in that scope) |
| `remote%` inside a proof | only allowed as an entire published value |
| payload bytes corrupted in the cache (malicious replica) | re-hash: `object … fails hash verification` |
| receipt and envelope signed by an untrusted validator and controller | `the receipt is signed by an untrusted key` |
| another group's genuine receipt substituted | `the receipt names another group` |
| **ill-typed proof under a valid receipt.** `Cross.bad : 1 = 2`, proof `Eq.refl 1`. The trusted validator and controller keys signed it (a compromised validator), and T1 published it | type check of the fetched proof: `Type mismatch Eq.refl 1 … expected 1 = 2`. Nothing remains in the environment |

The last row is what v1 adds. The prototype elaborated only the statement and added a
placeholder axiom, so it would have accepted `Cross.bad` and every theorem built on it.
The clean export rejects it as well (its capsule rebuilds to another group). The P1
validator rejects its source replay.

## Measured costs

### Gate run (fixture-sized declarations)

Medians over all processes of the run (`impl/p3-remote/results/gate-costs.json`). Each step
is a whole process, including Lean or Rust start-up and the FDB/S3 client set-up; the box
was shared with other agents' runs.

| Step | n | median | p95 |
|---|---|---|---|
| `plr validate` (envelope, validator replay of the closure, receipt) | 17 | 434 ms | 499 ms |
| `plr publish` (T1) | 15 | 85 ms | 116 ms |
| `plr stage` (payload + capsule to S3) | 17 | 65 ms | 125 ms |
| `plr pull` | 109 | 73 ms | 131 ms |
| `paralean ws-capture` | 13 | 1.10 s | 1.30 s |
| `paralean ws-plan` | 17 | 102 ms | 182 ms |
| `paralean ws-sync` | 83 | 114 ms | 193 ms |
| `paralean ws-check` (elaborate a working file, `collectAxioms` of every constant) | 42 | 1.12 s | 1.41 s |
| `remote%` load, theorem with fetched proof | 146 | 4 ms | 95 ms |
| `remote%` load, elaborated group | 24 | 2 ms | 3 ms |
| content check against the payload | 170 | 0 ms | 1 ms |

| Transfer | n | total | median per transfer |
|---|---|---|---|
| metadata per pull (markers, revisions, receipts, envelopes, capsules) | 82 pulls | 299 KB | 2.9 KB in 17.6 ms |
| payload fetched by `remote%` | 62 | 22 KB | 360 B in 4.1 ms |
| staged payloads / capsules | 18 / 18 | 6.0 KB / 21.9 KB | 352 B / 1.2 KB |

Per published group, the metadata a reader pulls (about 3 KB, mostly the capsule) is
several times the payload (about 0.4 KB). Payloads move only when a copy elaborates the
element.

### Mathlib corpus

CORPUS_RESULTS

## Deviations

1. **Capsule format.** A capsule object is the package's P1 metadata JSON (`GroupRec`),
   as P3 control publishes P1 groups, not §5's PCE capsule. Its ID is the S3 ID of those
   bytes. The receipt pins it through the job envelope, and readers recompute the package
   ID from it.
2. **`remote%` spelling.** `remote% "<64 hex group ID>"` and `remote_decl% "<64 hex>"` are
   written as string literals. §11.2's bare `hex64` is not a single Lean token.
3. **Theorems are fetched; other groups are re-elaborated.**
   - Only theorems (including Mathlib `lemma`) take their proof from the payload.
   - Definitions, instances, structures, inductives and effect-only commands are
     elaborated from their capsule, then compared with the fetched payload: statements
     always, bodies of non-Prop definitions always. Bodies of Prop-typed auxiliaries of a
     re-elaborated group (a recursive theorem's `_f`) may differ, which matches §5's
     interface equality. The case occurs because P1 still lets a group reuse another
     group's matcher (the "disable matcher reuse" obligation is not implemented).
   - Payloads are never materialized directly, because compilation, equation lemmas,
     structure info and instance search need the elaborator.
4. **Effect-only group IDs** (P1 encoding change).
   - Problem: a command without kernel members (attribute or notation only) used to
     encode to the same group ID as every other such command. §4 includes `effects` in
     the group ID; P1 encodes none. P2 keys markers by group ID, so the second such
     command could not be published.
   - Change: their base string now carries `;effects=H("v0/effects", command text,
     namespace, opens)`. Groups with members are unchanged; P2's golden vector and the
     P1 core and negative runs are unchanged except for those IDs.
   - The digest stands in for §4's `FrontendEffects` and is not that field.
5. **Fresh-name spelling** (OPEN-25, chosen here).
   - The losing group's last component gets the suffix `✝pl<first 8 hex of the group
     ID>`. In source it is written `«…»`, because Lean prints `✝` unescaped.
   - A reserved name is any name with a `✝` in a component. P3 control's `checkGroup`
     now rejects any group with such a public name.
   - Renames are applied to the declared name and, by token rewriting, to dependents'
     capsule text (OPEN-17, as in the prototype), not only to the declared name as §11.3
     item 5 says.
6. **Working file vs projection.**
   - The canonical projection (§11.3, what is hashed) has no comments. The working file
     wraps each element in its own scope between `-- paralean:published <group>` and
     `-- paralean:end` lines, so the author's drafts can sit between elements.
   - The projection omits `import Init` in non-module files and puts `open` lines before
     `namespace` (P1's capsule order).
7. **Git projection.**
   - Commits hold the working-form projection, not §11.6's source rendering. Authors and
     dates follow §11.6.
   - Commits are made in (Lamport, author) order per sync. A record that arrives later
     with a lower key is committed after newer ones, so commit histories can differ
     between copies while the trees agree. There are no `paralean/snapshot/*` tags.
8. **Job envelopes.** Working copies sign the envelopes of target-free groups with their
   own job-issuer key (P3 control `99987f8`; issuer-signed envelopes may name no target).
   A copy's key file holds only its own workspace and issuer seeds. The gate's
   checkpoint step uses the full key file, acting as controller (T3) and bob (T5).
9. **Tombstones.**
   - Stored at FDB key `tombstone/<id>` as a `Signed<Tombstone>` by the author's
     workspace key, written once the target is published, certified, and by the same
     author (OPEN-19 default).
   - Readers verify the signature and the author.
   - They are not acknowledged with per-replica certificates as §11.4 asks; P2 has no
     tombstone transaction yet.
10. **Revocations are not consulted by working copies.** `remote%` verifies receipts and
    envelopes in Lean but does not read `vrevoke/`; T1 does. `plr check-receipt` runs P3
    control's full consumer check (`published_receipt`, including revocation).
11. **Invalidation is stricter than "dependents keep the exact old ID".**
    - A copy refuses to load a group it knows to be superseded. A live element whose
      closure holds a superseded group therefore fails in that copy, with a diagnostic,
      until it is revised. Otherwise a later name-based reference in the same file could
      bind to the stale version.
    - Dependents of a tombstoned group still load it.
    - A snapshot restore knows only the snapshot's records, so old versions load there.
12. **Stale responses**, as defined here (the spec names the requirement only):
    - a validator response is stale when a remote dependency it was checked against is no
      longer a live head when the response is used;
    - a pull response is stale when it lacks a record the copy already knows.
13. **Checkpoint.** The gate's snapshot is every revision bob knew. Its build receipt is
    synthetic (`--build-ok`), not a real export build; P2 does not check closure or
    buildability at commit.
14. **Machines are simulated** by separate directories and processes on one host,
    sharing one store instance and one validator. Only the fork was run, not stock Lean.
15. **`remote%` in the host.** As in P1, `remote%` runs in the host process
    (`paralean ws-check`, capture) that injects `Paralean.Remote`. The fork has no native
    `remote%` and the interactive server is not involved (P4).

## Not done

- Target names in working copies (owner rule, epochs, controller-issued target jobs). The
  gate publishes no targets; P3 control covers targets in its own tests.
- OPEN-26: rendered collision renames are not committable. The registry conflict stays
  until a revision or tombstone resolves it; there is no tooling for that beyond the
  diagnostic.
- Per-replica certificates for tombstones; moves (OPEN-20); deletion by the controller
  (OPEN-19).
- Revocation checks in `remote%` (Lean); lazy loading below group granularity (payloads
  are fetched per group, unchunked).
- §11.6 in full: history-preserving or rewritten projection branches and snapshot tags.
- Capsule rewriting for renamed dependencies beyond identifier tokens (OPEN-17;
  generalized field notation is not handled).
- A stock-Lean run of the gate and the corpus measurement (fork only). The P1 core and
  negative runs were repeated on the fork as a regression check, with unchanged results.
- `remote%` inside `lean --server` (P4). Root-scope local state (`local instance`) still
  leaks into capsule elaboration. This fails closed (forgery table) but can refuse a
  legitimate load.
- The interactive cost of capture: every working-copy step is a fresh process that
  re-imports the base (Init: about 1 s per `ws-capture`/`ws-check`; Mathlib: more).

## Reproduce

```sh
impl/p2/scripts/bootstrap.sh && impl/p2/scripts/up.sh   # with this branch's prefix and ports, see below
PARALEAN_LEAN=fork impl/p1/scripts/bootstrap.sh --mathlib
(cd impl/p2 && cargo build --release -p paralean-remote -p paralean-control)
source impl/p3-remote/scripts/env.sh
impl/p3-remote/scripts/gate.py .runs/p3-remote/gate            # gate, about 2 min
impl/p3-remote/scripts/gate-costs.py .runs/p3-remote/gate
impl/p3-remote/scripts/corpus-cost.py .runs/p3-remote/cost M14 M03 M15 M13 M16 M01 M18
```

`impl/p3-remote/scripts/env.sh` defaults to this branch's cluster instance
(`PARALEAN_P2_PREFIX=/data/home/kirancodes/paralean-p3-remote-cluster`, FDB 4789, Garage
18539–18541, S3 18533). Override them to use another instance. Each gate run uses a fresh
`PARALEAN_DEPLOYMENT` (an FDB key prefix and an S3 prefix) and its own keys.
