# Track B: transparent workspaces prototype (`remote%`, placement CRDT, git projection)

Date 2026-10-05. Design: [architecture.md § Transparent workspaces](architecture.md).
Code at the time: `impl/p1/Paralean/{Remote,Crdt,Workspace,Receipt,Validate}.lean`.
Scripts: `impl/p1/scripts/{run-transparent,remote-forgery,remote-cost}.sh`. Logs:
`impl/p1/results/{transparent.log,remote-forgery.log,remote-cost.tsv}`.

**Status (2026-10-06): superseded by P3 v1** ([p3-remote-log.md](p3-remote-log.md),
branch `p3-remote`). This document records the prototype as it was. P3 replaced every
shortcut listed below:

| Prototype | P3 v1 |
|---|---|
| theorems in working copies: statement only, receipt-backed placeholder axiom `<thm>._remote_proof` | the published proof is fetched from the store, decoded, and kernel-checked by `addDecl`; no placeholder exists, and a working copy's `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` |
| receipts: HMAC-SHA256 under a shared key over (package, declaration ID) | P3 control's receipts: Ed25519 by a trusted validator, bound to a signed job envelope (group, capsule, dependency closure, base, policy, checker); verified in Lean by `remote%` itself |
| store: a directory per copy, anti-entropy by copying files (`copy-pull`) | the P2 store (FoundationDB + Garage) through `plr`; publication is T1 and discovery is by certificates. Payloads are fetched on demand, metadata by anti-entropy |
| records `{pid, file, anchor, lamport, author}`; RGA with unknown anchors attached to the file start; no revisions or tombstones | §11.1 markers with `rootPath` and `lineageKeys`; revisions and author-signed tombstones; rendering reads only carried fields (Workspaces) |
| collisions: lowest (Lamport, author, package) wins; loser renamed `<name>_<author>_<lamport>` (not reserved) | lineage keys per name over live heads; losers get the reserved fresh name `x✝pl<8 hex>` (written `«…»`), which validators reject in declared names; the losing author gets a diagnostic and a rename of their drafts |
| `remote% "<package id>"` | `remote% "<group id>"` (and `remote_decl%` for commands without a value) |

The prototype scripts and the `copy-*` commands were removed. The measurements below are
the prototype's; P3's are in [p3-remote-log.md](p3-remote-log.md#measured-costs).

The P1 host process stands in for the fork. It injects `import Paralean.Remote` and runs
with `Elab.async` off. Everything else is the stock nightly.

## What was built

- **`remote%` elaborator** (`Paralean/Remote.lean`, a `module`, so `module` files such as
  Mathlib projections can import it). It handles two forms:
  `<published header> := remote% "<package id>"`, and the command `remote% "<package id>"`
  for groups without a single value (structures, mutual blocks, notation, attributes).
  Elaboration runs these steps:
  1. requires a validator receipt (HMAC over the exact package and declaration ID);
  2. requires the written header to be the published header byte for byte, with the
     published namespace as a prefix of the current one;
  3. loads the dependency closure from the store at the root scope, independent of
     imports. Each closure member is checked against its published content: theorems by
     statement hash with exact dependency pins, everything else by member encoding. A
     local declaration with the same name but different content is a version conflict;
  4. theorems: elaborates the published statement (attributes included). The proof is a
     receipt-backed placeholder (`<thm>._remote_proof`), **never fetched**. Defs,
     instances and structures re-elaborate their real capsule, because unfolding, `simp`
     and instance search need bodies.

  Capture treats a `remote%` command as a reference, not a new group. It indexes the
  loaded constants to their package IDs and allows only receipt-backed placeholder
  axioms. The validator and the exporter always use real proofs.
- **Placement CRDT** (`Paralean/Crdt.lean`). Publication records are
  `{pid, file, anchor, lamport, author}`; the anchor is the nearest published element
  above it in the author's copy. The set is grow-only and replicas merge by union. RGA
  linearization: siblings after one anchor are ordered by descending (Lamport, author).
- **Canonical rendering.** A projection is the sorted base imports plus one fixed-text
  block per element: the capsule scope wrapper around the `remote%` form, between
  `-- paralean:published <pid>` / `-- paralean:end` markers. It is a pure function of the
  record set and the stored capsules.
- **Working copies** (`Paralean/Workspace.lean`; `paralean copy-init|copy-publish|copy-sync|copy-pull|copy-hash`):
  - *publish* captures in remote mode, validates, adds records, and removes the published
    text from the drafts;
  - *sync* applies new records in (Lamport, author) order. Each record becomes one git
    commit authored by its publisher, containing only the projection. Then it rewrites
    the working file as projection plus this agent's drafts, re-attached after the
    element they followed;
  - *pull* is anti-entropy (store union), followed by sync.

## Results

**B→A→B with `remote%`** (`run-transparent.sh`, alice = A, bob = B, files
`A.lean`, `B.lean`):

1. bob publishes `Cross.helper_b`;
2. alice pulls and writes `Cross.helper` using it. Visibility comes from loading the
   published group by name; there is no import. She publishes;
3. bob pulls and writes `Cross.helper_c` using `helper`, plus an unfinished `sorry`
   draft. `helper_c` is published; the draft is rejected and stays private.

Every projection file in both copies elaborates standalone (no imports between `A.lean`
and `B.lean`, no module cycle). The only rejection is bob's own unfinished draft. Export
from alice's store: 3 modules (`B` → `A` → `B.Part2`), stock build OK, 3/3 groups
byte-identical.

**Projection identity.** After exchange, `A.lean` and `B.lean` have identical projection
hashes in both copies. Two concurrent publications at the start of `Shared.lean` (alice
and bob, both anchored at the file start) were exchanged in both orders (AB and BA, four
copies). All four copies have the same projection hash, `9185d0b8…`.

**Git projection** (bob's copy):

```
258fc8c bob:   paralean: bob publishes #[Cross.helper_c] in B.lean (…, t=3)
94f187a alice: paralean: alice publishes #[Cross.helper] in A.lean (…, t=2)
a5d948d bob:   paralean: bob publishes #[Cross.helper_b] in B.lean (…, t=1)
```

`git diff` in bob's copy shows only his unpublished draft (4 lines).

**Forged `remote%` uses** (`remote-forgery.sh`): the genuine use is accepted, and every
forgery is an error, not a `sorry`:

| Attempt | Result |
|---|---|
| unknown package ID | rejected: no published declaration |
| edited statement (`= n + 2`) with the real ID | rejected: header does not match |
| same statement under another name | rejected: header does not match |
| `remote%` inside a proof term | rejected: only allowed as an entire published value |
| receipt under the wrong validator key | rejected: receipt does not verify |
| receipt deleted | rejected: not published |
| a different local `helper_b`, then the remote `helper` | rejected: the published `helper_b` cannot be redefined |

## Measurements (`remote-cost.sh`; round-2 numbers at the end of this document)

Each corpus module's groups are published as one shared file. The all-`remote%`
projection is elaborated standalone by the host and compared with local capture of the
original file (same host) and with stock `lean` with `Elab.async=false`.

| module | groups | remote% (s) | local capture (s) | stock sync (s) | statement-only loads | full re-elaborations |
|---|---|---|---|---|---|---|
| M18 | 265 | 2.88 | 2.53 | 1.68 | 216 | 46 |
| M01 | 213 | 3.72 | 3.25 | 2.21 | 162 | 36 |
| M16 | 211 | 3.04 | 2.42 | 1.81 | 183 | 22 |
| M13 | 115 | 2.45 | 2.44 | 1.99 | 68 | 38 |
| M03 | 83 | 1.81 | 1.77 | 1.56 | 71 | 7 |
| M14 | 50 | 1.13 | 1.01 | 0.85 | 6 | 42 |
| M15 | 56 | 3.52 | 1.81 | 1.47 | 24 | 29 |
| **total** | **993** | **18.55** | **15.23** | **11.57** | **730** | **220** |

- **Proof bodies fetched in working copies: 0 of 730 theorem loads.** The elaborator
  has no code path that reads a stored object (`getObject` does not occur in
  `Remote.lean`). Bodies are fetched by the validator, which replays every published
  group, and by the exporter. The kernel never needed a theorem body in these files.
- **Re-elaboration cost** (from the elaborator's log): 730 statement-only theorem loads
  took 5.9 s (8.1 ms mean). 220 full re-elaborations of defs, instances and structures
  took 3.2 s (14.6 ms mean; the maximum is one M15 definition at 514 ms). Effect-only
  groups took 0.08 s.
- **`remote%` overhead vs local:** ×1.22 the host's local capture and ×1.60 stock
  synchronous `lean`, with 0 errors over 993 groups. Skipping proofs does **not** pay
  for itself on these files: Mathlib proofs here are cheap compared with statement
  elaboration plus per-element wrapper, receipt and closure checks. M15 is ×1.9,
  dominated by re-elaborating defs whose bodies are needed. Remaining overheads, all in
  the prototype rather than the design: one root-scope re-entry per element, a closure
  walk per element, and receipt JSON reads.

## Round 2: header meaning, visibility, namespaces, drafts, collisions

**The written header must mean the published declaration where it is written.** Byte
equality of the header text was not enough: the same text can be placed in another
namespace or read under different `open`s, notation or instances. `remote%` now also
checks:

- *name*: the declared name, resolved in the current scope (current namespace +
  `declId`, `_root_`, `private`), must be the Lean name of a member of the loaded
  published package;
- *meaning*: the written binders and type are elaborated **in the current scope** and
  closed over the binders and the section variables they use. The result must be
  definitionally equal (reducible transparency, fresh universe levels) to the loaded
  published statement. The published statement was itself checked against its
  published hash with exact dependency pins.

Two new forgery tests use byte-identical headers. Placing the header inside
`namespace Foo` fails ("the written declaration `Foo.Cross.helper` is not the published
declaration"). Reinterpreting `+` with a local instance fails ("the written statement
… does not elaborate here to the published statement"). The suite is now 10/10.

**Cross-file visibility through name resolution** (`Paralean/Visibility.lean`). The
text-scan prelude is gone. At host start-up every published public name, as rendered
after collision renaming, is registered through Lean's reserved-name mechanism:

- the predicate reports such names as reserved, only in working-copy environments and
  not while a package is being loaded;
- the action loads the package (receipt, closure and content checks) when ordinary
  name resolution reaches the name: terms, `rw`, `simp [...]`, `#check`, and so on.

Capture indexes constants loaded this way as dependencies of the command, never as its
members. Alice's `Cross.helper` now captures with one dependency (bob's `helper_b`),
found purely by name, with no import and no scan.

**Draft namespaces.** Sync tracks the scope stack the drafts open (`namespace`,
`section`, `end`, and `open`/`variable`/`universe`/`set_option`/`include`/`omit` inside
each frame). Every published element is surrounded by machine-generated
`-- paralean:auto-begin` … `-- paralean:auto-end` blocks that close those scopes before
the element and reopen them, with their scope commands, after it. The blocks are
dropped and recomputed on every sync. Elements are therefore always elaborated at the
root, and drafts may use `namespace` blocks freely. In `run-transparent2.sh` part A,
bob writes in `namespace Cross … end Cross` blocks with short names. His whole working
file, drafts included, elaborates standalone; the only rejection is his unfinished
`sorry` draft.

**Draft re-placement.** On publish, the drafts are re-split around the newly published
declarations. Text that followed a just-published declaration now follows its element:
bob's unfinished `wip`, written after `helper_c`, stays right after `helper_c`'s
element.

**Name collisions (rule 4).** For each public name published by more than one package
(unrelated, since revisions are not modelled), the lowest (Lamport time, author,
package) keeps the name. Every other package's declaration is renamed to
`<name>_<author>_<lamport>`; its auxiliaries follow by prefix. This is a prototype
spelling: it lies outside any reserved namespace, so a user could write the same name.
The v1 spelling of fresh names is tracked as OPEN-25 (reserved-name spelling) in
[p0-interfaces.md](p0-interfaces.md). Published uses of a
renamed package (groups depending on it) are rewritten in their rendered and loaded
text by identifier-token rewriting. Renames apply consistently in rendering,
`remote%` loading, the visibility index, capture and export. Identity is unaffected:
dependencies pin packages and encodings use package identities, so a wrong rewrite
fails the content check instead of passing silently.

In part B, alice and bob concurrently publish an unrelated `Shared.dup`, and bob also
publishes `Shared.use_dup`, which uses his. Exchanged in both orders, all four copies
render `Shared.lean` with the same hash. Alice keeps `Shared.dup` (Lamport tie, `alice`
< `bob`); bob's declaration becomes `Shared.dup_bob_1`. In bob's git history the rename
arrives as alice's commit (`-theorem Shared.dup : 2 + 2 = 4 …`, `+theorem Shared.dup_bob_1 …`).
Both copies elaborate the file standalone. A draft can use `Shared.dup_bob_1` and
`Shared.dup`. The export of the merged store builds and verifies 3/3, with
`Shared.use_dup := Shared.dup_bob_1`.

## Limitations found (remaining)

P3 status of each item: the last two (placeholder axioms, HMAC) are gone. The first
four still hold in P3 v1: visibility is still built at process start, but every working
copy step is a new process; renaming is still token-based; capsule elaboration still sees
root-scope local state (a forgery test now hits it, failing closed); scope tracking is
still line-based.

- **Visibility** is registered at host start-up from the store as it was then.
  Publications that arrive later in the same process are visible after the next process
  start; the fork would consult the live registry. A draft that declares a name that is
  already published, and so visible, gets Lean's "reserved name" error instead of a
  rename. That is deliberate at authoring time; rule 4 handles only *concurrent*
  collisions.
- **Rename rewriting is token-based**: it handles qualified and namespace-relative
  identifiers, but not generalized field notation (`x.dup`). A missed rewrite fails the
  content check and is never silently rebound. Target names (owner rule) and revisions
  are not modelled here.
- **Capsule elaboration inherits root-scope local state** of the working file: a
  `local instance` at the root also applies while a published capsule is being loaded.
  Content checks make this fail closed, but a legitimate load can be refused.
- **Scope tracking is line-based**: commands at column 0, with a known list of scope
  commands. Exotic scope manipulation (e.g. `open … in` blocks spanning elements)
  is not modelled.
- Placeholder axioms appear in a working copy's `#print axioms`. They are allowed only
  through the receipt index and are absent from validator and export closures.
- Receipts are an HMAC with a shared key, not signatures (P3).

## Round-2 measurements (with the header-meaning check and name-resolution visibility)

Same setup as above: 7 modules, 993 published groups, each module's projection
elaborated standalone.

| module | remote% (s) | local capture (s) | stock sync (s) | statement-only | full | errors |
|---|---|---|---|---|---|---|
| M18 | 12.37 | 2.66 | 1.68 | 216 | 46 | 0 |
| M01 | 8.46 | 3.44 | 2.21 | 79 | 119 | 0 |
| M16 | 7.30 | 2.46 | 1.81 | 180 | 25 | 0 |
| M13 | 4.73 | 2.50 | 1.99 | 13 | 93 | 0 |
| M03 | 2.06 | 1.84 | 1.56 | 71 | 7 | 0 |
| M14 | 1.70 | 1.01 | 0.85 | 6 | 42 | 0 |
| M15 | 3.69 | 2.03 | 1.47 | 24 | 29 | 0 |
| **total** | **40.31** | **15.94** | **11.57** | **589** | **361** | **0** |

0 errors over 993 groups and 0 proof objects read. The cost went up from ×1.22 to
**×2.5 local capture (×3.5 stock)**, for two reasons:

1. every written header is elaborated a second time in the pre-load environment and
   compared with the published statement;
2. theorems whose attributes generate further declarations from the proof
   (`@[to_additive]`, `@[to_dual]`, `@[simps]`) are now loaded in full, because those
   attributes translate the proof term. M01 moved from 162 statement-only loads to 79.

Fixes found while measuring, all failing closed before the fix:

- a placeholder proof abstracted every local, which made Lean include unused section
  variables in Prop-valued instances. It now abstracts only the variables the statement
  needs;
- the header check must apply Lean's variable rules: `include`d variables are part of a
  statement, and definitions include variables their body uses (handled by peeling the
  published binders);
- the header must be elaborated *before* the declaration itself is loaded, and with the
  visibility hook suspended. Otherwise its own name, or later published names, capture
  identifiers: `theorem swap … : SymmGen (swap r) a b` means `Function.swap`;
- proof-internal auxiliaries (`_simp_n`, `_proof_n`, a recursive theorem's `_f`) are not
  part of the content check when the proof is a placeholder.
