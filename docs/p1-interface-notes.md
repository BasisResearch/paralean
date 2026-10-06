# P1 notes for the interface freeze

Findings from the P1 implementation (`impl/p1/`) that the frozen formats in
[p0-interfaces.md](p0-interfaces.md) must account for. P1 does not edit P0's file.
Each item gives the evidence and the choice P1 made.

## 1. Auxiliary names depend on `Elab.async`

- Evidence: synchronous elaboration (`Elab.async := false`) names a proof auxiliary
  `Probe.aux_pos._proof_1`. Stock `lake build` elaborates asynchronously by default and
  names the same auxiliary `Probe.aux_pos._proof_1_1`. The kernel terms, and therefore
  the declaration IDs, differ.
- P1 choice: capture runs synchronously, and every exported module pins
  `set_option Elab.async false`. With that pin, 14/14 probe groups and 3/3 B→A→B groups
  re-encode identically from the stock-built `.olean`s.
- **Decided:** this is the v1 position in p0-interfaces.md §4.3, architecture.md and
  lean-integration.md: `Elab.async` is off everywhere, including the interactive
  server, and is not overridable. Restoring asynchronous interactive elaboration is a
  fork target tracked as OPEN-14, conditional on async and sync captures of the corpus
  giving equal group IDs under canonical numbering (OPEN-22). P1 implements this for
  capture (`reject:async-override`) and pins it in replay and export. Fork locations:
  [p1-fork-hooks.md](p1-fork-hooks.md) item 1.
- Measured cost (stock `lean`, best of 3, `impl/p1/results/async-cost.tsv`): Mathlib
  M01–M18 wall 11.7 s → 16.3 s (×1.39); worst file M18 ×2.2; fixtures 5.5 s → 5.9 s.
  Total CPU time goes down (24.6 s → 22.4 s): the cost is lost within-file
  parallelism, not extra work.
- The stock elaborator publishes a theorem's signature before its kernel check
  finishes (async), and it re-adds kernel-rejected theorems as axioms in both modes.
  Publication must therefore never follow from "the command returned"; see the
  F-async results in [p1-gate.md](p1-gate.md).

## 2. Identity normalization

A declaration ID must not depend on the module a group was elaborated in. P1 encodes
identity after these normalizations; all were needed to make replay reproduce IDs:

| Module-dependent spelling | Example | Normalization |
|---|---|---|
| private prefix | `_private.M.0.P.aux` | strip prefix (scoped, group-keyed) |
| relocation namespace | `P._pl_61d5bb79.aux` | strip `_pl_*` component |
| `_aux` macro names | `_aux_Fix_Probe2___macroRules_…` | replace module with `$M` |
| hygienic decl names | `initFn._@.M.<hash>._hygCtx._hyg.2` | `initFn._hyg.<k>`, k = per-group creation order |
| hygienic binder names | `x._@.M.<hash>._hygCtx._hyg.5` | macro scopes erased (kernel ignores binder names) |
| hygienic universe params | `v._@.M….` in `noConfusionType` | renamed injectively by position, `v._hyg_<i>` |
| auto-named instance | stock `instInhabitedProdNat_fix`, `instFoo_1` | none needed: an anonymous `instance` gets the canonical name `instInhabitedProdNat_<8 hex>` at capture (§6), which the capsule writes explicitly; derived instances keep the deriving handler's spelling, and export keeps module roots so Lean regenerates it |

Hygienic *name literals inside terms* (e.g. `register_simp_attr`'s `initFn` bodies)
cannot be normalized; such groups are module-dependent and reported.

## 3. Constant references

The P1 encoding uses four reference forms: `base n` (pinned toolchain/library),
`self l`, `dep <package-id> l` (exact pin), and `res <ref> <suffix>` (a reserved name,
never transported). Dependencies pin **package** IDs (declaration content + capsule +
frontend dependencies), not bare declaration IDs, so two byte-identical declarations
with different capsules remain distinct packages.

## 4. Reserved names

"Reserved" is decided with Lean's own `isReservedName` in the producing environment. This
covers private-spelled match equations and splitters. Kernel replay re-realizes them via
`executeReservedNameAction` in the reconstructed frontend environment. It then adds them
with the stock kernel, interleaved with the consumer's own declarations in one
topological order: a WF equation such as `ack.eq_1` needs `ack.match_1` from the same
group.

## 5. Frontend dependencies

Kernel dependencies are not enough for capsules:

- Constants named in source but absent from the term (`simp [lemma]` with a
  definitional lemma) must be in scope. P1 adds every constant referenced by a
  `TermInfo` to the frontend dependencies.
- Syntax kinds and elaborators used by the command are resolved through the macro and
  elaborator attribute tables.
- `attribute [...] c` commands become effect groups that consumers of `c` depend on.
- Section-local effects (`local notation`, `attribute [local …]`, `open scoped`) are not
  published. Their text travels in the capsule of every later command in the section.

## 6. Canonical instance names (OPEN-24, implemented)

P1 follows the decided scheme of p0-interfaces.md §3.2. An anonymous `instance` written in
source is named

    <ns>.<stock base name, no `_n`, no project suffix>_<first 8 hex of H("v0/insttype", τ)>

where `τ` is the elaborated instance type (all binders, including section variables,
auto-bound implicits and instance arguments) and `H` is the §1.2 hash (SHA-256 over
`"paralean" NUL "v0/insttype" NUL` and the PCE string of an injective text of `τ`): every `Expr` constructor has its own tag, binder names
and `mdata` are erased, binder kinds are kept, universe parameters are numbered by first
occurrence, and constants are spelled by their module-independent identity (`normName`).
Example: `instance : Foo Nat` in `F08` is `F08.instFooNat_3b90afc0`. The two instances
`Inhabited (ULift.{1} Nat)` and `Inhabited (ULift.{2} Nat)`, which stock Lean names
`instInhabitedULiftNat` and `instInhabitedULiftNat_1` depending on order, get
`…_92742698` and `…_06ff4481`. (Hashes since the §1.2 domain prefix, §7. Before it the
examples were `F08.instFooNat_7d9f17e6`, and `…_2672ce46`/`…_ad3bb490` for the pair.)

Implementation: `Paralean/InstName.lean` (fork-hooks item 14). Capture records the stock
spelling as metadata (`MemberRec.stock`) for the G2 oracle comparison only.

**Injectivity.** Within one namespace, the name is a function of `τ`, so equal types give
equal names (the duplicate-instance collision LEAN-NAMES.md's `instance_collision`
requires). The text of `τ` is injective on types modulo alpha-renaming, binder names,
`mdata` and level-parameter renaming, none of which changes which instance it is.
Different types therefore get different names unless the 32-bit truncations collide.
A collision needs the same namespace, the same stock base name *and* the same 8 hex
digits: for n instances sharing a base name, the chance of any clash is about
n² / 2³³ (n = 100: about 1 in 860,000). A clash is never resolved by renaming. Within one
environment the hook reports `instance name collision: … is already declared`; across
workspaces the two groups publish the same public name, and the registry's ordinary
collision check reports it (`version-conflict`, `run-negative.sh`, fixture
`impl/p1/fixtures/instdup`). Either way the cost of a hash clash is a spurious,
diagnosed collision, never an unsound merge, and the user resolves it by naming one
instance explicitly.

**Where it does not apply (P1).**

- Instances that a deriving handler synthesizes (`deriving Repr`, `deriving instance`) keep
  the handler's spelling (`instReprShape`). A stock export re-runs the handler and cannot
  be told a name, so the prototype cannot rename them without a fork; the fork changes
  `mkInstName` (Deriving/Util.lean:95) to the same scheme. P1 still never accepts a `_n`
  deduplicated derived name: capture rejects it as `instance-name-clash`. These names are
  public and collide by spelling, which is environment-independent once `_n` is excluded,
  but not injective (two derived instances whose types share head symbols share a name).
- Anonymous instances inside `mutual` blocks bypass the `declaration` elaborator; capture
  reports `unsupported:noncanonical-instance` (none in the corpus).
- The stock name for an instance whose type mentions macro-scoped constants is fresh
  (hygienic); the hook leaves those to the stock elaborator.
- The hook elaborates such a command twice (once to read the type). The fork computes the
  name from the elaborated header directly.
- Source that refers to an anonymous instance by its stock name (`@instFooNat`) must use
  the canonical name instead. No corpus file does: all 18 Mathlib modules and the fixtures
  capture with 0 rejections under the canonical scheme.
- Attributes that derive names from an instance's name (`@[to_dual]`) derive them from the
  canonical name (`Pi.instMinForall_9122ed72` from `Pi.instMaxForall_9122ed72`). Such a
  derived name is a function of the base name, so it collides exactly when the base does.

## 7. Group identity: canonical numbering and group-ID pins (OPEN-22, OPEN-23, implemented)

The group encoding is now `paralean-group-v3` (v2 plus the §1.1/§1.2 changes at the end of
this section):

- `self` references carry the member's canonical index, not its spelling. Members are
  numbered as p0-interfaces.md §3.4 says: public members by name; then scoped members in
  order of first reference from the public members' types and values (depth-first,
  left to right); then unreferenced scoped members sorted by their encoding with
  self-references written `self(⊥)`.
- Public members carry their name in the bytes. Scoped members carry none; their spelling
  is metadata (`MemberRec.local_`). Two groups that differ only in the spelling of a
  `_proof_n`, `match_n` or private auxiliary therefore have the same group ID.
- `dep` references pin the dependency's **group ID** (its declaration ID) and member index
  (OPEN-23 option (a)). The package ID still pins the capsule through the group's `deps`
  and `feDeps` metadata, which decoding uses to map a group ID back to a package. The
  package ID hashes the group ID, the capsule and the frontend dependencies, as before.
- Eager auxiliaries of a public base (`casesOn`, `injEq`, `ctorIdx`, …) are `pubAux`;
  internal auxiliaries under a public root (`_proof_n`, `match_n`, `_sizeOf_n`, …) are now
  scoped, so they are numbered rather than named.

Effect on G4: the export is verified against the stored group ID by matching scoped
members to constants by spelling; identities are unchanged by relocation as before.

**§1.1/§1.2 conformance (OPEN-1/OPEN-2, p2-log.md deviation 10, fixed 2026-10-06).** Every ID
P1 computes is `H(domain, x) = SHA-256("paralean" NUL domain NUL ‖ PCE(x))`
(`Encode.domainHash`):

| ID | domain | preimage `x` |
|---|---|---|
| group (`declId`) | `v0/group` | the group bytes |
| capsule | `v0/capsule` | record: `format` 0, the capsule (P1's JSON rendering, a `string`), frontend dependencies as a `set` of package IDs |
| package | `v0/package` | record: group ID, capsule ID (§4.1) |
| publication record | `v0/marker` | record: package ID, file, anchor (option of a package ID), Lamport time (`uvarint`), author |
| instance type digest | `v0/insttype` | the type text as a PCE `string` (`uvarint` length, UTF-8); the fork computes the same bytes |

IDs inside PCE are `bytes` of the 32-byte digest. In the group bytes, the encoding starts
with `format : uvarint = 0` (§1.4). Lean `Nat` values use §1.1 `nat` (minimal big-endian
magnitude as `bytes`): name `num` components, `bvar` indices, nat literals (previously decimal
strings), `DataValue.ofNat`, `proj` indices and the `Nat` fields of inductive, constructor and
recursor infos (`numParams`, `numIndices`, `numNested`, `cidx`, `numFields`, `numMotives`,
`numMinors`, `nfields`). Counts, lengths, table indices, tags and bounded machine integers
(`ReducibilityHints.regular` height, a `UInt32`) stay `uvarint`. Dependency group IDs are 32
raw bytes instead of a hex string. The decoder rejects non-minimal `uvarint`s and `nat`s, IDs
that are not 32 bytes, unknown formats and trailing bytes. P2's `check-p1`/`import-p1`
recompute `H("v0/group", bytes)` for every group and require it to equal P1's `declId`.

Still not the §4/§5 schemas: the group's field layout is P1's term table, not the
`GroupManifest` record list (effects are metadata, not bytes); `baseID` is the string
`lean:<commit>`, not a `v0/base` manifest ID; the capsule's body is P1's JSON rather than the
§5 field list; `DataValue.ofInt`/`ofSyntax` are strings (§1.1 has no integer type). Content
hashes that are not object IDs (the rendered projection's hash, the materialization cache key)
and the receipt HMAC (a stand-in for signatures) are unchanged.
