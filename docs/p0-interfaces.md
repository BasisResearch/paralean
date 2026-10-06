# P0 interface freeze (draft v0)

Status: **draft freeze**, 2026-10-05. It fixes the shapes P1–P3 build against: the
encoding, declaration groups, names, source capsules, validator receipts, revisions,
durable acknowledgements and certificates, and snapshots and catalogue records. Every
unresolved choice is marked **OPEN-n** and collected in [§13](#13-open-decisions),
which also marks the ones that block P2.
A field marked OPEN is still frozen as a slot; only its contents may change. Any
change after the freeze bumps `format` (§1.4) and is noted in [p0-log.md](p0-log.md).

Pins: Lean `193c3589a4fc16c4059261ab38cfa365eb24f323` (`nightly-2026-10-03`); Mathlib
`0575336843263378752eeb5f4c75a612327768a2`. The interfaces implement the
[hardened protocol](../verification/veil/HARDENED.md) contracts; §12 maps each
contract to its section. §11 adds the transparent-workspace formats. Evidence for the Lean-specific rules comes from the P0
corpus oracle ([p1-corpus.md](p1-corpus.md), `corpus/reference/`).

## 1. Encoding

### 1.1 Canonical binary encoding (PCE)

All hashed objects use one canonical, length-delimited encoding:

- `uvarint`: unsigned LEB128, minimal length (no redundant `0x80` groups).
- `bytes`: `uvarint len ‖ raw`. `string`: UTF-8 `bytes`, NFC not applied (Lean names are
  compared bytewise).
- `bool`: one byte `0x00`/`0x01`. `nat` (Lean `Nat`, unbounded): `bytes` of minimal
  big-endian magnitude; zero is the empty string.
- `record`: a fixed, versioned field list encoded in declaration order with no field
  tags. Optional fields are `0x00` or `0x01 ‖ value`.
- `list`: `uvarint count ‖ items` in significant order. `set`: a list sorted by the
  items' encoded bytes with duplicates rejected.
- `enum`/sum: one tag byte, then the variant's record.
- There are no maps, floats, or implicit defaults. A decoder rejects trailing bytes,
  non-minimal varints, unsorted sets and unknown tags (a schema-valid decode, as
  assumed by the recovery proofs).

**OPEN-1**: a hand-specified PCE (as above) or deterministic CBOR (RFC 8949 §4.2)
with a fixed schema. PCE is the default; CBOR would only change the bytes, not the
fields.

### 1.2 Hashes and IDs

`H(domain, x) = SHA-256("paralean\x00" ‖ domain ‖ "\x00" ‖ PCE(x))`.
Domains are fixed strings listed with each object: `v0/group`, `v0/capsule`,
`v0/receipt`, `v0/revision`, `v0/marker`, `v0/cert`, `v0/ocert`, `v0/rcert`,
`v0/tombstone`, `v0/snapshot`, `v0/catalog`,
`v0/base`, `v0/chunk`. IDs are the 32-byte digest. Text form is
`<kind>:<lowercase hex>`, e.g. `group:3fa1…`. Collision resistance is assumed
(as in the model). Fetched bytes are always re-hashed before use.

**OPEN-2**: SHA-256 vs BLAKE3. SHA-256 is the default because it needs no new native
dependency in the validator. Lean core has no cryptographic hash. Both P1 and the
validator need an FFI or a pure-Lean implementation; choose one before P2.

### 1.3 Lean terms

A declaration's kernel content is encoded as a **term table**, which preserves DAG
sharing and is never re-hashed per node:

- `names`: a list of Lean `Name` values, each `anonymous | str(prefixIdx, string) |
  num(prefixIdx, nat)`. Entries refer only to earlier entries.
- `levels`: `zero | succ i | max i j | imax i j | param nameIdx`. `mvar` is rejected.
- `exprs`: in topological order, each referring only to earlier indices:
  `bvar nat | sort lvl | const ref [lvl] | app f a | lam n ty body bi |
  forallE n ty body bi | letE n ty val body nondep | lit (nat | string) |
  mdata kvmap e | proj typeRef idx e`. **`fvar` and `mvar` are rejected**: groups are
  closed, as kernel insertion requires. `kvmap` is a sorted list of (name, DataValue).
- Binder names and `BinderInfo` are kept, with macro scopes erased
  (`x._@.M.<hash>._hygCtx._hyg.5` → `x`; P1 notes §2). They do not affect kernel
  checking but are part of the elaborated constant that consumers and the exporter
  see (`intro` names, implicit arguments). Hygienic universe parameters are renamed
  injectively by position (`v._hyg_<i>`). Source positions are never encoded.
- `const ref` is one of `base(nameIdx)` (a constant of the pinned base, §2),
  `self(memberIdx)` (a member of this group), `dep(depIdx)` (an entry in this group's
  dependency map) or `realized(depOrSelf, suffixNameIdx)` (a reserved constant
  re-realized from a base constant; §3.3). `proj typeRef` uses the same refs.
- The table is canonical: nodes are emitted in post-order of the member list,
  deduplicated by structural equality, so equal content gives equal bytes.

Large tables may be split into `chunk:` objects (`v0/chunk`). Chunks are storage
units only; identity is always the whole group.

### 1.4 Versioning

Every top-level object starts with `format : uvarint`. v0 = `0`. A reader rejects
unknown formats. The Lean commit is part of the base manifest, so a format can stay
fixed across Lean bumps while IDs still change.

## 2. Base manifest

`BaseManifest` (`v0/base`) pins everything a group is elaborated and checked against:

| Field | Value at P0 |
|---|---|
| `leanCommit` | `193c3589a4fc16c4059261ab38cfa365eb24f323` |
| `leanVersionString` | `4.36.0-nightly-2026-10-03`. The `.olean` header stores the version string as well as the githash. The release binary **rejects** `.olean` files written by a plain source build (`4.36.0-pre`) with "incompatible header" (p0-log.md), so both fields are pinned. Fork and stock builds that must share `.olean` files set `-DLEAN_SPECIAL_VERSION_DESC=nightly-2026-10-03` |
| `mathlibCommit` | `0575336843263378752eeb5f4c75a612327768a2` |
| `lakeManifestHash` | SHA-256 of Mathlib's `lake-manifest.json` |
| `trustedImports` | the set of (module name, `.olean` SHA-256) for every module of the base the validator loads. These come from the validator's own build, never from a worker |
| `options` | sorted (name, value) list that elaboration and checking depend on (`maxHeartbeats`, `maxRecDepth`, Mathlib's `leanOptions`, …). v0 contains **`Elab.async = false`** (§4.3). Must not contain `debug.skipKernelTC` or any bypass option |
| `prelude` | capsule ID of the controller-generated shared prelude (§4), or none |

A group is meaningful only relative to one `baseID`. Groups with different
`baseID`s are never mixed in one environment.

## 3. Names

### 3.1 Classes

The capture layer classifies every constant a command adds:

| Class | Meaning | Collision key | Published | Exported as |
|---|---|---|---|---|
| `public` | a name a user can write: declared names, **auto-named instances and deriving outputs** (named canonically and injectively, §3.2), and eager auxiliaries derived from a public base of the same group (`casesOn`/`recOn`/`noConfusion`/`below`/`brecOn`/`ctorIdx`/`injEq`/projections/constructors/`SizeOf` instances) | the Lean name; an eager auxiliary collides exactly when its base does | yes | its own spelling |
| `scoped-private` | declared `private` (`_private.<Mod>.0.x`) | none; identity is `(groupID, x)` | yes, group-keyed | a group-unique name (§3.4) |
| `scoped-generated` | synthesized by the elaborator and not user-writable: `proof_n`, `match_n`, `_unary`, `_unsafe_rec`, `_sizeOf_*`, macro and elaborator `_aux_*`, `_hyg` and `initFn` hygiene names, compiler auxiliaries | none; identity is `(groupID, x)` | yes, group-keyed | group-unique |
| `reserved` | created by `realizeConst` (equation lemmas, `eq_def`, `unfold`, `induct`, `fun_cases`, `hinj`, match equations/splitters, congruence lemmas) | none | **never** | re-realized by the consumer |
| `anchor` | a synthetic registry name for a group with no `public` member (§3.5) | the anchor | yes (registry only) | not a kernel constant |

Only `public` and `anchor` names enter collision checks, revision ancestry and
heads.

### 3.2 Classification is by provenance, not spelling

The P0 oracle runs Lean's own spelling classifier
(`isAutoDeclOrPrivate_Internal`, `isReservedName`, `isPrivateName`) over the corpus,
and that classifier disagrees with the contract above in three places:

1. Auto-named instances (`instInhabitedBoxNat`, `instFooNat`) and deriving outputs
   (`instReprBox`, `instReprBox.repr`) are spelled like public names.
2. Consumer realizations include `F._unary.induct` (spelled generated) and
   `_private.<Mod>.0.PSigma.casesOn._arg_pusher` (spelled private, keyed on a *base*
   constant). Both are created by `realizeConst`. (`isReservedName` does recognize the
   private-spelled `match_n.eq_n`/`splitter`, provided it is asked before
   `isPrivateName`.)
3. WF definitions realize `eq_def` inside their own defining command.

So capture records provenance at the point of creation:

- an `addDecl` executed inside `realizeConst` → `reserved`, whatever its spelling,
  in whichever command it happens. It is excluded from the group.
- an instance or deriving output the elaborator named → `public`, under the fork's
  canonical instance name (below);
- an eager auxiliary of a public base in the same group → `public`;
- any other name the elaborator synthesized (auxiliary lemma/match/proof
  generation, macro scopes, hygiene) → `scoped-generated`;
- `private` modifier → `scoped-private`;
- otherwise `public`.

**Canonical instance names.** Stock names drop binders and arguments, so
`Foo (∀ x : Nat, P x)` and `Foo (∀ s : String, Q s)` both become `instFooForall`,
and they gain environment-dependent `_n` suffixes. The fork replaces both with an
injective, environment-independent scheme, so two instance names collide only for
the same instance head. Export writes every instance name explicitly.
**OPEN-24** (decided, §13): the stock name plus a short hash of the instance type's
canonical encoding. P1 implements this for anonymous `instance` commands
(`impl/p1/Paralean/InstName.lean`): the type is the elaborated type with binder
names and `mdata` erased, binder kinds kept, universe parameters numbered by first
occurrence, and constants spelled by module-independent identity. Derived instances
keep the deriving handler's spelling until the fork changes `mkInstName`; a
`_n`-deduplicated derived name is rejected as a collision. Names that attributes
derive from an instance name (`@[to_dual]`) follow the canonical base name.

**Reuse across groups.** Stock `mkMatcherAuxDefinition` and `mkAuxLemma` reuse an
existing `match_n`/`_auxLemma` with the same body, which would make a group's term
refer to another group's scoped name depending on arrival order. The fork disables
that reuse across group boundaries. A `private` declaration referenced by a later
command of the same file is a cross-group reference to a scoped name; capture
rejects it with a diagnostic unless P1 rewrites it to the group-keyed identity
(§3.4).

The spelling classifier is a cross-check. Every disagreement is logged, and an
unexplained disagreement fails capture. **OPEN-3**: the hook points for "synthesized
name" provenance. Instance and deriving naming have no single choke point at this
pin; candidates are `Lean.Elab.Command.mkInstanceName` and the deriving handler
registry, or a post-hoc rule "the command's syntax supplied no `declId` for this
name".

### 3.3 Reserved names

Reserved constants are never transported. A consumer that uses one, and the
validator, call the stock reserved-name action on the pinned base constant. In terms
the reference is `realized(base, suffix)`. Determinism is proved only for public
bases resolved through a snapshot (LEAN-NAMES.md); for scoped bases the reference
goes through the base's group-keyed identity.

### 3.4 Group-keyed identities and export renaming

Inside a group's encoding, scoped members are referred to by `self(memberIdx)`.
Other groups refer to them as `dep(i)` with `deps[i] = (groupID, memberIdx)`. The
original spelling is kept as metadata (`localSpelling`) and is **not** part of
identity. A module relocation therefore never changes identity
(`relocation_invariant`), and neither does auxiliary renaming such as `_proof_1` vs
`_proof_1_1` (§4.3).

**Canonical member numbering.** `memberIdx` does not follow `addDecl` order, which
asynchronous elaboration can permute. Public members come first, sorted by name.
Scoped members follow in order of first reference in a depth-first, left-to-right
traversal of the public members' (type, value) terms, in public-member order. Scoped
members never referenced from a public member come last, sorted by their encoded
declaration bytes with self-references written as `self(⊥)`. The same rule numbers
anchors' groups, with the anchor-producing members treated as public.

**Spelling normal form.** `localSpelling` and every name literal stored in a term
use P1's normal form ([p1-interface-notes.md](p1-interface-notes.md) §2): the
private prefix is stripped, `_pl_*` relocation components are stripped, `_aux`
macro names have their module replaced by `$M`, hygienic declaration names become
`initFn._hyg.<k>` (k = per-group creation order), and generated-instance project
suffixes are stripped. Groups whose *term-level name literals* are hygienic and
module-dependent (e.g. `register_simp_attr`'s `initFn` bodies) cannot be
normalized; P1 reports them as module-dependent. **OPEN-22** (decided, §13):
identity uses canonical numbering and treats spellings as metadata, which is
relocation-invariant and also invariant to auxiliary renaming. P1 implements
canonical numbering and group-ID dependency pins as encoding `paralean-group-v3` (v2 plus §1.1/§1.2 conformance)
([p1-interface-notes.md](p1-interface-notes.md) §7); scoped spellings are unhashed
metadata.

The exporter must materialize distinct kernel names. A `scoped-private` member
becomes `_private.<ExportModule>.0.<x>` in its export module. A `scoped-generated`
member becomes `<x>_pl<first 8 hex of groupID>`. Public members, including eager
auxiliaries and canonically named instances, keep their spelling. **OPEN-4**: how
source capsules referring to a mangled spelling are rewritten.

### 3.5 Anchors

A command whose outputs include no `public` name (for example
`attribute [instance] d`, `attribute [simp] t` or a notation-only command; a bare
`instance` or `deriving instance` now has its canonical public name) gets the anchor
`Paralean.anchor.g<first 32 hex of groupID>`. Anchors are registry names only. They
cannot collide except for identical groups, which deduplicate. **OPEN-5**: whether
commands that add *no constant at all* (`attribute`, `notation`, `open`, `set_option`)
are groups, or frontend state carried only in capsules. The default is capsule-only
state with no group, unless the command changes an extension that a later command's
*kernel* content depends on (instances and simp sets do, through elaboration).

## 4. Declaration group (package)

One elaborated command is one group. The group holds every `addDecl` the command
performs, in execution order, including nested `realizeConst` calls of the command's
own elaboration. Those are reserved and listed only in `realizedDuringElab` for audit.
A capture never publishes a single `addDecl`.

```
GroupManifest (v0/group, ID = H("v0/group", body)):
  format        : uvarint = 0
  baseID        : base:…                  -- §2
  members       : list Member             -- canonical numbering (§3.4)
  deps          : list DepRef             -- kernel deps, sorted by (target ID, memberIdx); see OPEN-23
  effects       : FrontendEffects         -- normalized, §4.2
  terms         : TermTable | list chunk: -- §1.3
Member:
  class         : public | scoped-private | scoped-generated
  publicName    : option Name             -- iff class = public
  localSpelling : Name                    -- original spelling, metadata
  decl          : KernelDecl              -- axiom|defn|thm|opaque|quot|mutualDefn|induct (+ ctor/rec info),
                                          -- levelParams, type/value term indices, hints, safety, `all`
  reducibility  : reducible | instances | semireducible | irreducible
DepRef: groupID : group:…, memberIdx : uvarint
```

Not part of the ID: source text and positions, docstrings, receipts, provenance, the
capsule, scoped members' spellings, and compiled code (IR/LCNF entries). The exporter and the consumer
recompile. Equal kernel content with equal effects and deps deduplicates across
source locations (architecture §Objects).

### 4.1 Package

A package is the transport unit:
`{manifest, capsule:…, receipt:… (once validated), provenance}`, where
`provenance = {workspaceID, file URI, byte range, capture tool hash}`. Only the
manifest determines the group ID.
`PackageID = H("v0/package", (groupID, capsuleID))` identifies a group together with
its frontend input.

**OPEN-23**: what `DepRef` pins. Option (a): the **group ID** for kernel deps (dedupes
byte-identical declarations from different capsules, as architecture §Objects
intends), and the **package ID** for capsule `requires`/`frontendDeps`. Option (b), as
P1 implements now: the package ID everywhere. That is stricter and never dedupes
across capsules. Both are sound. v0 accepts (b); decide by P2, when storage
deduplication matters.

### 4.2 Frontend effects

Kernel declarations alone do not reconstruct attributes, instances, simp sets,
notation or reducibility. `FrontendEffects` is a normalized, hashed summary of what
the command added to persistent extensions, restricted to entries about this group's
members or this command's syntax:

- instances: (member, class, priority, attribute kind);
- simp, `ext`, `to_additive`/translation and other tag attributes:
  (attribute name, member, priority/args);
- notation, syntax and macro declarations: (parser/macro kind name, scope: global |
  scoped ns | local);
- reducibility and `@[expose]`/visibility: (member, value);
- `initialize` declarations: (member, `IO` action member);
- an `extensionDigest`: sorted (extension name, entry count) over all persistent
  extensions except compiler-only ones (`IR.*`, `LCNF.*`, `declRange`,
  `extraModUses`, `exportedAxioms`). The oracle records exactly these deltas per
  command, and replay must reproduce them.

**OPEN-6**: an attribute or extension outside the list above is an unsupported
extraction (a diagnostic, never guessed) until it is added. P1 measures which ones
occur in the corpus.

### 4.3 Elaboration mode and determinism

The P1 finding: under stock asynchronous elaboration, auxiliary proofs get different
names (`aux_pos._proof_1_1` asynchronously vs `_proof_1` synchronously). Export
already pins `set_option Elab.async false`.

**Decision (v1): `Elab.async = false` everywhere, not overridable.** The pin is part
of `BaseManifest.options`. Capture, the validator, replay, the export build, the
`remote%` elaborator and the interactive server all elaborate synchronously, and a
`set_option Elab.async` in user source is rejected with a diagnostic
([p1-interface-notes.md](p1-interface-notes.md) §1, [p1-fork-hooks.md](p1-fork-hooks.md)
item 1). P1 measured the cost on stock `lean`: Mathlib M01–M18 wall time ×1.39, worst
file ×2.2, total CPU time lower; the loss is within-file parallelism. There is no
second, synchronous re-elaboration at capture. Independently, §3.4 makes identity
invariant to scoped spellings and `addDecl` order, so the pin is not the only
defence once OPEN-22 adopts canonical numbering. **OPEN-14** (fork target):
restore asynchronous elaboration in the interactive server, with capture still
synchronous or reading async results, once async and sync captures of the whole
corpus give equal group IDs under canonical numbering.

The P0 baseline shows proof bodies are **not** reproducible across build environments
even with one binary and pinned options. The upstream CI cache and the local build
of the same Mathlib commit agree on every `.olean` and `.olean.server` byte except
the version field. Nine `.olean.private` files differ, though. In three modules a
theorem's proof term differs: `HomologicalComplex.mapBifunctorMapHomotopy.comm₁`,
`Nat.Partrec.Code.evaln_mono._f`, `MonomialOrder.sPolynomial_decomposition`, each
with a different number of private `_simp_n`/`_abel_n` auxiliaries. All types agree.
Local rebuilds are deterministic across thread counts 1, 4 and 32, and with either
binary. Consequences:

- A group ID is computed **once**, at capture, from the captured terms. Everything
  downstream transports and re-checks those terms. Nothing re-derives an ID by
  re-elaborating source on another machine and expects equality.
- Replay and export comparison (§5) require interface equality: names, types,
  non-`Prop` definition values, deps and effects. Exact group-ID equality is a
  measured metric, not a correctness condition.

## 5. Source capsule

The capsule is the frontend input that replays the command. Replay uses the stock
pinned Lean, the base, and the materialized dependency groups.

```
SourceCapsule (v0/capsule, ID = H("v0/capsule", body)):
  format       : uvarint = 0
  baseID       : base:…
  header       : {isModule : bool, imports : list ImportRef}   -- base module | group-materialized module
  scope        : {namespaces : list Name, openDecls : list OpenDecl (incl. `open scoped`),
                  universes : list Name, variables : list VariableBinder (used subset),
                  options : list (Name, DataValue), visibility : public|private section,
                  isMeta : bool, noncomputable : bool, sectionStack : list Name}
  requires     : list capsule:…  -- earlier commands whose frontend state this one needs
                                  -- (local notation/macros/instances, `variable` commands)
  frontendDeps : set package:…   -- groups this command needs in scope but which are absent
                                  -- from its terms: every constant named by a `TermInfo`
                                  -- (`simp [lemma]`), the macro/elaborator groups of the syntax
                                  -- it uses, and effect groups of `attribute [...] c` for used `c`
  command      : string          -- the exact command bytes
  signatureEnd : option uvarint  -- byte offset in `command` where the body starts (`:=`, `where`, `|`); §11.3
  sourceMap    : {uri, startByte, endByte, startLine, startCol}   -- metadata, not hashed
```

`sourceMap` is excluded from the capsule ID. It is carried alongside so diagnostics
and exports keep usable line mappings.

**Replay rule.** Elaborate `requires` (transitively) and then `command` against
`header` plus `scope`. The result must regenerate the group's **interface** exactly:
public names, member classes and count, every member's type, the value of every
non-`Prop`-typed definition, deps and effects. Theorem bodies (and `Prop`-typed
auxiliaries) may differ (§4.3). P1 reports how often the full group ID also matches. Any mismatch, or any `IO`/environment input not
captured (file reads, `run_cmd` side effects, plugins), is an **unsupported
extraction diagnostic**. The capsule is never widened by guessing.

**Capsule size** is the PCE length of the capsule body excluding `requires` targets,
which are counted once each. It is the P1 measurement of interest; the gates are in
p1-corpus.md.

## 6. Validator receipt

```
Receipt (v0/receipt, ID = H("v0/receipt", body)):
  body:
    format        : uvarint = 0
    groupID       : group:…          -- the exact group; never a name or a revision
    baseID        : base:…
    validatorKey  : bytes             -- public key ID
    validatorBin  : bytes             -- SHA-256 of the validator executable
    policyID      : H(policy)          -- allowed axioms {propext, Classical.choice, Quot.sound},
                                       -- forbidden options, unsafe policy, target-contract rules
    requestID     : option bytes      -- job envelope that asked for this check (OPEN-7)
    targetID      : option bytes      -- pinned target contract, if the group realizes one
    verdict       : accepted | rejected(reason)
    axioms        : set Name          -- transitive axioms of every member, as checked
  signature       : Ed25519(validatorKey, H("v0/receipt", body))
```

Rules (PublicationReceipts):

- A worker **stages** group `g` only while holding a receipt `r` with
  `r.groupID = g`, `verdict = accepted`, a signature valid under a trusted key, and
  `policyID`/`baseID` in the accepted set. Workers never self-certify; a worker's own
  check is a hint only.
- The validator rebuilds the environment from `trustedImports` plus the dependency
  groups' **receipted** manifests. It re-runs the kernel on every member, reads the
  closure's axioms, and re-realizes reserved names. It never trusts worker `.olean`
  files or axiom summaries. P0 evidence (corpus N3): with `debug.skipKernelTC` an
  ill-typed theorem is accepted and reports *no* axioms. Only kernel re-checking
  catches it.
- Axiom policy: any axiom outside the allowed set rejects. That includes the
  `<decl>._native.native_decide.ax_*` auxiliary axioms `native_decide` emits at this
  pin (corpus N6), `sorryAx`, and new user axioms. Module-system axiom-shaped
  interfaces of trusted imports are followed by provenance (lean-integration.md).
- **OPEN-7**: the model does not bind receipts to request, epoch or worker. v0
  reserves `requestID` and `targetID` and requires them in P3. Until then a receipt
  for `g` suffices for any request whose contract `g` satisfies.

## 7. Revisions

```
Revision (v0/revision, ID = H("v0/revision", body)):
  format     : uvarint = 0
  groupID    : group:…
  name       : Name                 -- one public or anchor name of the group (one revision per name)
  parents    : set revision:…       -- revisions of the same name this edit actually read
  capsuleID  : capsule:…
  workspace  : WorkspaceID
```

Rules (architecture §Revisions, TargetNames):

- Every parent is admitted, has the same `name`, and the ancestry is transitively
  closed (admitted ancestor closure). No timestamps or Lamport clocks are used for
  supersession.
- Heads(name) are the known revisions not superseded by a known descendant. Zero
  heads means unknown, one means a candidate, and more than one means an eventual
  error in the registry: no checkpoint containing any of them commits. The registry
  picks no winner; the rendered workspace view does (§11.5), without resolving the
  registry conflict.
- A revert is a new revision whose `groupID` points at old content. An ancestor is
  never resurrected as a head.
- **Target names**: each target name has one store record,

  ```
  TargetRecord (mutable, linearizable, one per target name):
    name  : Name
    owner : WorkspaceID
    epoch : uvarint                 -- bumped on every reassignment
    head  : option revision:…       -- latest published proof of the name
  ```

  Only the owner prepares a group declaring that name. The preparer reads owner,
  epoch and head in **one** read, stamps the proof with that epoch, and lists the
  recorded `head` as a parent. A scan of markers or certificates is not a
  substitute: it can miss a published proof that has no certificate quorum yet.
  Publishing a target proof is the atomic publish write of §8.2, conditional on
  `epoch` (and `owner`), and the same write sets `head`. Either the owner
  serializes prepare and publish per name, or the write compares-and-swaps `head`.
  Reassignment (owner crash or partition) is a linearizable write that bumps
  `epoch`, so an old owner's pending proof can never publish. Proofs of a target
  therefore form a chain with a unique head across any number of handovers
  (TargetNames `recorded_head_tops_chain`, `target_head_unique`). Targets declared
  by one group are assigned jointly. The controller signs assignments;
  `TargetAssignment = {name, owner, epoch, assignedBy, signature}` is stored with
  the snapshot.
- Commit freshness: a commit selects the unique current head of every name in its
  contents, using the committer's knowledge immediately before the commit. This
  holds also for a repeated commit of the same checkpoint.

## 8. Durable acknowledgement, publication and certificates

### 8.1 Typed store

The store holds typed immutable objects keyed by `(kind, ID)`:
`payload` (group manifest and chunks), `capsule`, `receipt`, `revision`, `manifest`
(export/snapshot), `catalog`, `marker`, `cert`, `ocert`, `rcert`, `tombstone`. The mutable
`TargetRecord`s (§7) and the catalogue fence (§9) live in the same linearizable
metadata store. Put verifies `H(kind domain, bytes)
= ID` before acknowledging. Types are never confused across kinds. Groups rejected
at capture are kept only in a separate audit namespace, never in the publishable
store.

```
ReplicaAck   = {replica : ReplicaID, kind, id, verified : true}
DurableAck   = {kind, id, acks : set ReplicaAck}   -- acks cover some write quorum W
```

Quorum systems are configuration: `W` (write quorums) and `R` (recovery quorums)
with `meet(w, r)` for every pair. The proofs use this interface, not majority
arithmetic. **OPEN-9** (resolved, signed off 2026-10-05): [store.md](store.md).
FoundationDB holds the metadata kinds, the target records and the fence; S3 holds
`payload`, `capsule`, `manifest` and chunk objects, written before any metadata
that names them. The pair is one abstract replica, `W = R = {{σ}}`; physical
redundancy is the stores' configuration (FoundationDB `triple` or
`three_data_hall`, one region).

### 8.2 Publication

```
Marker (v0/marker, ID = H("v0/marker", body)):
  groupID : group:…, revisionIDs : set revision:…, receiptID : receipt:…
```

Publication has one atomic point. In order:

1. The payload, capsule, receipt, revisions and the dependency closure are durably
   acknowledged.
2. The marker is durably acknowledged on a write quorum. A partial marker upload
   remains staged.
3. A single conditional publish write in the metadata store makes the group
   published. For a group declaring a target name it is conditional on the
   `TargetRecord` epoch and updates `head` (§7).
4. Only after that write succeeds does anyone write certificates (§8.3).

A writer whose step 3 failed never certifies the group, so its marker stays
undiscoverable however many replicas hold it.

### 8.3 Acknowledgement certificates

```
Cert (v0/cert, ID = H("v0/cert", body)):
  replica  : ReplicaID     -- the replica that stores it
  markerID : marker:…
  groupID  : group:…
  writer   : WorkspaceID   -- must already know the group as published
  sig      : Signature     -- by the writer, so a repair cannot forge one
```

- A writer writes a certificate only after observing the publish write of §8.2
  succeed (AckCertificates `cert_sound` assumes exactly this; the TLA mutation
  `cert_put_unknown` shows it is load-bearing).

- A certificate is a separate durable record on its replica. It is not marker bytes
  and is never inferred from them. A lost replica's certificates are gone. (AckCertificates
  `guard_necessity`: an acknowledged and a staged marker can have identical surviving
  bytes.)
- **Discovery** of an already-published group reads certificates from live replicas
  only, never raw markers. A scan of any fully live recovery quorum finds every
  certificate-acknowledged group.
- **Checkpoint commit** waits until every group in the checkpoint has certificates on a
  full write quorum (verified replies).
- Receiving an already-published group requires a live replica certificate for it.

## 9. Snapshots, checkpoints and the catalogue

```
Snapshot (v0/snapshot, ID = H("v0/snapshot", body)):
  format        : uvarint = 0
  workspace     : WorkspaceID
  baseID        : base:…
  contents      : set revision:…   -- closed under deps and ancestry; one head per name
  predecessors  : set snapshot:…
  targets       : set TargetAssignment
  sourceRoot    : manifest:…        -- export layout: files → ordered capsule IDs
  buildReceipt  : manifest:…        -- stock-build attestation (below)
```

`BuildReceipt` = `{exporterBin, leanCommit, mathlibCommit, layoutID, buildLogHash,
targetChecks : list (targetID, groupID, statementMatches, axioms), verdict}`, produced
by a clean build with the frozen stock binary (`~/p0-deps/lean-stock-193c3589`, see
p0-log.md). An empty buildable snapshot does not complete a task. Every required
target must be present with its pinned contract.

```
CatalogRecord (v0/catalog, ID = H("v0/catalog", body)):
  workspace   : WorkspaceID
  snapshotID  : snapshot:…
  predecessor : option catalog:…
  token       : {rank : uvarint, holder : WorkspaceID}   -- the writer's fence token
```

```
ObjectCert (v0/ocert, per replica):            CommitCert (v0/rcert, per replica):
  replica  : ReplicaID                           replica  : ReplicaID
  kind, id : the manifest or a payload           catalogID: catalog:…
  writer   : WorkspaceID                         token    : {rank, holder}   -- = record's token
  sig      : Signature                           sig      : Signature
```

- **Tokens** are issued by the fence authority, signed and bound to `holder`. Each
  rank is issued once. The record's token sits under the record's hash, and the
  record is signed by the holder.
- **First write**: the first Put of a catalogue record is a conditional write that
  succeeds only if `token.rank == fence`. Fence rotation is a linearizable write to
  the same store.
- **Repair and Ack** are unconditional, so work written before a rotation can still
  be acknowledged and repaired. A replica accepts a repair Put only for bytes some
  replica already holds (signed record bytes make this checkable).
- **Commit**: committing a record writes a `CommitCert` on each replica, each a
  conditional write that succeeds only if `token.rank == fence`, and only after
  the writer's own durable Ack of the record bytes. `ObjectCert`s for the manifest
  and every payload follow their own Acks and are not fenced. Fencing the first
  write alone is not enough: a stale writer can first-write one replica before a
  rotation and repair and acknowledge it after (CatalogFencing
  `late_ack_and_repair_execution`). That record never gets a `CommitCert`, so it
  is never adopted (CatalogCertificates `uncertified_not_committed`).
- **Completion**: a task is reported complete only after the catalogue record for the
  exact snapshot is committed, i.e. its `CommitCert` and the manifest and payload
  `ObjectCert`s are durable, in the same store as its payloads and manifest.
- **Recovery**: enumerate catalogue records and certificates from a fully live
  recovery quorum. A record is **ready** when its `CommitCert`, its manifest's
  `ObjectCert` and every payload's `ObjectCert` are each held by every live member
  of some write quorum. Readiness never asks whether surviving bytes were once
  acknowledged; a lone surviving copy cannot show that. Validate the decoded
  records (schema, workspace, buildable, complete), reconstruct causal heads, and
  adopt only ready records. The selected record was committed while its writer
  held the fence (`selected_fenced`). Recovery never depends on the desktop's last
  snapshot ID. Certificates are not repaired in v0: a record stays adoptable
  after replica loss only if its certificates were already durable.
  **OPEN-10**: the external fenced ownership service that issues ranks. The
  default is a counter in the catalogue store itself, rotated by the controller.

## 10. Workspace and job envelope

`WorkspaceID` is 16 random bytes, fresh per workspace. A replacement after worker
loss gets a fresh ID unless the fence service transfers ownership. A timeout alone
grants nothing. **OPEN-11**: the job envelope (P3) is reserved here as
`{requestID, groupID | capsuleID, baseID, policyID, targetID?, deadline}`; its fields
may still change.

## 11. Transparent workspaces

This section freezes the formats behind the *transparent workspaces* design
(architecture.md, "Transparent workspaces"). Each agent's file shows teammates'
published declarations in place, as a replicated per-file sequence. Everything here
sits **on top of** publication (§8). Only published groups (receipted, durably
acknowledged, certified) ever appear in a file sequence.

**Verification status.** §11.5 changes the protocol: unrelated same-name
declarations stop being an eventual error in the rendered view and get a
deterministic winner. The registry still records the conflict, and it still
blocks every commit containing either group (§11.5, OPEN-26). The placement,
rendering and naming rules are modelled in `verification/tla/Workspace.tla` and
`verification/veil/Paralean/Workspaces.lean` ([notes](../verification/veil/WORKSPACES.md)):
only live heads render, in stable order; intention is preserved; a revised winner
keeps the name in its lineage; the rendered view is a function of the known
records. Byte-level canonical printing (§11.3), git projection (§11.6) and
`remote%` checking (§11.2) are not modelled.

### 11.1 Publication record

The marker of §8.2 becomes the publication record. The new fields are part of the
marker body and therefore of its ID:

```
Marker (v0/marker):
  groupID     : group:…
  revisionIDs : set revision:…
  receiptID   : receipt:…
  filePath    : string        -- workspace-relative POSIX path, NFC, no `.`/`..`, `/`-separated
  anchor      : fileStart | after(group:…)   -- nearest published or own-staged declaration above it
  lamport     : uvarint       -- Lamport timestamp (§11.4)
  author      : AgentID       -- 16 bytes; registered with the controller (§11.6)
  rootPath    : list (group:…, lamport, author)   -- anchor path of the lineage root, file start first
  lineageKeys : list (Name, lamport, author)      -- per public name: lowest key in its lineage
```

"Declaration ID" in this section means the **group ID**. One file element is one
published command. `anchor` is the nearest group above the new one in the author's
local file that is published or that the author has itself staged. Unstaged
drafts above it are skipped. If there is none, the anchor is `fileStart`. A group
publishes only after its anchor is known to the publisher, so an author's batch of
new declarations keeps its order. The author computes `rootPath` and
`lineageKeys` at staging from groups it knows or has staged. Rendering and naming
read only these carried fields of known records, never the anchors or ancestors
of unknown ones (Workspaces `render_carried`, `view_carried`), so no causal
delivery is required. `rootPath` is O(depth) in size.

### 11.2 `remote%` term syntax

```
term ::= "remote%" declId        declId ::= hex64 | "group:" hex64
```

`remote% X` is a fork-only term elaborator. It may be the whole body of a `theorem`,
`def`, `abbrev`, `instance` or `opaque` command whose declared name is a public name
of group `X`. It checks, in this order, and fails with a distinct diagnostic for each:

1. **Name.** `X` is published (a live certificate is found, §8.3). The enclosing
   command's fully qualified name equals a `public` member `m` of `X`, after §11.5
   renaming. The command kind matches `m`'s kernel kind (theorem/def/opaque) and
   reducibility.
2. **Statement.** The enclosing command's elaborated signature (level parameter
   names in order, plus the type, with binder names and binder info) is `==`
   (syntactic `Expr` equality after instantiating metavariables) to `m`'s published
   type. Definitional equality is **not** accepted.
3. **Dependency versions.** Every constant reached from the elaborated signature, and
   every entry of `X.deps`, resolves in the current environment to exactly the
   group ID that `X`'s manifest pins. A same-named constant from another group is a
   version conflict, reported, never rebound.
4. **Receipt.** `X`'s marker names a receipt with `groupID = X`,
   `verdict = accepted`, a signature valid under a trusted validator key, and
   `baseID`/`policyID` in the accepted set (§6).

On success, the command adds `X`'s members exactly as published (materialized from
the store, kernel-checked locally unless the environment already holds them). The
body term is `m`'s published value. `remote%` never accepts a body it cannot fetch.
The P1 prototype deviates: it never fetches theorem proofs in working copies, adds
a receipt-backed placeholder axiom instead, and checks an HMAC under a shared key
in place of the Ed25519 signature of §6 ([p1-transparent.md](p1-transparent.md)).
This section is the v1 requirement.
**OPEN-16**: commands without a term body (`inductive`, `structure`, `class`,
`mutual`, attribute-only and notation commands) use a command form,
`remote_decl% <declId>`, with checks 1, 3 and 4 and, for check 2, comparison of every
member's type.

### 11.3 Canonical rendering of a file's published projection

`render(path, state)` returns bytes and is a pure function of the replicated state:
the file sequence (§11.4), the publication records, capsules and manifests it names,
and the §11.5 renaming. Viewer, clock, locale and the local working copy do not
affect it.

1. Encoding: UTF-8, no BOM, LF line endings, no trailing whitespace on any line, and
   exactly one final LF. Tabs are kept only inside capsule text.
2. Header: `module` on line 1 if every element's capsule has `isModule`. Elements
   that disagree on `isModule` make the projection fail with a diagnostic. Then the
   imports: the union of the elements' capsule imports, minus imports of this file
   itself, deduplicated. Base modules come first, sorted by module name (bytewise),
   then workspace files, sorted by path. In a module the keyword is `public import`
   when any element imports it publicly, otherwise `import`. One import per line.
   Then one blank line.
3. Body: the visible elements in sequence order, grouped into maximal runs with
   identical capsule `scope`. Each run is one block:
   `public section`/`noncomputable section` (if set), then `namespace <full dotted>`
   (if any), then `open …` lines in capsule order, then `universe …` (sorted), then
   `variable …` lines in capsule order, then `set_option k v` lines (sorted by `k`),
   then the elements, then the matching `end` lines in reverse. Blocks and elements
   are separated by exactly one blank line. There are no comments other than those
   inside capsule text.
4. Element text: the capsule's command bytes up to the start of the body
   (`signatureEnd`, a new capsule field), including the docstring and attributes,
   with trailing whitespace stripped. Then ` :=`, LF, two spaces,
   `remote% <64 hex>`. Commands without a term body render as
   `remote_decl% <64 hex>` on one line, preceded by their docstring if any.
   **Every** element renders this way, including the author's own. The author's
   working copy is not the projection.
5. Renamed losers (§11.5) render with their new name substituted in the
   declared name only. References inside capsule text are not rewritten
   (**OPEN-17**: capsule rewriting for renamed dependencies).
6. An empty sequence renders as the empty file (zero bytes).

The **source rendering** used for git (§11.6) and stock export applies the same rules,
but writes each element's full capsule command bytes instead of the `remote%` stub.

### 11.4 Per-file declaration list CRDT

One state-based CRDT object per `filePath`:

```
FileSeq(path) = (Inserts : set Marker with filePath = path,
                 Tombstones : set Tombstone)
Tombstone (v0/tombstone): {filePath, target : group:…, lamport, author, receiptID?}
```

- **Element** = group ID. Within one file a group appears at most once. If several
  markers insert the same group into one file, the one with the lowest
  `(lamport, author)` defines its position, and the others are ignored except as
  history.
- **Order (RGA).** Build a tree: each element's parent is its anchor, and `fileStart`
  is the root. Siblings are ordered by **descending** `(lamport, author)`
  (lexicographic, `author` compared bytewise), so a later insertion at the same
  anchor sits closer to it, as in RGA. The sequence is the pre-order traversal
  without the root. **OPEN-18**: Fugue instead of RGA, to avoid interleaving of
  concurrent runs. That would add a `rightAnchor : option group:…` field to
  `Marker`, which is reserved now and absent in v0.
- **Lamport clock.** Each agent keeps `L`. On receiving any marker or tombstone,
  `L := max(L, its lamport)`. On staging, `L := L + 1`, and the new record's
  `lamport` is that value. `L` is persisted before use, so a restarted agent never
  reuses a timestamp. A record's `lamport` must exceed its anchor's, and a
  validator of the record rejects it otherwise.
- **Deletes** are tombstones. A tombstoned element stays in the tree as an anchor and
  is hidden from rendering. A tombstone never removes the group from the registry,
  from snapshots, or as a dependency. **OPEN-19**: who may delete. The v0 default is
  the element's author or the controller.
- **Moves** are a tombstone plus a new insert of the same group with a new anchor.
  Under the "lowest `(lamport, author)` wins" rule above, a re-insert is a no-op.
  **OPEN-20**: allow moves by exempting tombstoned positions from that rule.
- **Merge** is set union of `Inserts` and `Tombstones`. It is commutative,
  associative and idempotent, and rendering is deterministic, so replicas that hold
  the same sets produce identical bytes.
- Tombstones are stored, acknowledged and certificate-discovered like markers. They
  are a new typed store kind, `tombstone`.

### 11.5 Name collisions under Lamport order

Two published groups `g ≠ h` that both have the public name `x`, and neither of which
is an ancestor of the other in `x`'s revision history, are **unrelated**. Related
groups follow the revision and head rules of §7.

- Candidates for `x` are the **live** heads declaring `x`: known, not tombstoned,
  and not superseded by any known revision, including a revision of the group for
  another of its names. A superseded group holds no name.
- Each candidate's key is its `lineageKeys` entry for `x`: the lowest
  `(lamport, author)` in its lineage. The lowest key keeps `x`. Revising the winner
  keeps the name in the winner's lineage; a concurrent revision of that lineage by
  another author may take it, but no other lineage can.
- Every other candidate is renamed, deterministically, into a reserved namespace
  that user source cannot write, for example `x` with a `✝pl<first 8 hex of group
  ID>` final component (**OPEN-25**: exact spelling). Validators reject any group
  declaring a reserved name, so a later declaration never clashes with a fresh name.
- Renaming is hierarchical: the group's derived public names (`T.mk`, `T.casesOn`,
  ...) move with it and keep their namespace. The group ID and every
  `dep(groupID, idx)` reference are unchanged. Tactic text in the losing author's
  capsules (`simp [x]`, `rw [x]`) needs a textual rename (OPEN-17).
- The rename is a projection over replicated state: the registry, rendering, `remote%`
  and the exporter apply it. The winner changes only when a lower-keyed candidate
  arrives, the winner is tombstoned, or the winner's lineage is superseded by a
  revision for another name (Workspaces `winner_change_explained`). A snapshot fixes the mapping in force
  at commit (`renames : set (group:…, Name, Name)` is added to `Snapshot`), and old
  snapshots keep theirs.
- **Rendered is not committable.** The rename does not resolve the registry
  conflict. Groups' `buildable` rejects a snapshot holding both colliding groups,
  and `current` rejects any snapshot holding either while the committer knows both
  heads. A working copy can therefore show and elaborate a renamed loser that no
  checkpoint can contain until a revision naming both heads, or a tombstone of the
  loser plus a republication under the new name, lands. Until then `renames` holds
  no pair for an unresolved conflict. **OPEN-26**: whether the commit rule should
  accept the rendered renaming; not modelled.
- **Target names keep the owner rule** (§7). Only the owner stages a group declaring
  a target name, and each new proof revises the recorded head, so target names
  never reach this rule. A non-owner group declaring a target name is rejected at
  staging, not renamed.

### 11.6 Git projection

A deterministic git repository derived from the replicated state, for humans and
stock tools:

- **Tree.** For each file, the source rendering (§11.3) of the state after applying
  the records up to the commit. A root `lean-toolchain` (the pinned base) and a
  `lakefile.toml` are generated by the controller.
- **Commits.** One commit per insert or tombstone record, in ascending
  `(lamport, author)` order (a linear extension of causality). The git **author** is
  the record's `author` agent, looked up in the controller's agent registry
  `AgentID → (name, email)`. Teammates' insertions therefore appear as commits by
  those teammates. The committer is the controller identity. Author and committer
  dates are `1970-01-01T00:00:00Z + lamport seconds`, so commit hashes are a pure
  function of state. Message: `<insert|delete> <publicName or anchor> in <path>`,
  with trailers `Paralean-Group:`, `Paralean-Lamport:`, `Paralean-Receipt:`.
- **Late records.** A record with a lower `(lamport, author)` than an existing commit
  changes the linear order. v0 rewrites the projection branch `paralean/projection`,
  which is not fast-forward safe. Every committed snapshot gets an immutable tag
  `paralean/snapshot/<snapshotID>` that is never rewritten. **OPEN-21**: a
  history-preserving alternative (per-agent branches with merge commits).

## 12. Hardened contract coverage

| Hardened contract (HARDENED.md) | Where |
|---|---|
| Validators sign receipts over the exact group ID; workers stage only with a receipt | §6 (`groupID`, staging rule), §8.2 (`receiptID` in marker) |
| Target owner and epoch in one store record with the recorded head; new proofs revise the head; epoch-conditional publish updates it | §7 `TargetRecord`, §8.2 step 3, §9 `targets` |
| First catalogue writes and commit certificates conditional on token = fence; unconditional repair of existing bytes; adoption only of certified records | §9 |
| Atomic publish point: marker durable, then conditional publish write, then certificates | §8.2, §8.3 |
| Per-replica acknowledgement certificates, separate from marker bytes; discovery and commit read certificates | §8.3 |
| Command-granularity capture with a trusted classifier; group-keyed scoped names renamed on export; reserved names re-realized | §3, §4 |
| Canonical injective instance names; no matcher/aux-lemma reuse across groups | §3.2 |
| Constant-free commands need an anchor | §3.5 |
| Joint completion: durable catalogue record before completion | §9 completion |
| Transparent workspaces: placement with carried root paths, live-head rendering, lineage-key winners, reserved fresh names, persistent Lamport clocks | §11 (rendering and naming modelled; printing, git and `remote%` not) |

## 13. Open decisions

"Blocks P2" means P2 persists bytes or keys that depend on the decision, or
implements the behaviour itself; changing it afterwards bumps `format` and
invalidates P2's stored data and fixtures. For those rows, "Proposed" is a concrete
resolution. Rows marked **Decided** were signed off on 2026-10-05 and are recorded in
[p0-log.md](p0-log.md); for them the resolution replaces the v0 default.

| ID | Decision | Default in v0 | Decide by | Blocks P2 | Resolution |
|---|---|---|---|---|---|
| OPEN-1 | PCE vs deterministic CBOR | PCE | P1 start | yes: the bytes of every ID | **Decided 2026-10-05.** PCE exactly as §1.1. P1's encoder is brought to §1.1 byte for byte and checked against golden vectors shared with the validator |
| OPEN-2 | SHA-256 vs BLAKE3; FFI vs pure Lean | SHA-256 | before P2 | yes: every ID and the S3 checksum ([store.md](store.md)) | **Decided 2026-10-05.** SHA-256. Capture keeps P1's pure-Lean `Sha256.lean`; the validator and the store client use a native implementation tested against it. Storing the hashed preimage lets S3's `x-amz-checksum-sha256` verify uploads |
| OPEN-3 | Hook points for "synthesized name" provenance (instances, deriving) | post-hoc "no `declId` supplied" rule, cross-checked against the spelling classifier | P1 | no | |
| OPEN-4 | Renamed scoped instances: attribute re-application and capsule rewriting | re-apply with original priority | P1 export | no | |
| OPEN-5 | Whether constant-free commands are groups | P1's choice: global `attribute [...] c` commands are anchored *effect groups* that consumers of `c` depend on (`frontendDeps`); section-local effects (`local notation`, `attribute [local …]`, `open scoped`) are not published and travel as text in later capsules of the section | P1 | no (P1's choice is in force) | |
| OPEN-6 | Extension coverage list for `FrontendEffects` | list in §4.2; others are unsupported | P1 (measured on corpus) | no; additions bump `format` | |
| OPEN-7 | Receipt binding to request, epoch and target | slots reserved; required from P3 | P3 | no (slots reserved) | |
| OPEN-8 | ~~Target ownership transfer and owner failure~~ | resolved: epoch-fenced reassignment with recorded head (§7) | — | n/a | |
| OPEN-9 | ~~Concrete durable store; quorum configuration~~ | resolved, signed off 2026-10-05: [store.md](store.md) (self-hosted FoundationDB metadata, S3-compatible payloads, one abstract replica) | — | n/a | |
| OPEN-10 | Fence/rank authority | counter in the catalogue store | P2 | yes: fenced writes are P2 work | **Decided 2026-10-05.** `fence` key in FoundationDB, rotated by the controller in one read-modify-write transaction that also writes the signed token `token/<rank>` (store.md T3); never an atomic add |
| OPEN-11 | Job envelope fields | reserved shape §10 | P3 | no | |
| OPEN-12 | Whether docstrings and `declRange` belong in capsule metadata or effects | capsule metadata (not hashed) | P1 | no | |
| OPEN-13 | Treatment of `meta`/`initialize` groups (IO at import) in validators | validator replays `initialize` only for allow-listed effects; others unsupported | P1 | no | |
| OPEN-14 | Restore asynchronous interactive elaboration (fork target) | **Decided 2026-10-05** for v1: `Elab.async = false` everywhere, not overridable (§4.3) | after OPEN-22 and a corpus run of async vs sync IDs | no | |
| OPEN-15 | ~~Model and proof for Lamport collision resolution and file sequences~~ | resolved: `Workspace.tla`, `Workspaces.lean`; byte printing and git projection remain unmodelled | — | n/a | |
| OPEN-16 | `remote_decl%` command form for commands without a term body | as §11.2 | P1/P3 | no | |
| OPEN-17 | Rewriting capsule text that refers to renamed names | not rewritten; the export may fail with a diagnostic | P1 export | no | |
| OPEN-18 | RGA vs Fugue | RGA; `rightAnchor` slot reserved | before P3 | yes, if P2 stores §11.1 markers: the marker bytes | **Decided 2026-10-05.** Keep RGA; encode `rightAnchor` now as an optional field fixed to `0x00`, so a later switch to Fugue does not change the marker format |
| OPEN-19 | Delete authority for file elements | author or controller | P3 | no | |
| OPEN-20 | Moves (re-insert after tombstone) | not supported in v0 | P3 | no | |
| OPEN-21 | History-preserving git projection | rewritten `paralean/projection` branch plus immutable snapshot tags | P5 | no | |
| OPEN-22 | Identity via canonical numbering vs P1's normalized spellings | P1's normalized spellings accepted while `Elab.async` is pinned | before P2 | yes: group-ID bytes | **Decided 2026-10-05.** Canonical numbering (§3.4), spellings as unhashed metadata. It is also invariant to auxiliary renaming, which OPEN-14 needs. P1 changes `self <name>` to `self <memberIdx>`; G4 identity is re-measured Implemented in P1 (encoding v2); G1 and G4 re-measured: 1224/1225 and 1116/1142. |
| OPEN-23 | `DepRef` pins group ID or package ID | package ID (P1) accepted | P2 | yes: dependency bytes in group IDs and storage deduplication | **Decided 2026-10-05.** Option (a): group ID for kernel `deps`, package ID for `requires` and `frontendDeps`. Byte-identical declarations from different capsules then deduplicate, and replay still finds a capsule through `frontendDeps` Implemented in P1 (encoding v2); G1 and G4 re-measured: 1224/1225 and 1116/1142. |
| OPEN-24 | Injective canonical instance-naming scheme | stock name plus a short hash of the instance type's canonical encoding | P1 | yes: public names enter membership, group IDs and collision keys | **Decided 2026-10-05.** Stock base name without `_n`, then `_` and the first 8 hex of `H("v0/insttype", type term)` with binder names erased, for every auto-named instance. Export writes the name explicitly. A truncated-hash clash is a spurious public-name collision, diagnosed, not unsound Implemented in P1 for anonymous instances; derived instances need the fork. |
| OPEN-25 | Spelling of the reserved fresh-name namespace | a final component the parser rejects in user source | P1 | no (rendering and validation, P3) | |
| OPEN-26 | Whether a snapshot may commit a rendered collision rename (§11.5) | no: Groups' `buildable` and `current` reject it; resolution is a registry revision or tombstone | P3 | no | |
