# W1: Lean replay and identity bugs

Work began 2026-10-20 on `w1-lean-bugs`, based on
`fee94d9be23d9e9902cb006b1e8cdfaa3bcf809c` (`origin/main`).

## Scope and safety

The work covers the M08 `by_cases!` replay failure, the scope of export
identity for module-dependent literals, and fresh stock/fork G1–G6
measurements. Exact declaration-ID validation must remain mandatory.
The historical export identity denominator is 1,142: its 26 mismatches
include four core fixtures and 22 Mathlib groups, rather than 26 Mathlib
groups in addition to the core four.

Three GPT-6-sol agents were delegated disjoint implementation, identity
proof/model, and gate measurement tasks. The primary agent reviews and
integrates their changes and runs validator certification.

Builds and measurements use private caches under this worktree. Shared
Mathlib/toolchain installations are copy sources only. Initial free space
on `/data` was 244 GiB. Heavy work is limited to six processes across the
team. Any services started for certification use a W1-specific prefix
and ports.

## Investigation

The historical M08 failure is reproduced in
`impl/p3/results/m-targets-cold-M08-private.log`: stored declaration
`f5a1a2428cd2…`, replayed declaration `b20f7eca3d55…`.
`sourceReplay` chooses `Mathlib.ParaleanReplay` while capture runs under
`Mathlib.Tactic.ByCases`. Lean's generated macro helper includes this
module name in a literal in the declaration body. The canonical encoder
preserves literal bytes, and the validator correctly rejects the result.

The correction restores the captured module context when
the replay closure has one source module. Identity encoding and validator
acceptance checks are unchanged. A replay model and mutation case preceded
the implementation. Mixed-module closures retain the synthetic module;
this change makes no universal replay-completeness claim for such closures.
No fork patch or fork rebuild is needed.

Targeted fork reproduction preserves the historical M08 package
`4cb846e8e10a561a786626acb401de0870008bb7e08a975539752eb086a795d4`
and declaration
`f5a1a2428cd23c4930dd18c0dfed5c2b5e8d81c1429f48e99e1b0315f9f22bfa`.
The patched cold `check-group` returns `ok: true` without diagnostics.
M08 source, kernel, and isolated replay each pass 3/3 groups.

The five fork hook fixtures pass against a private copy of the pinned
`99967f1ee50a1ee82bb178359ad95b723c8196a2` installation, including the mode-off
fixture. Evidence: `fork/results/w1-fork-subset.json`.

## Identity scope

[The identity analysis](w1-identity.md) inventories the 26 historical export
mismatches and explains why a universal quotient of module-dependent name
literals cannot preserve their observable values. The interface notes now
state the narrower claim explicitly. No literal normalization or export
validator exception was added.

The real `register_simp_attr` witness passes on stock and fork: two identical
commands elaborated in different modules contain different module-name
values in their generated initializer bodies. Logs:
`verification/results/w1/identity-stock.log` and `identity-fork.log`.
The Lean proof separates declaration-name rendering from observable values
inside terms. Initializer materialization remains a separate existing effect
coverage mechanism; it does not establish exact export-body identity.

The three F13 failures have a separate, repairable cause. The old export
lookup paired hygienic declarations by enumeration order. Capture sees the
reference, trace, and option initializers in source order; Lean's exported
constant array lists them in trace, option, reference order. This misassigns
all three bodies even when the original module name is preserved.

The corrected lookup retains each generated name's command discriminator,
imported context, and numeric macro scopes while rebasing only the module
prefix for lookup. It requires a unique candidate and forbids reusing an
exported declaration. The unchanged encoder then checks the exact stored
declaration ID. A focused F13 export improves from 0/3 to 3/3. The
`ExportLookup` model was checked before introducing the lookup behavior;
it has 160 distinct states, six coverage witnesses, and four mutations
(positional matching, missing uniqueness, declaration reuse, and missing
exact-content validation).

## Results

The final stock and fork runs agree on all counts below. The primary agent
independently ran the assertion-based
[gate aggregator](../impl/p1/scripts/aggregate-w1-gates.py) and checked that
both frozen P1 snapshots and the certification source hashes match the
production sources in this checkout.

| Gate | Historical baseline | Final stock / fork |
|---|---|---|
| G1 source / kernel / isolated | 1224 / 1225 / 1224 out of 1225 | **1225/1225 in all three modes**, each toolchain; separate diagnostic probe 8/8 |
| G2 public sets | 1122/1127 | 1122/1127; same five explained spellings, zero reserved names or missing anchors |
| G2 canonical instances | stock 78, fork 90 | stock 78, fork 90 |
| G3 maximum capsule | fixtures 390 B, Mathlib 2868 B | unchanged; zero above-bound groups |
| G4 builds | 22 corpus packages plus diagnostic probe | 23/23, each toolchain |
| G4 exact export identity | 1116/1142; core 81/85 | **1121/1142; core 85/85**; separate probe 7/7 |
| G4 axiom sets / mappings | 1445/1448, zero differ; 5/5 | unchanged; same three missing reference names |
| G5 required negatives | 6/6 rejected | 6/6 rejected; zero rejected groups publishable |
| G6 cross-workspace export | 3 modules, 3/3 exact | unchanged, including the expected early dependency rejection |

Mathlib's exact maximum p50 and p95 capsule ratios are 3.795918 and 9.826087
on both toolchains; the older “9.8” wording was rounded.
Machine-readable baseline comparisons and full provenance are in
[w1-measurement.json](../impl/p1/results/w1-measurement.json) and
[the gate evidence notes](../impl/p1/results/README-w1.md).

### Review discoveries and intermediate measurements

The historical 26 G4 failures comprise **four core fixture groups and 22
Mathlib groups**, rather than 26 additional Mathlib groups. Treating all of
them as necessarily changed body literals was incorrect.

The first raw-hygiene lookup repair recovers all three F13 initializer groups
and M17's `register_label_attr` group at line 102. Stock remeasurement reaches
1120/1142 exact export identities, including core 84/85 and Mathlib
1021/1042. Fork core already reaches 85/85 with that repair. Both toolchains
replay all 1105 Mathlib groups in source, kernel, and isolated modes.

The remaining stock F10 failure is also an association error: the captured
initializer scopes are 5 and 22, while the exported scopes are 5 and 28.
A test-only forced association of 22 with 28 reproduces the original group
ID `04043f8c56590724dac5541fb14bfc763bc7639f61e558590a6622ddb8aafff0`.
This rules out the earlier claim that F10 necessarily changes literal
content. A second, modeled lookup refinement reserves exact matches first
and considers a residual association only when both sides are unique.
The full declaration encoding and ID check remain unchanged.

All 147 initially hashed Lean source, `.olean`, and Lake configuration
artifacts were byte-identical before and after the first lookup-only repair.
That manifest digest is
`3b2d1ff821364156b9acc26ad65606e6d82f68721645e3cc1bc7fd68c2a37519`;
however, parent review found that the hasher omitted `.olean.server` and
`.olean.private`, which both the identity verifier and axiom checker consume.
The corrected hasher includes all 185 artifacts. A fresh full stock G4 run
passed with identical axiom/diagnostic results and an unchanged complete
manifest. The original partial manifest was not used to justify that result.
An intermediate re-export
attempt omitted Mathlib's `LEAN_PATH`; it was discarded and rerun with the
correct environment, rather than counted as a product failure.

Formal evidence was regenerated after the model additions. Four
existing wide positive TLC logs are retained because every checked model
and configuration hash still matches the current source. Negative and
hardened runs record the entire pristine TLA source inventory and must be
rerun after additions, even when their own models are unchanged.
The 24-case positive manifest combines 23 passing checks from this work
session with the final `ExportLookupResidual` check; every checked input hash
was verified before completing that manifest. No provenance block was
rewritten. All **113 default negative/expected-outcome cases** were rerun
successfully against the final complete TLA source inventory, including the
derived fallback-eligibility baseline and mutation.

The final residual lookup model passes 1,040 states, with eight reachability
witnesses and five guard-removal cases. Parent review required reserving
every exact-key candidate, including candidates whose owner is ambiguous or
later fails the body check. The implementation computes that reservation
before assigning residual matches. Six executable source-removal mutations
cover exact-key uniqueness, reuse, exact-key reservation, residual captured
member uniqueness, residual exported candidate uniqueness, and requiring an
empty full-key candidate set before fallback. The parent independently reran
all six against the final stock library. The last case uses an ambiguous
full-key owner, a residual capture under the same stem, and a third unclaimed
exported candidate. Its derived TLA baseline passes 1,296 states; removing
only the fallback eligibility guard violates `NoAmbiguousAccepted`.
The derived fixture and mutation are generated in temporary copies with
their own checked-file hashes; pristine model provenance is unchanged.
The full hardened suite uses `TLC_WORKERS=2 TLC_HEAP=4g` to limit shared-host
load. The Lean/Veil run passes its project-wide axiom audit for 7,292
declarations, including the seven initializer-identity lemmas; no `sorryAx`
or additional axiom is admitted.
All **29 hardened cases pass**, including the complete 7,628,232-state
commit-quorum redundancy check and the final 3,104,542-state readiness
redundancy check. The full archive command, the requested `--tla-only`
re-archive, and `scripts/archive-verification.sh --verify` pass.
The archive contains 24 positive, 113 default expected-outcome, four wide,
and 29 hardened TLC logs. Every entry in its source SHA-256 manifest also
verifies. `origin/main` was fetched again before committing and remains
`fee94d9be23d9e9902cb006b1e8cdfaa3bcf809c`; no rebase is needed.

Final export verification on both toolchains is **1121/1142**, with
**85/85 core groups** and **1021/1042 Mathlib groups**. The separate diagnostic
probe adds 7/7 declaration groups, giving 1128/1149 across all 23 packages.
The remaining 21 corpus failures are exact-content mismatches, not missing
associations: 20 M17 `register_simp_attr` groups and M08's quotation.
For every one of those groups on both toolchains, decoding the canonical
expression table finds a new string literal `"ParaleanExport"` in the
relocated export. Name/reference/level sections remain equal. M17 line 102
and M08 line 23 remain byte-identical. Full per-group evidence is linked from
[the identity analysis](w1-identity.md).

The first repaired exporter completed full validator certification:
**1105/1105 accepted and published, zero failures, 18 store audits passed**.
The two disjoint nine-module shards are checked together by
`impl/p3/scripts/aggregate-mathlib-certification.py`, including exact module
coverage and agreement with capture counts. Their complete reports are retained
under `impl/p3/results/w1/first-lookup-fix/`. The checker ID is
`cf5d2ccbf9c24d1989913c5134946d4f5f37c6f9ed5a07707477b6b7f7c74396`.
All 18,720 files in the private Mathlib/dependency build trees remain unchanged:
1,260,683,296 bytes, manifest digest
`4056a52ff9c810896ef18392a5989e60be7e075abbe089cbf22f8c9018b73548`.
The **final residual-lookup binary also passes 1105/1105**, with 1,105 new
publications, zero duplicates or failures, and all 18 store audits passing.
Its checker ID is
`705c50ee338a2f69f5407963e9d98df5546bb2a69ef2adcb4fabf85cdbd6c2d2`.
The final reports, capture counts, source/binary hashes, and reproduction
notes are in [the certification evidence](../impl/p3/results/w1/README.md).
The complete private Mathlib build manifest remains identical after this
second certification. The W1-only cluster was stopped after verifying its
process ownership; its data remains private and intact.

## Reproduction and environment

The W1 service prefix is `.runs/w1/cluster`. FDB listens on 5289; Garage's
S3/RPC/admin ports are 19439/19440/19441; the S3 guard listens on 19433.
`impl/p3/scripts/cluster-up.sh` starts only this prefix. Service binaries are
read from the P2 installation; service data and credentials are W1-private.

Private installations and build snapshots:

- Fork: `.runs/w1/toolchains/fork-stage1`, copied with dereferencing and
  reflinks, never hardlinks, from the pinned fork installation.
- Final P1: `.runs/w1/p1-stock-final2` and `.runs/w1/p1-fork-final2`,
  separate source-identical builds of this checkout's Lean files.
- Final warm checker: `.runs/w1/warm-final2`, linked against the final fork
  library. Earlier snapshots are retained separately.
- Mathlib: `.runs/w1/mathlib-stock`, `.runs/w1/mathlib-fork`, and a separate
  `.runs/w1/mathlib-fork-validator` for materialization/certification.

Mathlib's reference closure must be compiled with `LEAN_PARALEAN` **unset**;
then check freshness with `LEAN_PARALEAN=1 lake build --no-build`. An initial
attempt to rebuild the closure with every hook on failed in
`Mathlib.Order.OrderDual` and `Mathlib.Lean.Expr.ExtraRecognizers`, whose
source uses stock instance names. That failed copy was retained separately
as `mathlib-fork-validator-mode-on-failed`, with
`.runs/w1/validator-prebuild-mode-on-failed.log`. It is not a certification
base. This is consistent with the mode-off reference build described in
`docs/fork-log.md`.

The stock network cache returned no artifacts for this pin. A private copy
of the existing `.ltar` cache supplied 8,996 artifacts; the stock Mathlib
closure then passed `lake build --no-build`.

The targeted M08 reproducer is:

```sh
python3 impl/p1/tests/m08_source_replay.py \
  --bin .runs/w1/p1-fork-final2/.lake/build/bin/paralean \
  --sysroot .runs/w1/toolchains/fork-stage1 \
  --mathlib .runs/w1/mathlib-fork-validator \
  --out impl/p1/results/w1-m08/targeted.json
```

It checks the production replay's unchanged declaration hashes and separately
re-elaborates each M08 capsule in a test helper, comparing the canonical byte
array directly with the stored object. All three groups have byte-for-byte
equality on stock and fork.
It also restores the old synthetic module as a negative case, mutates the
macro body, and checks same-module, mixed-module, explicit-override, and
empty-closure module selection.

## Proposed plan and README wording

Proposed `plan.md` sentence:
“W1 restores M08's original elaboration module for exact source replay and
replaces order-dependent hygienic export association with unique raw-key
matching plus a guarded singleton residual match; full encoded identity
remains mandatory.”

Proposed `README.md` sentence:
“On the pinned 18-module Mathlib sample, replay and validator certification
cover all 1,105 groups. Exact relocated export identity is a separate claim:
1,121/1,142 corpus groups verify, including all 85 core declaration groups;
the remaining 21 exports contain changed module-name literals and are
rejected.”
