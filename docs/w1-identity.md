# W1 initializer and quotation identity boundary

The recorded P1/Fork G4 result is **1116/1142 exact exported declaration-group IDs**. The other 26 groups build, but their re-encoded `.olean` declarations do not equal the stored group IDs. This is an exact-content exception, not a failed Lean build. The four core exceptions are the `81/85` result. The inventory below is from the fork gate logs at the frozen P1 baseline; IDs in those logs are prefixes and are specific to that base and encoding version.

| Source group | Count | Exact mismatch locations | Capture/replay evidence |
|---|---:|---|---|
| `F10SimpAttrDecl` | 1 | line 4, `register_simp_attr f10_simps` | Two generated `initFn` members flagged `unsupported:module-dependent-literal`; initializer materialized for consumers. |
| `F13InitDecl` | 3 | lines 6, 8, 10: `IO.Ref` initializer, trace-class initializer, `register_option` | Materialized for consumers; all three mismatch at export. Only line 8 is flagged by the capture literal heuristic. |
| Mathlib M17 `Tactic/Attr/Register` | 21 | lines 25, 35, 38, 41, 44, 48, 52, 56, 65, 74, 88, 91, 94, 97, 102, 105, 108, 111, 114, 117, 154 | Twenty `register_simp_attr` commands and one `register_label_attr` (line 102). All 21 initializer groups are materialized; source replay reports 22/22 groups, and export verifies 0/21 declaration groups exactly. |
| Mathlib M08 `Tactic/ByCases` | 1 | line 37, `macro_rules` quoting local `try_push_neg_at` syntax | The one quoted generated macro body is flagged at capture, fails source and isolated replay (2/3 groups), and mismatches at export (1/2 declaration groups exact). |

Evidence: [core fork log](../impl/p1/results/fork/core.log), [M17 fork log](../impl/p1/results/fork/mathlib-M17.log), [M08 fork log](../impl/p1/results/fork/mathlib-M08.log), [P1 gate](p1-gate.md), [fork gate](fork-log.md). The core mismatch prefixes in `core.log` are `1520c26827f6 ≠ 2cb453be7de5`, `ceab74274d8b ≠ 9416a4c616b5`, `f743b319265d ≠ 39c06086b391`, and `1dc1224dc415 ≠ 2a61123b4b8f` in the order above. The M17 log lists 21 mismatch pairs; the M08 pair is `1d241b0bb068 ≠ ec5cc4449883`.

## Why a name quotient is insufficient

P1's `normName` normalizes **declaration and reference names** (private prefixes, relocation components, macro-scope tails) in [Model.lean](../impl/p1/Paralean/Model.lean). Scoped member spellings are metadata outside the group hash. An `Expr.lit (.strVal s)` in a **kernel value** is encoded verbatim in [Encode.lean](../impl/p1/Paralean/Encode.lean). Lean represents a quoted `Name` with string components in that value, and an initializer or macro can inspect the resulting `Name`. Replacing one module component inside that data with a common symbol could make unequal bodies share an ID while their runtime behavior still distinguishes the modules. Capture's current diagnostic searches only for `_private` or `_@` string literals ([Capture.lean](../impl/p1/Paralean/Capture.lean)); the three F13 export mismatches establish that this heuristic is incomplete, although the logs alone do not isolate every changed F13 subterm.

A minimal executable witness uses the same `register_simp_attr identity_simps` command in [IdentityOriginal.lean](../verification/fixtures/identity/IdentityOriginal.lean) and [IdentityRelocated.lean](../verification/fixtures/identity/IdentityRelocated.lean). On the fork at `99967f1` with `LEAN_PARALEAN=1`, `bash scripts/check-identity-fixture.sh .runs/w1/toolchains/fork-stage1/bin/lean` passes and prints these generated members and embedded string values:

```text
_private.verification.fixtures.identity.IdentityOriginal.0.initFn._@.verification.fixtures.identity.IdentityOriginal.1111279983._hygCtx._hyg.28: [IdentityOriginal]
_private.verification.fixtures.identity.IdentityOriginal.0.initFn._@.verification.fixtures.identity.IdentityOriginal.1111279983._hygCtx._hyg.5: [IdentityOriginal]
_private.verification.fixtures.identity.IdentityRelocated.0.initFn._@.verification.fixtures.identity.IdentityRelocated.1111279983._hygCtx._hyg.28: [IdentityRelocated]
_private.verification.fixtures.identity.IdentityRelocated.0.initFn._@.verification.fixtures.identity.IdentityRelocated.1111279983._hygCtx._hyg.5: [IdentityRelocated]
PASS: generated initializer literals differ with the Lean module
```

[InitializerIdentity.lean](../verification/veil/Paralean/InitializerIdentity.lean) proves the limited fact needed here: group-keyed rendering of a scoped declaration can remain equal across module relocation while its embedded private-name value changes; any quotient that identifies those two values fails to reflect exact observable equality. This is an abstract refinement of the name distinction, not a proof about all Lean elaborator expansions or cryptographic collision resistance. It does not exclude a semantics-specific normalization for a restricted metaprogram after separately proving that its name data cannot affect behavior.

[ReplayIdentity.tla](../verification/tla/ReplayIdentity.tla) models context selection before replay. A module-sensitive group is accepted in its original context and rejected in a synthetic context; an ordinary group is accepted in either. `AcceptedExact` independently checks the output against stored content. TLC explores 16 distinct states with no error; three witness runs establish the useful paths, and removing the exact acceptance guard produces an `AcceptedExact` counterexample. The model is finite and abstracts the actual group bytes and elaborator; it tests the protocol rule, not a claim that every original-context elaboration succeeds.

For groups checked by source replay, acceptance requires exact stored identity. Materialized initializer coverage is a separate existing mechanism for consumer effects; it does not prove byte-identical re-elaboration or exported literal-body identity. W1's targeted M08 replay now passes a cold `check-group` under the stored source module while retaining the exact group-ID comparison. That repairs the historic M08 source-replay failure documented in [m-targets-log.md](m-targets-log.md) for this targeted check; wider replay closures still need their own measurement. The 26 baseline G4 export mismatches remain outside an exact export-identity claim until exports are measured with identical IDs. The prior `1116/1142` result must not be reported as full export certification.
