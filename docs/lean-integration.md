# Lean integration investigation

Source inspected: Lean nightly `193c3589a4fc16c4059261ab38cfa365eb24f323`
(`nightly-2026-10-03`). Mathlib nightly commit
`0575336843263378752eeb5f4c75a612327768a2` specifies that toolchain; upstream
build/test CI passed. [Mathlib toolchain](https://github.com/leanprover-community/mathlib4-nightly-testing/blob/0575336843263378752eeb5f4c75a612327768a2/lean-toolchain),
[CI evidence](https://github.com/leanprover-community/mathlib4-nightly-testing/actions/runs/37115079169).
No full local Mathlib build or distributed fork is claimed in this delivery.

## Existing boundaries

`Lean.addDecl` already separates asynchronous elaboration from checked kernel
environments. `addConstAsync` can expose a signature before its kernel task has
finished. `Environment.toKernelEnv` forces the checked representation. The sharing
hook must wait for successful checked completion, not merely signature publication.
[Environment implementation](https://github.com/leanprover/lean4-nightly/blob/193c3589a4fc16c4059261ab38cfa365eb24f323/src/Lean/Environment.lean#L30),
[declaration insertion](https://github.com/leanprover/lean4-nightly/blob/193c3589a4fc16c4059261ab38cfa365eb24f323/src/Lean/AddDecl.lean#L101).

Kernel insertion checks free variables, metavariables and duplicate names. Thus
complete declaration groups are a useful context-free transport boundary. Their
expressions still contain bound variables and universe parameters. Distinct
versions of one name cannot coexist in an ordinary kernel environment.
[Kernel environment](https://github.com/leanprover/lean4-nightly/blob/193c3589a4fc16c4059261ab38cfa365eb24f323/src/kernel/environment.cpp#L86).

The elaboration environment additionally contains persistent extensions, visibility
information and asynchronous state. Serialized kernel declarations alone do not
reconstruct notation, attributes, instances, tactics or source-level name lookup.
Capture that separately; do not attempt to send live `Task` values or pointers.
[Environment extensions](https://github.com/leanprover/lean4-nightly/blob/193c3589a4fc16c4059261ab38cfa365eb24f323/src/Lean/Environment.lean).

## When bodies are needed

Ordinary constant type inference reads its type and instantiates universe parameters.
It does not recursively replay every referenced proof. Definitional equality may
unfold definitions, so type-only dependency identity is unsound. At this pin,
`constant_info::has_value` includes theorems and definitions, and the delta path
uses it. Do not promise that theorem bodies are never inspected.
[Constant inference and delta reduction](https://github.com/leanprover/lean4-nightly/blob/193c3589a4fc16c4059261ab38cfa365eb24f323/src/kernel/type_checker.cpp#L101),
[constant values](https://github.com/leanprover/lean4-nightly/blob/193c3589a4fc16c4059261ab38cfa365eb24f323/src/kernel/declaration.h#L446).

Bodies are also needed to validate the producer's declaration, audit transitive
axioms, reconstruct fresh environments and export a standalone project. Normal
theorem-use checking can reuse an already validated environment. Signatures may
travel first, but authenticated bodies must remain retrievable.

V1 fetches missing declaration packages before kernel checking and materializes
a compatible environment locally. Independent declarations check on different
machines. Large storage chunks can live elsewhere without adding a new `Expr`
constructor or changing Lean's logic. This is fine-grained distributed admission;
it does not distribute every recursive kernel traversal across the network.

Demand-loading inside the kernel would require a defined provider interface,
failure/cancellation behavior, caching and referentially stable environment lookup
across C++ and Lean. `ConstantInfo` currently contains actual values. A missing
body is not a valid substitute for a definition. Consider that invasive change
only after prefetch/memory measurements demonstrate a need.

## Scoped changes

| Area / inspected source | Proposed change | Kernel-trust impact |
|---|---|---|
| `src/Lean/AddDecl.lean`: `addDecl`, `addAndCompile`, internal `addDeclCore` | Capture completed commands (all `addDecl` calls of one command, including nested `realizeConst`) as one group; defer publication until checked tasks succeed | Preserve existing checks |
| `Lean/ReservedNameAction.lean`, `Meta/Basic.lean` `realizeConst`, `Lean/PrivateName.lean`, `Lean/AutoDecl.lean`, instance naming in `Elab/DeclUtil` | Classify names; drop reserved realizations from published membership and re-realize them from the pinned base; key private and compiler-auxiliary names by group, not module; name instances canonically and injectively without `_n` dedup; disable matcher/aux-lemma reuse across groups | Realizations re-checked by the kernel |
| `src/Lean/Environment.lean`: `addConstAsync`, `addDeclCore`, `toKernelEnv`, extensions | Pin dependency maps; reconstruct environments; record compatible frontend manifests | No unchecked remote insertion |
| New `Lean/Distributed/Artifact`, `Registry`, `Admission` modules | Canonical encoding, exact IDs, version conflicts, receipts and job envelopes | Validate untrusted input at boundary |
| Frontend command processing / name resolution | Materialize discovered dependencies at snapshot boundaries; invalidate suffixes after rebasing | Exact ordinary constants reach kernel |
| `src/Lean/Language/Lean.lean` and command snapshot handling | Include environment identity in reuse keys | Prevent stale elaboration reuse |
| `src/Lean/Server/Watchdog.lean`, `FileWorker.lean` | Route document sessions; aggregate symbols; map URIs; filter stale responses | No proof acceptance authority |
| `src/Lean/Server/Rpc` and session code | Preserve session affinity/generation for remote RPC references | Avoid treating pointers as global IDs |
| New exporter plus Lake integration | Replay source capsules, regenerate acyclic imports, clean stock build | Stock build validates portability |
| Separate validator executable | Reconstruct trusted dependency environment, enforce axiom and target policies | Explicit additional trusted service |
| `addConstAsync` path and command snapshot completion | Keep local asynchronous elaboration; the capture hook waits for every kernel task of the command before staging. Validation and export run synchronously | No other worker sees a statement before its proof is kernel-checked |
| C++ kernel `environment.cpp`, `type_checker.cpp`, `declaration.h` | No semantic edits for v1; regression tests and profiling | Keep base kernel behavior |

This is a thin frontend/runtime fork plus services, not a new proof calculus.
One command emits many kernel declarations, and reserved constants appear lazily
in consumers via `realizeConst`. Package boundaries are therefore elaborated
commands. Collision checks apply to public names, which include auto-named
instances and eager auxiliaries. Private and compiler-auxiliary names are scoped
to their group; the renderer and exporter rename them to group-unique names.
Reserved names are re-derived, never transported. See
[Lean names](../verification/veil/LEAN-NAMES.md).

## Validation policy and comparator

`debug.skipKernelTC` explicitly selects unchecked insertion in `AddDecl.lean`.
Disabling one option in a worker is insufficient: metaprograms execute arbitrary
code, `.olean` files are trusted imports, and the kernel permits axioms. Run a
separate validator with fixed trusted imports and options, then inspect the actual
checked dependency closure. [Proof validation guidance](https://lean-lang.org/doc/reference/latest/ValidatingProofs/),
[skip-check path](https://github.com/leanprover/lean4-nightly/blob/193c3589a4fc16c4059261ab38cfa365eb24f323/src/Lean/AddDecl.lean#L22).

Reject new user axioms and `sorryAx`. Explicitly allow only the project's audited
baseline axioms, commonly `propext`, `Classical.choice`, and `Quot.sound`. Reject
unsafe proof dependencies and policy bypasses. Compare fixed target types together
with the meanings of constants they reference; matching printed statements alone
does not prevent changing an upstream definition.

Modern Lean module export can represent theorem interfaces as axiom-shaped public
metadata while retaining checked implementation evidence. Therefore a blanket
“reject every `axiomInfo` encountered” rule would reject ordinary trusted imports.
Follow original declaration kind, checked provenance and transitive evidence. Never
promote an arbitrary remote signature into the trusted baseline.
[Module visibility handling](https://github.com/leanprover/lean4-nightly/blob/193c3589a4fc16c4059261ab38cfa365eb24f323/src/Lean/AddDecl.lean#L113).

Lean's comparator provides a useful independent final-validation pattern, including
environment comparison, allowed axioms and sandboxing. Pin and test a compatible
comparator/exporter revision before integrating it; current compatibility with the
selected nightly is an implementation gate. Do not silently substitute its fake
sandbox mode. [Comparator documentation](https://github.com/leanprover/comparator).

## Distributed LSP and ordinary source

The current server has a watchdog and per-file workers. Workers perform elaboration
and hold snapshot/InfoTree state. Imported module changes can require restarting a
worker because compacted imported regions cannot safely be swapped in place.
Reuse this isolation model with remote transport; do not make the index process
responsible for every proof state. [Server architecture](https://github.com/leanprover/lean4-nightly/blob/193c3589a4fc16c4059261ab38cfa365eb24f323/src/Lean/Server/README.md).

Watchdog already aggregates workspace symbols and routes requests. Extend those
paths with immutable workspace/environment identity and worker generation. Keep
request cancellation, document version, URI mapping and RPC lifetime semantics.
[Watchdog implementation](https://github.com/leanprover/lean4-nightly/blob/193c3589a4fc16c4059261ab38cfa365eb24f323/src/Lean/Server/Watchdog.lean#L1174).

Lake rejects cyclic module/build dependencies. Declaration graphs can still be
acyclic while agent-file imports cycle. The exporter must split/reorder generated
files, and verify frontend command ordering as well as kernel dependencies.
[Module cycle guard](https://github.com/leanprover/lean4-nightly/blob/193c3589a4fc16c4059261ab38cfa365eb24f323/src/lake/Lake/Build/Module.lean#L197).

## Existing experiments

`experiments/KernelBoundary.lean` ran on unmodified local Lean 4.34.1. It confirms
same type/different body invalidation, retained old environments, and that kernel
acceptance alone does not enforce a target contract or prohibit axioms.
`ProofGraph.lean` tests AND/OR scheduling behavior. Its open task metadata is not
the declaration admission protocol. These are boundary experiments, not benchmarks
or evidence that the selected nightly fork has been implemented.
