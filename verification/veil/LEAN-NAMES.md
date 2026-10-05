# Lean naming layer under group membership

`Paralean/LeanNames.lean` (namespace `ParaleanLeanNames`) refines `ParaleanGroups.member`. In the base model, `member g x` is an abstract immutable relation. This file builds it from real Lean names. It is a naming refinement, not a protocol behaviour, so it has no TLA model. No transition changes; only the meaning of `member` does.

## Lean facts the layer rests on (checked against Lean 4.34.1 sources)

- Reserved names are created lazily by the *consumer*. `registerReservedNamePredicate` / `registerReservedNameAction` cover `f.eq_<n>`, `f.eq_def`, `f.unfold` (`Meta/Eqns.lean`), `f.induct`, `f.fun_cases` (`Meta/Tactic/FunInd.lean`), match equations and congruence lemmas. The action calls `realizeConst base name`, which runs `addDecl` in the consumer's environment.
- Inductive and structure commands produce their auxiliaries *eagerly*: `casesOn`, `recOn`, `below`, `brecOn`, `noConfusion`, `injEq`/`inj`, `ctorIdx`, constructors, projections and `SizeOf` instances. One command therefore makes many `addDecl` calls, and users can name every one of these in source.
- Anonymous instances get a generated name such as `instFooNat`. Users reference it (`attribute [-instance] instFooNat`, `@instFooNat`, `unfold instFooNat`), so it is a public name. Stock Lean may append a `_1` suffix to avoid a clash, which makes the name depend on the environment.
- Private names are `_private.<Module>.0.x` (`mkPrivateNameCore`), so their spelling depends on the module path. Two groups' `private def aux` rendered into one file would be a duplicate declaration.

## Classification (trusted implementation input)

The classifier is part of the fork and is trusted. It is not proved to agree with Lean. It maps Lean name forms to classes as follows.

| Class | Lean name forms | Model constructor |
|---|---|---|
| Public | explicitly declared names (including constructors and fields written in source); auto-named instances `instFooNat`, named canonically from the instance type with no `_n` deduplication; eager auxiliaries `T.below`, `T.brecOn`, `T.casesOn`, `T.recOn`, `T.noConfusion`, `T.noConfusionType`, `T.c.injEq`, `T.c.inj`, `T.ctorIdx`, structure projections, constructors (`T.mk`), `SizeOf` instances and `T.c.sizeOf_spec` | `pub b` |
| Scoped | `_private.<m>.0.b`; compiler auxiliaries `f.proof_<n>`, `f.match_<n>`, `_aux*`, `f._unsafe_rec` | `priv m b`, `gen b` |
| Reserved | `f.eq_<n>`, `f.eq_def`, `f.unfold`, `f.induct`, `f.fun_cases`, match equations, congruence lemmas, and any other name accepted by a registered reserved-name predicate | `res base s` |

## Encoding

- `LeanName mod atom sfx` = `pub b | gen b | priv m b | res base s`, classified by `kind` as `pub`, `scoped` or `reserved base`.
- `Rendered group atom sfx` is the Lean name that both the workspace renderer and the exporter emit. `render g` keeps public names, sends `gen b ↦ gen g b` and `priv m b ↦ priv g b` (dropping the module and adding the producing group), and renders reserved names over the rendered base.
- `Capture` has `capture : command → group` and `produces : command → LeanName → Prop`, which holds every `addDecl` output of the command.
- `canon enc` maps `pub b ↦ some (enc b)` and every other name to `none`. `member C enc g x := ∃ c y, capture c = g ∧ produces c y ∧ canon enc y = some x`.
- Eager auxiliaries are public names `der b e` (base `b`, fixed suffix `e`). `DerivedClosed C der`: a command producing `der b e` also produces `b`.
- `namingTheory base C enc rev` fills a `ParaleanGroups.Theory` with this membership.

## Results

- `public_collision_iff`: with `enc` injective, `Conflict g h x` holds iff `g ≠ h` and both groups produce the same public name `pub b` with `enc b = x`.
- `scoped_render_distinct`: scoped names of distinct groups render to distinct names, and a scoped name never renders to a public name. Structural: it holds because `Rendered` keeps the group and the class in the constructor. The content is the contract that the implementation's spelling is injective.
- `render_clash_iff`, `render_clash_conflict`: unreserved outputs of two distinct groups render to the same Lean name (an "already declared" error in the working copy) iff they are the same public name, and then the groups have a canonical `Conflict`. So the collision check sees every duplicate declaration the renderer can cause.
- `derived_collision_iff`: under `DerivedClosed` and injective `enc`, two groups conflict on `der b e` iff they conflict on `b` and both produce `der b e`. Derived names add no collision beyond their base's. `derived_name_determines_base`: with `der` injective on `(base, suffix)`, a derived canonical name determines its base and suffix.
- `instance_anchor`, `instance_collision` (definitional): a command producing the canonical instance name `instName τ` makes its group a member of that name, so an instance-only command has a public anchor; two groups declaring `instance : Foo Nat` conflict on `instFooNat` (a duplicate instance).
- `aux_same_group`: every output of one command is held by the single group `capture c`.
- `relocation_invariant`: an exporter relocation `f : mod → mod` leaves `render`, `canon` and `member` unchanged.
- `realization_member_eq`, `realization_theory_eq`: adding consumer-realised `res` names to any command does not change `member` or the registry theory.
- `reserved_consumer_deterministic`: for a reserved name on a public base, two consumers holding the same buildable snapshot realise the same constant `R g b s`; realisation leaves `isHead`, `current`, `buildable` and `Conflict` unchanged.
- `naming_assumptions`: `valid_ancestry`, `empty_contents` and `empty_exportable` hold for `namingTheory` if `rev` is transitive per name, each valid group has a public output, and the base's empty snapshot is empty and exportable.
- `conflict_not_buildable`: a canonical conflict inside a snapshot makes it unbuildable.
- Instance (`Fin` types). Group 0 defines `foo`, `instance : Foo Nat`, `private def aux` and `proof_1`. Group 1 defines `bar`, an inductive `T` with `T.casesOn`, and its own `private def aux` and `proof_1` in the same module. Group 2 defines `foo` and `instance : Foo Nat`. Groups 0 and 1 realise `foo.eq_1`.
  - `inst_conflicts_exact`: the only conflicts are groups 0 and 2 on `instFooNat` and on `foo`.
  - `inst_classes`: the two `private aux` and `proof_1` are scoped, render to distinct names and give no conflict between groups 0 and 1; the duplicate instance renders to one name and is a conflict (via `instance_collision`); `T.casesOn` is public and conflict-free.
  - `inst_theory_eq`, `inst_assumptions`: the concrete theory is `namingTheory`.
  - `inst_reachable`, `inst_nonvacuous`: a `ParaleanGroups` trace publishes groups 0 and 1, commits the snapshot containing both, then publishes group 2; committing that snapshot is then blocked by `overlapping_heads_block_commit`.
- `naive_false_collision`: with raw membership (every produced Lean name), groups 0 and 1 collide on `proof_1`, on the private name and on `foo.eq_1`, so the snapshot the canonical layer commits is unbuildable.
- `addDecl_capture_splits`: capturing per `addDecl` puts one command's outputs into different groups.
- Axioms: only `propext`, `Classical.choice` and `Quot.sound`. Log: `verification/results/lean/LeanNames.log`.

## Implementation contract (assumed, not proved)

- Capture runs at command boundaries and records every `addDecl` the command performs, including nested `realizeConst` calls made while elaborating it.
- The classifier follows the table above and is trusted.
- Instance names are canonical: the fork derives the name of an anonymous instance from its type alone and never applies `_n` deduplication. A clash is reported as a collision instead.
- The workspace renderer and the exporter both spell `Rendered` injectively. Scoped spellings use a reserved prefix that carries the group ID (for example `_private.<groupId>.0.aux`) and never coincide with a public spelling. Source that refers to a group's own private or auxiliary name is rewritten to the rendered form.
- Reserved names are never published. Consumers and the validator re-realise them from the pinned base group and never trust a remote copy.

## Not established

- Agreement of the classifier with Lean's auto-declaration and reserved-name rules, and injectivity of the renderer's spelling, are interfaces, not theorems.
- Realisation is modelled as a function `R g b s`. Determinism is proved only for public bases resolved through a snapshot; reserved names over scoped bases are assumed to follow the rendered base.
- `DerivedClosed` fails for a hand-written `def T.casesOn` in a group without `T`. That name is still public and still collision-checked; only `derived_collision_iff` does not apply to it.
- A group whose outputs are all scoped or reserved has no canonical member and fails `valid g → ∃ x, member g x`. Every source command with a declaration or instance has a public output, so this arises only for commands that the classifier should reject.
- Instance names are not distinct by construction. Lean's auto-naming reads only head symbols of the instance type, so different types share a name: `Foo (∀ x : Nat, P x)` and `Foo (∀ s : String, Q s)` both become `instFooForall`. Without the `_n` suffix the two groups collide on a public name even though the instances differ. The renderer must use an injective instance-naming scheme (or require explicit instance names); the model assumes injectivity of the spelling (see the first bullet).
- Two instances for different but overlapping types (for example `Foo Nat` and `Foo α`) both remain in scope. Which one resolution picks is a semantic question outside naming.
