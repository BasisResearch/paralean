# Durability proof

`Paralean/Durability.lean` models `verification/tla/Durability.tla` in Veil.
The proof is universal over replica, object, write-quorum, and recovery-quorum
types. It uses no finite enumeration or quorum cardinal arithmetic.

## Assumptions

The immutable theory supplies `memberW`, `memberR`, and `meet`. For every write
quorum `w` and recovery quorum `q`, `meet w q` belongs to both. Quorum types are
inhabited. These are explicit parameters and hypotheses, not new Lean axioms.

`stored r o` means the bytes for object `o` are hash verified, validator accepted,
and durably persisted on replica `r`. The implementation must supply these
trusted interfaces:

- Hash verification binds the retrieved bytes to the requested object identity.
- Validator acceptance binds a receipt to those bytes and the applicable rule.
- Stable-write completion means the bytes survive volatile-process loss until a
  modeled permanent disk loss.

`Put` is the completion event for all three interfaces. Their implementations,
cryptographic soundness, filesystem durability, and receipt checking are outside
this proof. The model does not treat network delivery or volatile buffering as
storage. A production implementation must refine this event before the theorem
can establish its durability.

## Actions and TLA correspondence

| TLA | Veil | Effect |
| --- | --- | --- |
| `Init` | `after_init` / generated `Init` | No stored objects; all replicas live; no acknowledgments. |
| `Put(r,o)` | `Put r o` | Requires a live replica; adds one durable object. |
| `Ack(o,w)` | `Ack o w` | Requires every member of `w` live and storing `o`; records acknowledgment and witness. |
| `Lose(r)` | `Lose r` | Requires a surviving recovery quorum; removes `r` from live replicas and erases its stored objects. |
| `Next` | generated `Next` | Dispatches the same three actions. |

The initial witness is the default write quorum for every object. Instantiating
that default with TLA's arbitrary chosen write quorum reproduces its witness
initialization. Reacknowledgment may replace the witness only after checking
the full new live durable quorum.

Immutable membership and `meet` encode TLA's fixed quorum sets and `Meet` map.
For any finite TLA instance, these functions are its characteristic functions
and supplied intersection witness. The action guards and assignments then
coincide after interpreting Boolean relations as sets. This correspondence is
documented; no formal Lean-to-TLA translation theorem is claimed.

`Reachable` uses Veil's generated `Init` and `Next`, not a separately written
transition system. Its induction covers all finite prefixes. TLA stuttering
leaves the reached state unchanged and therefore preserves the same predicates.

## Proven results

- `initializer_preserves` and `Init_preserves`: initialization establishes both
  invariants.
- `Put_preserves`, `Ack_preserves`, `Lose_preserves`: each generated Veil action
  transition preserves both invariants.
- `Next_preserves`: generated `Next` preserves the invariants, using Veil's
  kernel-checked action-to-transition equality lemmas.
- `reachable_invariants`: every reached state satisfies `WitnessSurvives` and
  `FailureEnvelope`.
- `reachable_recoverable`: for every acknowledged object and every entirely
  live recovery quorum, its intersection with the object's write witness is a
  live replica storing the object.
- `reachable_noDataLoss`: every acknowledged object has at least one live
  durable copy.

`WitnessSurvives` tracks every live member of an acknowledged object's current
write witness. `FailureEnvelope` supplies a surviving recovery quorum. The
intersection assumption selects its live witness member. These premises derive
recoverability and no data loss; neither conclusion is an axiom or action guard.

The results are conditional on the failure envelope. They do not establish
progress, repair completion, deployment availability, or durability after all
recovery quorums have been destroyed.

## Proof validation

Checked with Lean `4.32.0` and Veil commit
`d05518f22076b8cc84fb2d2b74d196aa979bfe8f`. The source contains explicit
`#print axioms` audits for initialization, each action, transition closure, and
both reachable guarantees. Each audit reports only `propext`, `Classical.choice`,
and `Quot.sound`, Lean's standard axioms.

The proof does not use trusted SMT results, `sorry`, new theorem axioms, or unsafe
proof construction. `unveil` exposes Veil's generated transitions; ordinary Lean
proofs discharge their preservation obligations. The final theorems depend on
these generated semantics and bridge lemmas, so their axiom audits also cover
those dependencies.
