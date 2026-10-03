import Veil

/-! Replicated storage abstraction corresponding to verification/tla/Durability.tla.
`stored r o` denotes hash-verified, validator-accepted bytes that completed a
stable write on replica r. The hash, validator, and stable-write implementations
are trusted refinement interfaces. Put is their durable completion event.
No state theorem is assumed. All preservation and reachability results below
are kernel-checked against Veil-generated transition predicates.
-/

veil module Durability

type replica
type obj
type writeQuorum
type readQuorum
immutable relation memberW : replica → writeQuorum → Bool
immutable relation memberR : replica → readQuorum → Bool
immutable function meet : writeQuorum → readQuorum → replica
relation stored : replica → obj → Bool
relation live : replica → Bool
relation acknowledged : obj → Bool
function witness : obj → writeQuorum
#gen_state
assumption ∀ (w : writeQuorum) (q : readQuorum), memberW (meet w q) w ∧ memberR (meet w q) q

after_init {
  stored R O := false
  live R := true
  acknowledged O := false
  witness O := (default : writeQuorum)
}
action Put (r : replica) (o : obj) {
  require live r
  stored r o := true
}
action Ack (o : obj) (w : writeQuorum) {
  require ∀ (r : replica), memberW r w → live r ∧ stored r o
  acknowledged o := true
  witness o := w
}
action Lose (r : replica) {
  require live r
  require ∃ (q : readQuorum), ∀ (n : replica), memberR n q → live n ∧ n ≠ r
  live r := false
  stored r O := false
}
invariant [WitnessSurvives] ∀ (o : obj) (r : replica), acknowledged o → memberW r (witness o) → live r → stored r o
invariant [FailureEnvelope] ∃ (q : readQuorum), ∀ (r : replica), memberR r q → live r
#gen_spec
section Proofs
variable (ρ σ replica obj writeQuorum readQuorum : Type)
variable [DecidableEq replica] [Inhabited replica]
variable [DecidableEq obj] [Inhabited obj]
variable [DecidableEq writeQuorum] [Inhabited writeQuorum]
variable [DecidableEq readQuorum] [Inhabited readQuorum]
variable (χ : State.Label → Type)
variable [χ_rep : ∀ f, Veil.FieldRepresentation
  (State.Label.toDomain replica obj writeQuorum readQuorum f)
  (State.Label.toCodomain replica obj writeQuorum readQuorum f) (χ f)]
variable [∀ f, Veil.LawfulFieldRepresentation
  (State.Label.toDomain replica obj writeQuorum readQuorum f)
  (State.Label.toCodomain replica obj writeQuorum readQuorum f) (χ f) (χ_rep f)]
variable [IsSubStateOf (State χ) σ]
variable [IsSubReaderOf (Theory replica obj writeQuorum readQuorum) ρ]
variable [Ack_dec_0 : delta% @Ack._veil_dec_type_0 obj writeQuorum replica readQuorum χ χ_rep]
variable [Lose_dec_0 : delta% @Lose._veil_dec_type_0 replica obj writeQuorum readQuorum χ χ_rep]

omit Ack_dec_0 Lose_dec_0 in
theorem Put_preserves (r : replica) (o : obj) :
  Veil.Transition.meetsSpecificationIfSuccessfulAssuming
    (Put.ext.tr ρ σ replica obj writeQuorum readQuorum χ r o)
    (Assumptions ρ replica obj writeQuorum readQuorum)
    (Invariants ρ σ replica obj writeQuorum readQuorum χ)
    (Invariants ρ σ replica obj writeQuorum readQuorum χ) := by
  unveil
  constructor
  · grind
  · obtain ⟨q, hq⟩ := hinv.2
    refine ⟨q, ?_⟩
    intro n hn
    grind

omit Lose_dec_0 in
theorem Ack_preserves (o : obj) (w : writeQuorum) :
  Veil.Transition.meetsSpecificationIfSuccessfulAssuming
    (Ack.ext.tr ρ σ replica obj writeQuorum readQuorum χ o w)
    (Assumptions ρ replica obj writeQuorum readQuorum)
    (Invariants ρ σ replica obj writeQuorum readQuorum χ)
    (Invariants ρ σ replica obj writeQuorum readQuorum χ) := by
  unveil
  constructor
  · grind
  · obtain ⟨q, hq⟩ := hinv.2
    refine ⟨q, ?_⟩
    intro n hn
    grind

omit Ack_dec_0 in
theorem Lose_preserves (r : replica) :
  Veil.Transition.meetsSpecificationIfSuccessfulAssuming
    (Lose.ext.tr ρ σ replica obj writeQuorum readQuorum χ r)
    (Assumptions ρ replica obj writeQuorum readQuorum)
    (Invariants ρ σ replica obj writeQuorum readQuorum χ)
    (Invariants ρ σ replica obj writeQuorum readQuorum χ) := by
  unveil
  constructor
  · grind
  · obtain ⟨q, hq⟩ := htr.2.1
    refine ⟨q, ?_⟩
    intro n hn
    grind

omit Ack_dec_0 Lose_dec_0 in
theorem initializer_preserves :
  Veil.Transition.meetsSpecificationIfSuccessfulAssuming
    (initializer.ext.tr ρ σ replica obj writeQuorum readQuorum χ)
    (Assumptions ρ replica obj writeQuorum readQuorum)
    (fun _ _ => True)
    (Invariants ρ σ replica obj writeQuorum readQuorum χ) := by
  unveil
  constructor
  · grind
  · exact ⟨default, fun r _ => htr.2.1 r⟩

variable [Inhabited σ]

omit Ack_dec_0 Lose_dec_0 in
theorem Init_preserves (rd : ρ) (st : σ)
    (has : Assumptions ρ replica obj writeQuorum readQuorum rd)
    (hi : Init ρ σ replica obj writeQuorum readQuorum χ rd st) :
    Invariants ρ σ replica obj writeQuorum readQuorum χ rd st :=
  initializer_preserves ρ σ replica obj writeQuorum readQuorum χ rd default st
    ⟨has, trivial⟩ hi

omit [Inhabited σ] in
theorem Next_preserves (rd : ρ) (st st' : σ)
    (label : Label replica obj writeQuorum readQuorum)
    (has : Assumptions ρ replica obj writeQuorum readQuorum rd)
    (hinv : Invariants ρ σ replica obj writeQuorum readQuorum χ rd st)
    (hstep : Next ρ σ replica obj writeQuorum readQuorum χ rd st label st') :
    Invariants ρ σ replica obj writeQuorum readQuorum χ rd st' := by
  cases label <;> simp only [Next, NextAct, Put.ext.derived_eq,
    Ack.ext.derived_eq, Lose.ext.derived_eq] at hstep
  case Put r o =>
    exact Put_preserves ρ σ replica obj writeQuorum readQuorum χ r o
      rd st st' ⟨has, hinv⟩ hstep
  case Ack o w =>
    exact Ack_preserves ρ σ replica obj writeQuorum readQuorum χ o w
      rd st st' ⟨has, hinv⟩ hstep
  case Lose r =>
    exact Lose_preserves ρ σ replica obj writeQuorum readQuorum χ r
      rd st st' ⟨has, hinv⟩ hstep

/-- Finite prefixes of the generated Veil Init/Next semantics. Stuttering is
already represented by leaving the prefix unchanged. -/
inductive Reachable (rd : ρ) : σ → Prop where
  | initial {st : σ} : Init ρ σ replica obj writeQuorum readQuorum χ rd st → Reachable rd st
  | step {st st' : σ} : Reachable rd st →
      (label : Label replica obj writeQuorum readQuorum) →
      Next ρ σ replica obj writeQuorum readQuorum χ rd st label st' → Reachable rd st'

theorem reachable_invariants (rd : ρ) (st : σ)
    (has : Assumptions ρ replica obj writeQuorum readQuorum rd)
    (hr : Reachable ρ σ replica obj writeQuorum readQuorum χ rd st) :
    Invariants ρ σ replica obj writeQuorum readQuorum χ rd st := by
  induction hr with
  | initial hi => exact Init_preserves ρ σ replica obj writeQuorum readQuorum χ _ _ has hi
  | step hr label hstep ih =>
    exact Next_preserves ρ σ replica obj writeQuorum readQuorum χ _ _ _ label has ih hstep

/-- Every surviving recovery quorum contains a live durable copy, at meet. -/
def Recoverable (rd : ρ) (st : σ) : Prop :=
  let th : Theory replica obj writeQuorum readQuorum := readFrom rd
  let s : State χ := getFrom st
  let ack : obj → Bool := @Veil.FieldRepresentation.get [obj] Bool (χ .acknowledged) (χ_rep .acknowledged) s.acknowledged
  let witness : obj → writeQuorum := @Veil.FieldRepresentation.get [obj] writeQuorum (χ .witness) (χ_rep .witness) s.witness
  let live : replica → Bool := @Veil.FieldRepresentation.get [replica] Bool (χ .live) (χ_rep .live) s.live
  let stored : replica → obj → Bool := @Veil.FieldRepresentation.get [replica, obj] Bool (χ .stored) (χ_rep .stored) s.stored
  ∀ o q, ack o = true → (∀ n, th.memberR n q = true → live n = true) →
    live (th.meet (witness o) q) = true ∧ stored (th.meet (witness o) q) o = true

def NoDataLoss (st : σ) : Prop :=
  let s : State χ := getFrom st
  let ack : obj → Bool := @Veil.FieldRepresentation.get [obj] Bool (χ .acknowledged) (χ_rep .acknowledged) s.acknowledged
  let live : replica → Bool := @Veil.FieldRepresentation.get [replica] Bool (χ .live) (χ_rep .live) s.live
  let stored : replica → obj → Bool := @Veil.FieldRepresentation.get [replica, obj] Bool (χ .stored) (χ_rep .stored) s.stored
  ∀ o, ack o = true → ∃ n, live n = true ∧ stored n o = true

omit Ack_dec_0 Lose_dec_0 [Inhabited σ] in
theorem invariants_recoverable (rd : ρ) (st : σ)
    (has : Assumptions ρ replica obj writeQuorum readQuorum rd)
    (hinv : Invariants ρ σ replica obj writeQuorum readQuorum χ rd st) :
    Recoverable ρ σ replica obj writeQuorum readQuorum χ rd st := by
  cases ht : (readFrom rd : Theory replica obj writeQuorum readQuorum)
  cases hs : (getFrom st : State χ)
  rename_i memberW memberR meet stored live acknowledged witness
  simp only [Assumptions, assumption_0, Invariants, WitnessSurvives, FailureEnvelope,
    Recoverable, ht, hs] at *
  intro o q ha hq
  have hm := has ((@Veil.FieldRepresentation.get [obj] writeQuorum (χ .witness) (χ_rep .witness) witness) o) q
  have hl := hq _ hm.2
  exact ⟨hl, hinv.1 o _ ha hm.1 hl⟩

omit Ack_dec_0 Lose_dec_0 [Inhabited σ] in
theorem invariants_noDataLoss (rd : ρ) (st : σ)
    (has : Assumptions ρ replica obj writeQuorum readQuorum rd)
    (hinv : Invariants ρ σ replica obj writeQuorum readQuorum χ rd st) :
    NoDataLoss σ replica obj writeQuorum readQuorum χ st := by
  have hrecover := invariants_recoverable ρ σ replica obj writeQuorum readQuorum χ rd st has hinv
  cases ht : (readFrom rd : Theory replica obj writeQuorum readQuorum)
  cases hs : (getFrom st : State χ)
  simp only [Invariants, WitnessSurvives, FailureEnvelope, Recoverable, NoDataLoss, ht, hs] at *
  intro o ha
  obtain ⟨q, hq⟩ := hinv.2
  exact ⟨_, hrecover o q ha hq⟩

theorem reachable_recoverable (rd : ρ) (st : σ)
    (has : Assumptions ρ replica obj writeQuorum readQuorum rd)
    (hr : Reachable ρ σ replica obj writeQuorum readQuorum χ rd st) :
    Recoverable ρ σ replica obj writeQuorum readQuorum χ rd st :=
  invariants_recoverable ρ σ replica obj writeQuorum readQuorum χ rd st has
    (reachable_invariants ρ σ replica obj writeQuorum readQuorum χ rd st has hr)

theorem reachable_noDataLoss (rd : ρ) (st : σ)
    (has : Assumptions ρ replica obj writeQuorum readQuorum rd)
    (hr : Reachable ρ σ replica obj writeQuorum readQuorum χ rd st) :
    NoDataLoss σ replica obj writeQuorum readQuorum χ st :=
  invariants_noDataLoss ρ σ replica obj writeQuorum readQuorum χ rd st has
    (reachable_invariants ρ σ replica obj writeQuorum readQuorum χ rd st has hr)

end Proofs
#print axioms Put_preserves
#print axioms Ack_preserves
#print axioms Lose_preserves
#print axioms Init_preserves
#print axioms Next_preserves
#print axioms reachable_invariants
#print axioms reachable_recoverable
#print axioms reachable_noDataLoss
end Durability
