import Paralean.Registry
import Paralean.Durability

/-! Guarded composition of the generated Registry and Durability transitions.
Publication and checkpoint advancement require acknowledgments in the storage
component. Storage transitions leave registry state unchanged. -/
namespace ParaleanComposition

abbrev DiskRep (replica obj writeQuorum readQuorum : Type) (f : Durability.State.Label) :=
  Veil.CanonicalField (Durability.State.Label.toDomain replica obj writeQuorum readQuorum f)
    (Durability.State.Label.toCodomain replica obj writeQuorum readQuorum f)

abbrev DiskState (replica obj writeQuorum readQuorum : Type) :=
  Durability.State (DiskRep replica obj writeQuorum readQuorum)

structure Theory (node decl name snapshot replica obj writeQuorum readQuorum : Type) where
  registry : ParaleanRegistry.Theory node decl name snapshot
  storage : Durability.Theory replica obj writeQuorum readQuorum
  payload : decl → obj
  manifest : snapshot → obj

structure State (node decl name snapshot replica obj writeQuorum readQuorum : Type) where
  registry : ParaleanRegistry.CanonicalState node decl name snapshot
  storage : DiskState replica obj writeQuorum readQuorum

noncomputable section Proofs
variable {node decl name snapshot replica obj writeQuorum readQuorum : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq decl] [Inhabited decl]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]
  [DecidableEq replica] [Inhabited replica] [DecidableEq obj] [Inhabited obj]
  [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum]

@[reducible] instance diskFieldRep : ∀ f, Veil.FieldRepresentation
    (Durability.State.Label.toDomain replica obj writeQuorum readQuorum f)
    (Durability.State.Label.toCodomain replica obj writeQuorum readQuorum f)
    (DiskRep replica obj writeQuorum readQuorum f) := by
  intro f
  cases f <;> (apply Veil.canonicalFieldRepresentation; infer_instance_for_iterated_prod)

instance diskFieldRepLawful : ∀ f, Veil.LawfulFieldRepresentation
    (Durability.State.Label.toDomain replica obj writeQuorum readQuorum f)
    (Durability.State.Label.toCodomain replica obj writeQuorum readQuorum f)
    (DiskRep replica obj writeQuorum readQuorum f) (diskFieldRep f) := by
  intro f
  cases f <;> apply Veil.canonicalFieldRepresentationLawful

instance diskStateInhabited : Inhabited (DiskState replica obj writeQuorum readQuorum) :=
  ⟨⟨fun _ _ => false, fun _ => true, fun _ => false, fun _ => default⟩⟩

local instance : delta% @Durability.Ack._veil_dec_type_0 obj writeQuorum replica readQuorum
    (DiskRep replica obj writeQuorum readQuorum) diskFieldRep :=
  fun _ _ _ _ => Classical.propDecidable _
local instance : delta% @Durability.Lose._veil_dec_type_0 replica obj writeQuorum readQuorum
    (DiskRep replica obj writeQuorum readQuorum) diskFieldRep :=
  fun _ _ _ => Classical.propDecidable _

abbrev StorageInit := Durability.Init (Durability.Theory replica obj writeQuorum readQuorum)
  (DiskState replica obj writeQuorum readQuorum) replica obj writeQuorum readQuorum
  (DiskRep replica obj writeQuorum readQuorum)
abbrev StorageNext := Durability.Next (Durability.Theory replica obj writeQuorum readQuorum)
  (DiskState replica obj writeQuorum readQuorum) replica obj writeQuorum readQuorum
  (DiskRep replica obj writeQuorum readQuorum)
abbrev StorageSafe := Durability.Invariants (Durability.Theory replica obj writeQuorum readQuorum)
  (DiskState replica obj writeQuorum readQuorum) replica obj writeQuorum readQuorum
  (DiskRep replica obj writeQuorum readQuorum)
abbrev StorageAssumptions := Durability.Assumptions (Durability.Theory replica obj writeQuorum readQuorum)
  replica obj writeQuorum readQuorum

def Assumptions (th : Theory node decl name snapshot replica obj writeQuorum readQuorum) : Prop :=
  ParaleanRegistry.TheoryAssumptions th.registry ∧ StorageAssumptions th.storage

/-- The baseline empty checkpoint has no stored manifest obligation. -/
def Coupled (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (rg : ParaleanRegistry.CanonicalState node decl name snapshot)
    (disk : DiskState replica obj writeQuorum readQuorum) : Prop :=
  (∀ d, rg.published d = true → disk.acknowledged (th.payload d) = true) ∧
  (∀ n, rg.head n ≠ th.registry.emptySnapshot → disk.acknowledged (th.manifest (rg.head n)) = true)

def Guard (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (disk : DiskState replica obj writeQuorum readQuorum) :
    ParaleanRegistry.Label node decl name snapshot → Prop
  | .publish _ d => disk.acknowledged (th.payload d) = true
  | .commit _ S => disk.acknowledged (th.manifest S) = true
  | _ => True

def Init (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (s : State node decl name snapshot replica obj writeQuorum readQuorum) : Prop :=
  ParaleanRegistry.RegistryInit th.registry s.registry ∧ StorageInit th.storage s.storage

inductive Next (th : Theory node decl name snapshot replica obj writeQuorum readQuorum) :
    State node decl name snapshot replica obj writeQuorum readQuorum →
    State node decl name snapshot replica obj writeQuorum readQuorum → Prop where
  | registry {rg rg' disk} (label : ParaleanRegistry.Label node decl name snapshot) :
      ParaleanRegistry.RegistryNext th.registry rg label rg' → Guard th disk label →
      Next th ⟨rg, disk⟩ ⟨rg', disk⟩
  | storage {rg disk disk'} (label : Durability.Label replica obj writeQuorum readQuorum) :
      StorageNext th.storage disk label disk' → Next th ⟨rg, disk⟩ ⟨rg, disk'⟩
  | stutter {s} : Next th s s

def Safe (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (s : State node decl name snapshot replica obj writeQuorum readQuorum) : Prop :=
  ParaleanRegistry.Safe th.registry s.registry ∧
    StorageSafe th.storage s.storage ∧ Coupled th s.registry s.storage

theorem storage_acknowledged_mono (th : Durability.Theory replica obj writeQuorum readQuorum)
    (s s' : DiskState replica obj writeQuorum readQuorum)
    (label : Durability.Label replica obj writeQuorum readQuorum)
    (ht : StorageNext th s label s') :
    ∀ o, s.acknowledged o = true → s'.acknowledged o = true := by
  cases label <;>
    simp only [StorageNext, Durability.Next, Durability.NextAct,
      Durability.Put.ext.derived_eq, Durability.Ack.ext.derived_eq,
      Durability.Lose.ext.derived_eq] at ht
  all_goals
    dsimp [Durability.Put.ext.tr, Durability.Ack.ext.tr, Durability.Lose.ext.tr,
      getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
      instIsSubStateOfRefl, instIsSubReaderOfRefl, diskFieldRep,
      Veil.canonicalFieldRepresentation] at ht
    repeat' rcases ht with ⟨ha, ht⟩
    try subst s'
    simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp]
    try grind

omit [DecidableEq replica] [Inhabited replica] [DecidableEq obj] [Inhabited obj]
  [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum] in
theorem registry_preserves_coupling
    (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (rg rg' : ParaleanRegistry.CanonicalState node decl name snapshot)
    (disk : DiskState replica obj writeQuorum readQuorum)
    (label : ParaleanRegistry.Label node decl name snapshot)
    (hc : Coupled th rg disk) (hg : Guard th disk label)
    (ht : ParaleanRegistry.RegistryNext th.registry rg label rg') : Coupled th rg' disk := by
  cases label <;>
    simp only [ParaleanRegistry.RegistryNext, ParaleanRegistry.Next, ParaleanRegistry.NextAct,
      ParaleanRegistry.prepare.ext.derived_eq, ParaleanRegistry.publish.ext.derived_eq,
      ParaleanRegistry.receive.ext.derived_eq, ParaleanRegistry.commit.ext.derived_eq,
      ParaleanRegistry.crash.ext.derived_eq, ParaleanRegistry.recover.ext.derived_eq,
      ParaleanRegistry.partition.ext.derived_eq, ParaleanRegistry.reconnect.ext.derived_eq,
      ParaleanRegistry.heal.ext.derived_eq] at ht
  all_goals
    dsimp [ParaleanRegistry.prepare.ext.tr, ParaleanRegistry.publish.ext.tr,
      ParaleanRegistry.receive.ext.tr, ParaleanRegistry.commit.ext.tr,
      ParaleanRegistry.crash.ext.tr, ParaleanRegistry.recover.ext.tr,
      ParaleanRegistry.partition.ext.tr, ParaleanRegistry.reconnect.ext.tr,
      ParaleanRegistry.heal.ext.tr, getFrom, setIn, readFrom,
      Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
      ParaleanRegistry.canonicalFieldRep, Veil.canonicalFieldRepresentation] at ht
    try split_ifs at ht
    all_goals
      repeat' rcases ht with ⟨ha, ht⟩
      try subst rg'
      simp only [Coupled, Guard] at *
      simp [Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
        Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
        Veil.IteratedProd.patCmp] at *
      grind

omit [DecidableEq replica] [Inhabited replica] [DecidableEq obj] [Inhabited obj]
  [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum] in
theorem initial_coupled
    (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (rg : ParaleanRegistry.CanonicalState node decl name snapshot)
    (disk : DiskState replica obj writeQuorum readQuorum)
    (ht : ParaleanRegistry.RegistryInit th.registry rg) : Coupled th rg disk := by
  dsimp [ParaleanRegistry.RegistryInit, ParaleanRegistry.Init,
    ParaleanRegistry.initializer.ext.tr, getFrom, setIn, readFrom,
    Veil.FieldRepresentation.get, instIsSubStateOfRefl, instIsSubReaderOfRefl,
    ParaleanRegistry.canonicalFieldRep, Veil.canonicalFieldRepresentation] at ht
  subst rg
  simp [Coupled, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
    Veil.IteratedProd.patCmp]

theorem initial_safe
    (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (ha : Assumptions th)
    (s : State node decl name snapshot replica obj writeQuorum readQuorum)
    (ht : Init th s) : Safe th s := by
  exact ⟨ParaleanRegistry.initial_safe th.registry s.registry ha.1 ht.1,
    Durability.Init_preserves _ _ replica obj writeQuorum readQuorum
      (DiskRep replica obj writeQuorum readQuorum) th.storage s.storage ha.2 ht.2,
    initial_coupled th s.registry s.storage ht.1⟩

theorem next_safe
    (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (ha : Assumptions th)
    (s s' : State node decl name snapshot replica obj writeQuorum readQuorum)
    (hs : Safe th s) (ht : Next th s s') : Safe th s' := by
  cases ht with
  | registry label ht hg =>
    exact ⟨ParaleanRegistry.next_safe th.registry _ _ label ha.1 hs.1 ht,
      hs.2.1, registry_preserves_coupling th _ _ _ label hs.2.2 hg ht⟩
  | storage label ht =>
    refine ⟨hs.1,
      Durability.Next_preserves _ _ replica obj writeQuorum readQuorum
        (DiskRep replica obj writeQuorum readQuorum) th.storage _ _ label ha.2 hs.2.1 ht,
      ?_⟩
    have hm := storage_acknowledged_mono th.storage _ _ label ht
    exact ⟨fun d hd => hm _ (hs.2.2.1 d hd), fun n hn => hm _ (hs.2.2.2 n hn)⟩
  | stutter => exact hs

inductive Reachable (th : Theory node decl name snapshot replica obj writeQuorum readQuorum) :
    State node decl name snapshot replica obj writeQuorum readQuorum → Prop where
  | initial {s} : Init th s → Reachable th s
  | step {s s'} : Reachable th s → Next th s s' → Reachable th s'

theorem reachable_safe
    (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (ha : Assumptions th)
    {s : State node decl name snapshot replica obj writeQuorum readQuorum}
    (hr : Reachable th s) : Safe th s := by
  induction hr with
  | initial hi => exact initial_safe th ha _ hi
  | step hr ht ih => exact next_safe th ha _ _ ih ht

omit [DecidableEq node] [Inhabited node] [DecidableEq decl] [Inhabited decl]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot] in
theorem acknowledged_recoverable
    (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (disk : DiskState replica obj writeQuorum readQuorum)
    (ha : StorageAssumptions th.storage) (hs : StorageSafe th.storage disk)
    (o : obj) (q : readQuorum) (hack : disk.acknowledged o = true)
    (hq : ∀ r, th.storage.memberR r q = true → disk.live r = true) :
    disk.live (th.storage.meet (disk.witness o) q) = true ∧
      disk.stored (th.storage.meet (disk.witness o) q) o = true := by
  have hrec := Durability.invariants_recoverable
    (Durability.Theory replica obj writeQuorum readQuorum)
    (DiskState replica obj writeQuorum readQuorum) replica obj writeQuorum readQuorum
    (DiskRep replica obj writeQuorum readQuorum) th.storage disk ha hs
  dsimp [Durability.Recoverable, getFrom, readFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, diskFieldRep,
    Veil.canonicalFieldRepresentation] at hrec
  exact hrec o q hack hq

omit [DecidableEq node] [Inhabited node] [DecidableEq decl] [Inhabited decl]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot] in
theorem acknowledged_has_copy
    (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (disk : DiskState replica obj writeQuorum readQuorum)
    (ha : StorageAssumptions th.storage) (hs : StorageSafe th.storage disk)
    (o : obj) (hack : disk.acknowledged o = true) :
    ∃ r, disk.live r = true ∧ disk.stored r o = true := by
  have hcopy := Durability.invariants_noDataLoss
    (Durability.Theory replica obj writeQuorum readQuorum)
    (DiskState replica obj writeQuorum readQuorum) replica obj writeQuorum readQuorum
    (DiskRep replica obj writeQuorum readQuorum) th.storage disk ha hs
  dsimp [Durability.NoDataLoss, getFrom, Veil.FieldRepresentation.get,
    instIsSubStateOfRefl, diskFieldRep, Veil.canonicalFieldRepresentation] at hcopy
  exact hcopy o hack

theorem published_recoverable
    (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (ha : Assumptions th)
    {s : State node decl name snapshot replica obj writeQuorum readQuorum}
    (hr : Reachable th s) (d : decl) (hp : s.registry.published d = true)
    (q : readQuorum) (hq : ∀ r, th.storage.memberR r q = true → s.storage.live r = true) :
    s.storage.live (th.storage.meet (s.storage.witness (th.payload d)) q) = true ∧
      s.storage.stored (th.storage.meet (s.storage.witness (th.payload d)) q) (th.payload d) = true := by
  have hs := reachable_safe th ha hr
  exact acknowledged_recoverable th s.storage ha.2 hs.2.1 _ q (hs.2.2.1 d hp) hq

theorem published_has_copy
    (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (ha : Assumptions th)
    {s : State node decl name snapshot replica obj writeQuorum readQuorum}
    (hr : Reachable th s) (d : decl) (hp : s.registry.published d = true) :
    ∃ r, s.storage.live r = true ∧ s.storage.stored r (th.payload d) = true := by
  have hs := reachable_safe th ha hr
  exact acknowledged_has_copy th s.storage ha.2 hs.2.1 _ (hs.2.2.1 d hp)

theorem checkpoint_manifest_recoverable
    (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (ha : Assumptions th)
    {s : State node decl name snapshot replica obj writeQuorum readQuorum}
    (hr : Reachable th s) (n : node) (hne : s.registry.head n ≠ th.registry.emptySnapshot)
    (q : readQuorum) (hq : ∀ r, th.storage.memberR r q = true → s.storage.live r = true) :
    s.storage.live (th.storage.meet (s.storage.witness (th.manifest (s.registry.head n))) q) = true ∧
      s.storage.stored (th.storage.meet (s.storage.witness (th.manifest (s.registry.head n))) q)
        (th.manifest (s.registry.head n)) = true := by
  have hs := reachable_safe th ha hr
  exact acknowledged_recoverable th s.storage ha.2 hs.2.1 _ q (hs.2.2.2 n hne) hq

theorem checkpoint_manifest_has_copy
    (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (ha : Assumptions th)
    {s : State node decl name snapshot replica obj writeQuorum readQuorum}
    (hr : Reachable th s) (n : node) (hne : s.registry.head n ≠ th.registry.emptySnapshot) :
    ∃ r, s.storage.live r = true ∧ s.storage.stored r (th.manifest (s.registry.head n)) = true := by
  have hs := reachable_safe th ha hr
  exact acknowledged_has_copy th s.storage ha.2 hs.2.1 _ (hs.2.2.2 n hne)

theorem checkpoint_declaration_recoverable
    (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (ha : Assumptions th)
    {s : State node decl name snapshot replica obj writeQuorum readQuorum}
    (hr : Reachable th s) (n : node) (d : decl)
    (hd : th.registry.contents (s.registry.head n) d = true)
    (q : readQuorum) (hq : ∀ r, th.storage.memberR r q = true → s.storage.live r = true) :
    s.storage.live (th.storage.meet (s.storage.witness (th.payload d)) q) = true ∧
      s.storage.stored (th.storage.meet (s.storage.witness (th.payload d)) q) (th.payload d) = true := by
  have hs := reachable_safe th ha hr
  exact published_recoverable th ha hr d (hs.1.2.2.2.2.2.1 n d hd) q hq

theorem checkpoint_declaration_has_copy
    (th : Theory node decl name snapshot replica obj writeQuorum readQuorum)
    (ha : Assumptions th)
    {s : State node decl name snapshot replica obj writeQuorum readQuorum}
    (hr : Reachable th s) (n : node) (d : decl)
    (hd : th.registry.contents (s.registry.head n) d = true) :
    ∃ r, s.storage.live r = true ∧ s.storage.stored r (th.payload d) = true := by
  have hs := reachable_safe th ha hr
  exact published_has_copy th ha hr d (hs.1.2.2.2.2.2.1 n d hd)

end Proofs
#print axioms storage_acknowledged_mono
#print axioms registry_preserves_coupling
#print axioms initial_coupled
#print axioms initial_safe
#print axioms next_safe
#print axioms reachable_safe
#print axioms published_recoverable
#print axioms published_has_copy
#print axioms checkpoint_manifest_recoverable
#print axioms checkpoint_manifest_has_copy
#print axioms checkpoint_declaration_recoverable
#print axioms checkpoint_declaration_has_copy
end ParaleanComposition
