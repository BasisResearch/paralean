import Paralean.Recovery

/-! General recovery adequacy. A surviving, complete, ready scan supplies an
actual generated enumerate/reconstruct/historical path for any committed record.
No writer authorization is gained by recovering the record. -/
namespace ParaleanRecovery
noncomputable section Adequacy
variable {node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum : Type}
  [DecidableEq node] [Inhabited node]
  [DecidableEq record] [Inhabited record]
  [DecidableEq workspace] [Inhabited workspace]
  [DecidableEq snapshot] [Inhabited snapshot]
  [DecidableEq decl] [Inhabited decl]
  [DecidableEq name] [Inhabited name]
  [DecidableEq token] [Inhabited token]
  [DecidableEq scan] [Inhabited scan]
  [DecidableEq replica] [Inhabited replica]
  [DecidableEq obj] [Inhabited obj]
  [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum]
attribute [local instance] Classical.propDecidable

local instance : delta% (reconstruct._veil_dec_type_0
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan)
  (χ := CanonicalRep record workspace snapshot decl name token scan)) :=
  fun _ _ _ => Classical.propDecidable _
local instance : delta% (reconstruct._veil_dec_type_1
  (record := record) (workspace := workspace) (snapshot := snapshot)
  (decl := decl) (name := name) (token := token) (scan := scan)
  (χ := CanonicalRep record workspace snapshot decl name token scan)) :=
  fun _ _ => Classical.propDecidable _

/-- Closure of committed records discharges the scan's causal-closure test. -/
theorem committed_admissible_from_physical_scan
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (s : CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (ha : CoupledAssumptions th) (hs : CoupledSafe th s)
    (q : readQuorum) (hq : ∀ r, th.base.storage.memberR r q = true → s.storage.live r = true)
    (v : scan) (hscan : PhysicalScan th s.storage q v) (hready : ReadyScan th s.storage v)
    (c : record) (hc : s.recovery.committed c = true) : admissible v c th.recovery s.recovery := by
  have available := physical_scan_ready_for_committed th s ha hs q hq v hscan hready
  have facts := hs.1.1 c hc
  refine ⟨(available c hc).1, (available c hc).2, facts.1, facts.2.2.1, ?_⟩
  intro p hp
  have pc := facts.2.2.2 p hp
  have pfacts := hs.1.1 p pc
  exact ⟨(available p pc).1, (available p pc).2, pfacts.1, pfacts.2.2.1⟩

theorem physical_enumeration_enabled_with_label
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (s : CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (ha : CoupledAssumptions th) (hs : CoupledSafe th s)
    (q : readQuorum) (hq : ∀ r, th.base.storage.memberR r q = true → s.storage.live r = true)
    (v : scan) (hscan : PhysicalScan th s.storage q v) (hready : ReadyScan th s.storage v) :
    ∃ rec', CoupledNext th s ⟨rec', s.storage⟩ ∧
      RecoveryNext th.recovery s.recovery (.enumerate v) rec' ∧
      rec'.scanned = true ∧ rec'.writer = s.recovery.writer ∧ rec'.fence = s.recovery.fence ∧
      (∀ c, rec'.known c = true ↔ admissible v c th.recovery s.recovery) := by
  let accepted := fun c => decide (admissible v c th.recovery s.recovery)
  let rec' : CanonicalState record workspace snapshot decl name token scan :=
    { s.recovery with
      known := accepted
      committed := fun c => s.recovery.committed c || accepted c
      durableAck := fun c => s.recovery.durableAck c || accepted c
      heads := fun _ => false
      scanned := true
      reconstructed := false
      conflict := false
      selected := false }
  have ht : RecoveryNext th.recovery s.recovery (.enumerate v) rec' := by
    have hc := physical_scan_ready_for_committed th s ha hs q hq v hscan hready
    simp only [RecoveryNext, Next, NextAct, enumerate.ext.derived_eq]
    dsimp [enumerate.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
      instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep, Veil.canonicalFieldRepresentation]
    refine ⟨hc, ?_⟩
    simp [rec', accepted, admissible, readFrom, instIsSubReaderOfRefl, buildable,
      Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set, Veil.FieldUpdatePat.match,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp]
  refine ⟨rec', ?_, ht, rfl, rfl, rfl, ?_⟩
  · apply CoupledNext.recovery (.enumerate v) (fun c epoch he => by cases he) _ ht
    intro v' hv c hc
    cases hv
    exact (hready c).1 hc
  · intro c
    simp [rec', accepted]

theorem reconstruction_enabled_for_known_record
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (s : CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (c : record) (hscan : s.recovery.scanned = true) (hk : s.recovery.known c = true) :
    ∃ s', CoupledNext th s s' ∧ RecoveryNext th.recovery s.recovery .reconstruct s'.recovery ∧ s'.recovery.reconstructed = true ∧ s'.recovery.known c = true ∧
      s'.recovery.writer = s.recovery.writer ∧ s'.recovery.fence = s.recovery.fence ∧ s'.storage = s.storage := by
  let rec' : CanonicalState record workspace snapshot decl name token scan :=
    { s.recovery with
      heads := fun c => decide (s.recovery.known c = true ∧
        ¬∃ d, s.recovery.known d = true ∧ th.recovery.ancestor d c = true)
      conflict := decide (∃ c d, s.recovery.known c = true ∧
        ¬(∃ e, s.recovery.known e = true ∧ th.recovery.ancestor e c = true) ∧
        s.recovery.known d = true ∧
        ¬(∃ e, s.recovery.known e = true ∧ th.recovery.ancestor e d = true) ∧ c ≠ d)
      reconstructed := true
      selected := false }
  have ht : RecoveryNext th.recovery s.recovery .reconstruct rec' := by
    simp only [RecoveryNext, Next, NextAct, reconstruct.ext.derived_eq]
    dsimp [reconstruct.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
      instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep, Veil.canonicalFieldRepresentation]
    refine ⟨hscan, ?_⟩
    simp [rec', Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp]
  exact ⟨⟨rec', s.storage⟩, CoupledNext.recovery .reconstruct
    (fun c epoch he => by cases he) (fun v he => by cases he) ht, ht,
    rfl, hk, rfl, rfl, rfl⟩

theorem historical_enabled_for_known_record
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (s : CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (c : record) (hr : s.recovery.reconstructed = true) (hk : s.recovery.known c = true) :
    ∃ s', CoupledNext th s s' ∧ RecoveryNext th.recovery s.recovery (.historical c) s'.recovery ∧ s'.recovery.selected = true ∧ s'.recovery.selectedRecord = c ∧
      s'.recovery.writer = s.recovery.writer ∧ s'.recovery.fence = s.recovery.fence ∧ s'.storage = s.storage := by
  let rec' : CanonicalState record workspace snapshot decl name token scan :=
    { s.recovery with selectedRecord := c, selected := true }
  have ht : RecoveryNext th.recovery s.recovery (.historical c) rec' := by
    simp only [RecoveryNext, Next, NextAct, historical.ext.derived_eq]
    dsimp [historical.ext.tr, getFrom, setIn, readFrom, Veil.FieldRepresentation.get,
      instIsSubStateOfRefl, instIsSubReaderOfRefl, canonicalFieldRep, Veil.canonicalFieldRepresentation]
    refine ⟨hr, hk, ?_⟩
    simp [rec', Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
      Veil.FieldUpdatePat.match, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.IteratedProd.patCmp]
  exact ⟨⟨rec', s.storage⟩, CoupledNext.recovery (.historical c)
    (fun c epoch he => by cases he) (fun v he => by cases he) ht, ht,
    rfl, rfl, rfl, rfl, rfl⟩

/-- Every committed historical checkpoint has a successful physical recovery path.
Conflict may remain visible. Recovery does not grant a writer lease. -/
theorem physical_historical_recovery_adequate
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (s : CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (ha : CoupledAssumptions th) (hs : CoupledSafe th s)
    (q : readQuorum) (hq : ∀ r, th.base.storage.memberR r q = true → s.storage.live r = true)
    (v : scan) (hscan : PhysicalScan th s.storage q v) (hready : ReadyScan th s.storage v)
    (c : record) (hc : s.recovery.committed c = true) :
    ∃ s₁ s₂ s₃, CoupledNext th s s₁ ∧ CoupledNext th s₁ s₂ ∧ CoupledNext th s₂ s₃ ∧
      RecoveryNext th.recovery s.recovery (.enumerate v) s₁.recovery ∧
      RecoveryNext th.recovery s₁.recovery .reconstruct s₂.recovery ∧
      RecoveryNext th.recovery s₂.recovery (.historical c) s₃.recovery ∧
      s₃.recovery.selected = true ∧ s₃.recovery.selectedRecord = c ∧
      s₃.recovery.writer = s.recovery.writer ∧ s₃.recovery.fence = s.recovery.fence ∧ s₃.storage = s.storage := by
  have hadm := committed_admissible_from_physical_scan th s ha hs q hq v hscan hready c hc
  obtain ⟨rec₁, ht₁, label₁, scanned, writer₁, fence₁, known₁⟩ :=
    physical_enumeration_enabled_with_label th s ha hs q hq v hscan hready
  let s₁ : CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum :=
    ⟨rec₁, s.storage⟩
  have hk : s₁.recovery.known c = true := (known₁ c).2 hadm
  obtain ⟨s₂, ht₂, label₂, reconstructed, known₂, writer₂, fence₂, disk₂⟩ :=
    reconstruction_enabled_for_known_record th s₁ c scanned hk
  obtain ⟨s₃, ht₃, label₃, selected, exactRecord, writer₃, fence₃, disk₃⟩ :=
    historical_enabled_for_known_record th s₂ c reconstructed known₂
  exact ⟨s₁, s₂, s₃, ht₁, ht₂, ht₃, label₁, label₂, label₃, selected, exactRecord,
    writer₃.trans (writer₂.trans writer₁), fence₃.trans (fence₂.trans fence₁), disk₃.trans disk₂⟩

/-- The recovery path extends any reachable prefix and retains durable copies. -/
theorem reachable_physical_historical_recovery
    (th : CoupledTheory node record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (s : CoupledState record workspace snapshot decl name token scan replica obj writeQuorum readQuorum)
    (ha : CoupledAssumptions th) (hr : CoupledReachable th s)
    (q : readQuorum) (hq : ∀ r, th.base.storage.memberR r q = true → s.storage.live r = true)
    (v : scan) (hscan : PhysicalScan th s.storage q v) (hready : ReadyScan th s.storage v)
    (c : record) (hc : s.recovery.committed c = true) :
    ∃ s', CoupledReachable th s' ∧ s'.recovery.selected = true ∧ s'.recovery.selectedRecord = c ∧
      s'.recovery.writer = s.recovery.writer ∧ s'.recovery.fence = s.recovery.fence ∧ s'.storage = s.storage ∧
      (∃ r, s'.storage.live r = true ∧ s'.storage.stored r (th.recordObject c) = true) ∧
      (∃ r, s'.storage.live r = true ∧ s'.storage.stored r (th.base.manifest (th.recovery.image c)) = true) ∧
      (∀ d, th.base.registry.contents (th.recovery.image c) d = true →
        ∃ r, s'.storage.live r = true ∧ s'.storage.stored r (th.base.payload d) = true) := by
  obtain ⟨s₁, s₂, s₃, ht₁, ht₂, ht₃, _, _, _, selected, exactRecord, writer, fence, disk⟩ :=
    physical_historical_recovery_adequate th s ha (coupled_reachable_safe th ha hr) q hq v hscan hready c hc
  have hr₃ := CoupledReachable.step (CoupledReachable.step (CoupledReachable.step hr ht₁) ht₂) ht₃
  have copies := coupled_selected_has_copies th ha hr₃ selected
  rw [exactRecord] at copies
  exact ⟨s₃, hr₃, selected, exactRecord, writer, fence, disk, copies⟩

end Adequacy
#print axioms physical_enumeration_enabled_with_label
#print axioms reachable_physical_historical_recovery
#print axioms committed_admissible_from_physical_scan
#print axioms reconstruction_enabled_for_known_record
#print axioms historical_enabled_for_known_record
#print axioms physical_historical_recovery_adequate
end ParaleanRecovery
