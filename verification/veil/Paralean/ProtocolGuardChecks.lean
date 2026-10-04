import Paralean.CompletionRecovery
import Paralean.PublicationDiscovery

/-! Guard regressions. Original component actions remain enabled in each bad
case; the strengthened operation rejects the missing durable evidence. -/
namespace ParaleanProtocolGuardChecks
noncomputable section
variable {node group name snapshot request packet record workspace token scan replica writeQuorum readQuorum : Type}
  [DecidableEq node] [Inhabited node] [DecidableEq group] [Inhabited group]
  [DecidableEq name] [Inhabited name] [DecidableEq snapshot] [Inhabited snapshot]
  [DecidableEq request] [Inhabited request] [DecidableEq packet] [Inhabited packet]
  [DecidableEq record] [Inhabited record] [DecidableEq workspace] [Inhabited workspace]
  [DecidableEq token] [Inhabited token] [DecidableEq scan] [Inhabited scan]
  [DecidableEq replica] [Inhabited replica] [DecidableEq writeQuorum] [Inhabited writeQuorum]
  [DecidableEq readQuorum] [Inhabited readQuorum]

/-- Removing the catalogue guard admits the supplied real delivery/commit step. -/
theorem missing_catalogue_guard_regression
    (a : ParaleanAdmission.Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (r : ParaleanRecovery.Theory record workspace snapshot group name token scan)
    (ad ad' : ParaleanAdmission.State node group name snapshot request packet replica writeQuorum readQuorum)
    (rec : ParaleanRecovery.CanonicalState record workspace snapshot group name token scan)
    (n : node) (S : snapshot) (c : record)
    (original : ParaleanAdmission.FinishStep a n S ad ad')
    (missing : rec.committed c = false) :
    ParaleanAdmission.FinishStep a n S ad ad' ∧
      ¬∃ after, ParaleanCompletionRecovery.FinishStep a r n S c ⟨ad, rec⟩ after := by
  refine ⟨original, ?_⟩
  rintro ⟨after, strengthened⟩
  cases strengthened with
  | guarded _ committed _ _ => simp [missing] at committed

/-- A durable record for another image cannot certify this completion. -/
theorem mismatched_image_guard_regression
    (a : ParaleanAdmission.Theory node group name snapshot request packet replica writeQuorum readQuorum)
    (r : ParaleanRecovery.Theory record workspace snapshot group name token scan)
    (ad ad' : ParaleanAdmission.State node group name snapshot request packet replica writeQuorum readQuorum)
    (rec : ParaleanRecovery.CanonicalState record workspace snapshot group name token scan)
    (n : node) (S : snapshot) (c : record)
    (original : ParaleanAdmission.FinishStep a n S ad ad') (mismatch : r.image c ≠ S) :
    ParaleanAdmission.FinishStep a n S ad ad' ∧
      ¬∃ after, ParaleanCompletionRecovery.FinishStep a r n S c ⟨ad, rec⟩ after := by
  refine ⟨original, ?_⟩
  rintro ⟨after, strengthened⟩
  cases strengthened with
  | guarded _ _ image _ => exact mismatch image

/-- The original registry can receive an ID whose discovery marker is absent.
The strengthened receive guard cannot supply a physical scan of that ID. -/
theorem absent_publication_marker_guard_regression
    (th : ParaleanPublicationDiscovery.Theory node group name snapshot replica writeQuorum readQuorum)
    (s : ParaleanPublicationDiscovery.State node group name snapshot replica writeQuorum readQuorum)
    (n : node) (d : group)
    (alive : s.registry.alive n = true) (online : s.registry.online n = true)
    (published : s.registry.published d = true) (missing : s.registry.known n d ≠ true)
    (absent : ∀ r, s.storage.stored r (.publication d) = false) :
    (∃ rg', ParaleanGroups.ReceiveStep th.registry s.registry rg' n d) ∧
      ¬∃ q ids, ParaleanPublicationDiscovery.PhysicalScan th s.storage q ids ∧
        ids d ∧ s.storage.acknowledged (.publication d) = true := by
  refine ⟨(ParaleanGroups.receive_enabled_iff th.registry s.registry n d).2
    ⟨alive, online, published, missing⟩, ?_⟩
  rintro ⟨q, ids, scan, present, _⟩
  obtain ⟨replica, _, _, stored⟩ := (scan d).1 present
  simp [absent replica] at stored

end
#print axioms missing_catalogue_guard_regression
#print axioms mismatched_image_guard_regression
#print axioms absent_publication_marker_guard_regression
end ParaleanProtocolGuardChecks
