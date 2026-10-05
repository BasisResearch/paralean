import Paralean
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let prefixes := #[`ParaleanRegistry, `Durability, `ParaleanConvergence, `ParaleanComposition,
    `ParaleanGroups, `ParaleanGroupComposition, `ParaleanDelivery, `ParaleanArtifacts,
    `ParaleanAdmission, `ParaleanRecovery, `ParaleanPublicationDiscovery,
    `ParaleanCompletionRecovery, `ParaleanProtocol, `ParaleanProtocolGuardChecks,
    `ParaleanLeanNames, `ParaleanPublicationReceipts, `ParaleanTargetNames,
    `ParaleanCatalogFencing, `ParaleanAckCertificates, `ParaleanCatalogCertificates, `ParaleanHardened, `ParaleanWorkspaces]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  -- Private declarations are named `_private.<module>.0.<name>`; match the user name.
  let userName (name : Name) : Name := (privateToUserName? name).getD name
  for (name, _) in env.constants.toList do
    if prefixes.any (·.isPrefixOf (userName name)) then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      count := count + 1
  unless count > 0 do
    throwError "Axiom audit found no project declarations"
  for namespaceName in prefixes do
    unless env.constants.toList.any (fun (name, _) => namespaceName.isPrefixOf (userName name)) do
      throwError "Axiom audit missing required namespace: {namespaceName}"
  logInfo m!"PASS: {count} project declarations use only the permitted stock Lean axioms"
