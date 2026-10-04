#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p verification/results/tlc/negative verification/results/lean
for model in Chain Collision Revision Revert Rejected Quorums Integrated CheckpointReuse ExportRejected; do
  cp ".runs/tla/$model.log" "verification/results/tlc/$model.log"
done
for label in work dependent_work collision durable loss integrated_work checkpoint_reuse export_rejection_work \
  unchecked unknown_dependency unknown_ancestor unclosed_ancestors unprepared_publication unpublished_receive \
  unbuildable_commit unclosed_snapshot unexportable_snapshot stale_commit stale_recommit dependent_work_blocked \
  checkpoint_loss_blocked premature_ack no_fair_recovery no_fair_receive unbacked_publication staged_publication \
  unbacked_checkpoint silent_winner; do
  cp ".runs/tla/negative/$label/result.log" "verification/results/tlc/negative/$label.log"
done
for module in Registry Durability Convergence Composition EndToEnd Commit Groups Delivery DeliveryAlternatives Admission AdmissionExecution Recovery RecoveryAncestry RecoveryAdequacy PublicationDiscovery CompletionRecovery Protocol CompletionRecoveryExecution ProtocolExecution ProtocolGuardChecks Audit; do
  cp ".runs/veil/$module.log" "verification/results/lean/$module.log"
done
{
  java -version 2>&1
  sha256sum .deps/tla2tools.jar
  git -C .deps/veil rev-parse HEAD
  (cd .deps/veil && "$HOME/.elan/bin/lake" env lean --version)
} > verification/results/toolchain.txt
rg --files verification/tla verification/veil scripts verification/README.md \
  verification/PROTOCOL-OBLIGATIONS.md verification/TLA-GUARDS.md \
  -g '*.lean' -g '*.tla' -g '*.cfg' -g '*.md' -g '*.toml' -g 'lean-toolchain' -g '*.sh' -g '!._*' | LC_ALL=C sort |
  while IFS= read -r file; do sha256sum "$file"; done \
  > verification/results/source-sha256.txt
