#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p verification/results/tlc/negative verification/results/lean
for model in Chain Collision Revision Revert Rejected Quorums Integrated CheckpointReuse ExportRejected Receipts Targets Fencing Certificates Workspace; do
  cp ".runs/tla/$model.log" "verification/results/tlc/$model.log"
done
# Archive every negative case the suite ran; drop logs of retired cases.
rm -f verification/results/tlc/negative/*.log
for dir in .runs/tla/negative/*/; do
  label="$(basename "$dir")"
  cp "$dir/result.log" "verification/results/tlc/negative/$label.log"
done
for module in Registry Durability Convergence Composition EndToEnd Commit Groups Delivery DeliveryAlternatives Admission AdmissionExecution Recovery RecoveryAncestry RecoveryAdequacy PublicationDiscovery CompletionRecovery Protocol CompletionRecoveryExecution ProtocolExecution ProtocolGuardChecks LeanNames PublicationReceipts TargetNames CatalogFencing AckCertificates CatalogCertificates Hardened HardenedExecution Workspaces Audit; do
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
