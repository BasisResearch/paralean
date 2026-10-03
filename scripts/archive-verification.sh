#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p verification/results/tlc/negative verification/results/lean
for model in Chain Collision Revision Revert Rejected Quorums Integrated; do
  cp ".runs/tla/$model.log" "verification/results/tlc/$model.log"
done
for label in work collision durable loss integrated_work unchecked premature_ack no_fair_recovery unbacked_publication unbacked_checkpoint silent_winner; do
  cp ".runs/tla/negative/$label/result.log" "verification/results/tlc/negative/$label.log"
done
for module in Registry Durability Convergence Composition EndToEnd Audit; do
  cp ".runs/veil/$module.log" "verification/results/lean/$module.log"
done
{
  java -version 2>&1
  sha256sum .deps/tla2tools.jar
  git -C .deps/veil rev-parse HEAD
  (cd .deps/veil && "$HOME/.elan/bin/lake" env lean --version)
} > verification/results/toolchain.txt
rg --files verification/tla verification/veil scripts \
  -g '*.lean' -g '*.tla' -g '*.cfg' -g '*.md' -g '*.toml' -g 'lean-toolchain' -g '*.sh' -g '!._*' | LC_ALL=C sort |
  while IFS= read -r file; do sha256sum "$file"; done \
  > verification/results/source-sha256.txt
