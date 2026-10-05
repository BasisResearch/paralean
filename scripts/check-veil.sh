#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
root="$PWD"
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p .runs/veil/Paralean
expected=d05518f22076b8cc84fb2d2b74d196aa979bfe8f
[[ "$(git -C .deps/veil rev-parse HEAD)" == "$expected" ]]
git -C .deps/veil diff --quiet
git -C .deps/veil diff --cached --quiet
cd .deps/veil
# Resolve the dependency environment once. Put freshly checked project objects
# first even if the caller has an older project build on LEAN_PATH.
dependency_path="$(lake env printenv LEAN_PATH)"
lean_binary="$(lake env which lean)"
export LEAN_PATH="$root/.runs/veil:$dependency_path"
for module in Registry Durability Convergence Composition EndToEnd Commit Groups Delivery DeliveryAlternatives Admission AdmissionExecution Recovery RecoveryAncestry RecoveryAdequacy PublicationDiscovery CompletionRecovery Protocol CompletionRecoveryExecution ProtocolExecution ProtocolGuardChecks LeanNames PublicationReceipts TargetNames CatalogFencing AckCertificates CatalogCertificates Hardened HardenedExecution Workspaces; do
  echo "Checking $module"
  "$lean_binary" -R "$root/verification/veil" -o "$root/.runs/veil/Paralean/$module.olean" \
    "$root/verification/veil/Paralean/$module.lean" \
    > "$root/.runs/veil/$module.log" 2>&1
  cat "$root/.runs/veil/$module.log"
done
"$lean_binary" -R "$root/verification/veil" -o "$root/.runs/veil/Paralean.olean" \
  "$root/verification/veil/Paralean.lean"
"$lean_binary" -R "$root/verification/veil" "$root/verification/veil/Audit.lean" \
  > "$root/.runs/veil/Audit.log" 2>&1
cat "$root/.runs/veil/Audit.log"
