#!/usr/bin/env bash
# Strict Ed25519 acceptance on every verifying path, with one guard-removal mutation
# per path that the path's own strict-vector regression must detect. Integration
# tests use a private cluster: PARALEAN_INSTANCE=w2-<name> (impl/p2/scripts/up.sh).
set -euo pipefail
cd "$(dirname "$0")/.."
[[ "${PARALEAN_INSTANCE:-}" =~ ^w2[a-z]?-[A-Za-z0-9_-]+$ ]] || { echo 'set PARALEAN_INSTANCE=w2-<name> (or w2b-, w2c-)' >&2; exit 2; }
source impl/p2/scripts/env.sh
out=results/w2/ed25519
rm -rf "$out"; mkdir -p "$out"
# path | package | mutation feature | test target | test name
cases=(
  'point-encoding|paralean-crypto|mutate-noncanonical-point|--test vectors|point_encoding_is_canonical'
  'store-verifier|paralean-store|mutate-weak-signature|--test strict_signatures|store_strict_signature_vectors'
  't1-receipt|paralean-store|mutate-relaxed-receipt-sig|--test strict_signatures|t1_publication_strict_receipt_signature_vectors'
  'ae-tombstone-import|paralean-store|mutate-relaxed-import-sig|--test strict_signatures|antientropy_import_strict_signature_vectors'
  'ae-group-import|paralean-store|mutate-relaxed-import-sig|--test strict_signatures|antientropy_group_import_strict_signature_vectors'
  'ae-transport|ae-wire|mutate-weak-signature|--lib|tests::transport_strict_signature_vectors'
  'validator-envelope|paralean-control|mutate-relaxed-envelope-sig|--test strict_signatures|validator_envelope_strict_signature_vectors'
  'rpc-auth|paralean-validator-api|mutate-relaxed-rpc-sig|--test strict_signatures|validator_rpc_strict_signature_vectors'
  # Paths merged from origin/main: W3's agent-key registry and controller deletion, and
  # W4's sharded controller endpoints (the RPC verifier at each shard's real challenge).
  'agent-key-grant|paralean-store|mutate-relaxed-agent-grant-sig|--test strict_signatures|agent_key_grant_strict_signature_vectors'
  'agent-key-revocation|paralean-store|mutate-relaxed-agent-revocation-sig|--test strict_signatures|agent_key_revocation_strict_signature_vectors'
  'controller-delete-grant|paralean-store|mutate-relaxed-controller-delete-sig|--test strict_signatures|controller_delete_grant_strict_signature_vectors'
  'sharded-controller-rpc|paralean-control|paralean-validator-api/mutate-relaxed-rpc-sig|--test strict_signatures|sharded_controller_rpc_strict_signature_vectors'
)
detected=0
for entry in "${cases[@]}"; do
  IFS='|' read -r path package feature target test <<< "$entry"
  # shellcheck disable=SC2086
  if ! cargo test --manifest-path impl/p2/Cargo.toml -j 4 -p "$package" $target "$test" -- --exact \
      > "$out/$path.log" 2>&1 || ! grep -Eq "test[[:space:]]+$test[[:space:]]+\.\.\. ok" "$out/$path.log"; then
    echo "BASELINE FAILED $path"; tail -20 "$out/$path.log"; exit 1
  fi
  # shellcheck disable=SC2086
  if cargo test --manifest-path impl/p2/Cargo.toml -j 4 -p "$package" --features "$feature" $target "$test" -- --exact \
      > "$out/$path-mutation.log" 2>&1; then
    echo "SURVIVED $path ($feature)"; exit 1
  fi
  # A compile or infrastructure failure is not a kill: the named test must fail.
  # libtest-mimic suites pad the name column, so match the verdict line by pattern.
  grep -Eq "test[[:space:]]+$test[[:space:]]+\.\.\. FAILED" "$out/$path-mutation.log" || { echo "ERROR $path"; tail -20 "$out/$path-mutation.log"; exit 1; }
  echo "$path: strict regression passed; $feature detected by $test"
  detected=$((detected + 1))
done
echo "Rust Ed25519 path mutations: $detected/${#cases[@]} detected"
python3 impl/p1/tests/check_security_mutations.py
