#!/usr/bin/env bash
# Strict verification in shared store/RPC paths, anti-entropy transport and Lean.
set -euo pipefail
cd "$(dirname "$0")/.."
source impl/p2/scripts/env.sh
mkdir -p results/w2/ed25519
for entry in \
  'paralean-store|sign::security_tests::weak_public_key_identity_signature_is_rejected' \
  'ae-wire|tests::weak_pinned_peer_key_is_rejected'; do
  IFS='|' read -r package test <<< "$entry"
  cargo test --manifest-path impl/p2/Cargo.toml -j 1 -p "$package" --lib "$test" -- --exact \
    > "results/w2/ed25519/$package.log" 2>&1
  if cargo test --manifest-path impl/p2/Cargo.toml -j 1 -p "$package" --features mutate-weak-signature --lib "$test" -- --exact \
      > "results/w2/ed25519/$package-mutation.log" 2>&1; then
    echo "SURVIVED $package strict verification"; exit 1
  fi
  grep -Fq "test $test ... FAILED" "results/w2/ed25519/$package-mutation.log"
  echo "$package: strict verification regression passed, mutation detected"
done
python3 impl/p1/tests/check_security_mutations.py
