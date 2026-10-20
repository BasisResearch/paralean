#!/usr/bin/env bash
# Local security regressions and mutations; no shared cluster or cache is touched.
set -euo pipefail
cd "$(dirname "$0")/.."
source impl/p2/scripts/env.sh
root="$PWD"
out="$root/results/w2/mutations"
mkdir -p "$out"
cargo test --manifest-path impl/p2/Cargo.toml -j 1 -p paralean-store -p paralean-control -p paralean-validator-api --lib > "$out/baseline.log" 2>&1
cargo test --manifest-path impl/p2/Cargo.toml -j 1 -p s3-guard >> "$out/baseline.log" 2>&1
python3 impl/p2/scripts/test-storage-boundary.py >> "$out/baseline.log" 2>&1
cases=(
 "paralean-store|mutate-public-key-file|sign::security_tests::private_key_file_replaces_public_inode_and_symlink|--lib"
 "paralean-store|mutate-weak-signature|sign::security_tests::weak_public_key_identity_signature_is_rejected|--lib"
 "paralean-store|mutate-key-debug|sign::security_tests::debug_does_not_disclose_role_seeds|--lib"
 "paralean-store|mutate-unbounded-pce|pce::tests::hostile_counts_are_bounded_before_container_allocation|--lib"
 "paralean-store|mutate-unbounded-s3-read|s3::security_tests::oversized_s3_body_is_rejected_before_hashing|--lib"
 "paralean-control|mutate-unbounded-rpc|server::tests::connection_admission_is_bounded_before_authentication|--lib"
 "paralean-control|mutate-no-rpc-deadline|server::tests::incomplete_frames_expire_and_release_admission|--lib"
 "paralean-validator-api|mutate-oversized-frame|rpc::tests::oversized_frame_is_rejected_without_waiting_for_body|--lib"
 "s3-guard|mutate-allow-delete|tests::encoded_and_unknown_mutations_are_denied|"
 "s3-guard|mutate-unbounded-body|tests::streamed_body_limit_is_enforced|"
)
for entry in "${cases[@]}"; do
  IFS='|' read -r package feature test target <<< "$entry"
  # Each verdict must name the test; a compiler or infrastructure failure is not a kill.
  if cargo test --manifest-path impl/p2/Cargo.toml -j 1 -p "$package" --features "$feature" $target "$test" -- --exact > "$out/$feature.log" 2>&1; then
    echo "SURVIVED $feature"; exit 1
  fi
  if ! grep -Fq "test $test ... FAILED" "$out/$feature.log"; then
    echo "ERROR $feature"; tail -30 "$out/$feature.log"; exit 1
  fi
  echo "detected $feature"
done
python3 - "$out" <<'PY'
from pathlib import Path
import shutil, subprocess, sys, tempfile
source = Path("impl/p2/scripts")
text = (source / "check-storage-boundary.py").read_text()
mutations = {
    "private_backend_mode": ('if parent.st_uid != os.getuid() or stat.S_IMODE(parent.st_mode) & 0o077:', 'if False:'),
    "private_backend_tcp": ('raise ValueError("direct Garage TCP port is reachable; restart this instance")', 'return'),
}
for name, (old, new) in mutations.items():
    assert text.count(old) == 1
    with tempfile.TemporaryDirectory(prefix="w2-boundary-mutation-") as tmp:
        dest = Path(tmp)
        (dest / "check-storage-boundary.py").write_text(text.replace(old, new))
        shutil.copyfile(source / "test-storage-boundary.py", dest / "test-storage-boundary.py")
        result = subprocess.run([sys.executable, str(dest / "test-storage-boundary.py")], capture_output=True, text=True)
        (Path(sys.argv[1]) / (name + ".log")).write_text(result.stdout + result.stderr)
        assert result.returncode != 0 and "AssertionError: ValueError not raised" in result.stderr, result.stderr
        print("detected", name)
PY
echo "W2 security mutations: 12/12 detected"
