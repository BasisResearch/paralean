#!/usr/bin/env bash
# Local security regressions and mutations; no shared cluster or cache is touched.
# Cases whose target is `--test <file>` exercise FDB/S3 transactions: they need the
# caller's own P2 instance (PARALEAN_INSTANCE=<name> after impl/p2/scripts/up.sh) and refuse
# to run against the default cluster.
set -euo pipefail
cd "$(dirname "$0")/.."
source impl/p2/scripts/env.sh
root="$PWD"
out="${W2_MUTATION_OUT:-$root/results/w2/mutations}"
mkdir -p "$out"
cargo test --manifest-path impl/p2/Cargo.toml -j 4 -p paralean-store -p paralean-control -p paralean-validator-api --lib > "$out/baseline.log" 2>&1
cargo test --manifest-path impl/p2/Cargo.toml -j 4 -p s3-guard >> "$out/baseline.log" 2>&1
cargo test --manifest-path impl/p2/Cargo.toml -j 4 -p paralean-remote --bin plr >> "$out/baseline.log" 2>&1
python3 impl/p2/scripts/test-storage-boundary.py >> "$out/baseline.log" 2>&1
# FoundationDB's connection string is its only client credential: never commit one.
if git grep -nE 'paralean:[a-z0-9]+@[0-9]' -- results docs impl scripts; then
  echo "an FDB connection string is committed (redact it and treat that cluster as exposed)"; exit 1
fi
cases=(
 "paralean-store|mutate-public-key-file|sign::security_tests::private_key_file_replaces_public_inode_and_symlink|--lib"
 "paralean-store|mutate-weak-signature|sign::security_tests::weak_public_key_identity_signature_is_rejected|--lib"
 "paralean-store|mutate-key-debug|sign::security_tests::debug_does_not_disclose_role_seeds|--lib"
 "paralean-store|mutate-unbounded-pce|pce::tests::hostile_counts_are_bounded_before_container_allocation|--lib"
 "paralean-store|mutate-unbounded-s3-read|s3::security_tests::oversized_s3_body_is_rejected_before_hashing|--lib"
 "paralean-control|mutate-unbounded-rpc|server::tests::connection_admission_is_bounded_before_authentication|--lib"
 "paralean-control|mutate-no-rpc-deadline|server::tests::incomplete_frames_expire_and_release_admission|--lib"
 "paralean-validator-api|mutate-oversized-frame|rpc::tests::oversized_frame_is_rejected_without_waiting_for_body|--lib"
 "paralean-validator-api|mutate-unbound-rpc-peer|rpc::tests::request_signature_binds_server_key_and_service|--lib"
 "paralean-control|mutate-shared-rpc-pool|server::tests::long_authenticated_calls_cannot_lock_out_the_authority|--lib"
 "paralean-control|mutate-no-per-source-admission|server::tests::one_source_cannot_hold_every_handshake_slot|--lib"
 "paralean-control|mutate-unchecked-gid|p1::gid_tests::hostile_gid_cannot_escape_the_scratch_store|--lib"
 "paralean-control|mutate-shared-workdir|validator::completed_tests::validator_workdir_must_be_private_and_ours|--lib"
 "paralean-control|mutate-unbounded-poll-responses|controller::snapshot_tests::worker_chosen_poll_tokens_and_finished_work_do_not_grow_the_snapshot|--lib"
 "paralean-control|mutate-no-work-gc|controller::snapshot_tests::worker_chosen_poll_tokens_and_finished_work_do_not_grow_the_snapshot|--lib"
 "s3-guard|mutate-allow-delete|tests::encoded_and_unknown_mutations_are_denied|"
 "s3-guard|mutate-unbounded-body|tests::streamed_body_limit_is_enforced|"
 "s3-guard|mutate-allow-overwrite|tests::overwrites_copies_and_unaddressed_keys_are_denied|"
 "paralean-store|mutate-receive-no-cancel-check|cancelled_request_is_not_received_by_its_issuer|--test antientropy"
 "paralean-store|mutate-receive-no-dep-check|received_group_waits_for_job_dependencies_here|--test antientropy"
 "paralean-store|mutate-no-statement-pin-check|t1_requires_the_pinned_target_statement|--test guards"
 "paralean-ae-service|mutate-ae-unbounded-parts|endless_event_parts_are_capped_and_archived|--test network"
 "paralean-ae-service|mutate-ae-unbounded-objects|oversized_declared_objects_are_terminal_before_fetch|--test network"
 "paralean-ae-service|mutate-ae-unbounded-source|declared_objects_are_bounded_per_source|--test network"
 "paralean-store|mutate-unchecked-file-path|objects::tests::marker_and_tombstone_file_paths_follow_the_relative_path_rule|--lib"
 "paralean-remote|mutate-unchecked-pid|cache::tests::put_capsule_refuses_traversing_package_ids_and_mismatched_bytes|--bin plr"
 "paralean-remote|mutate-unchecked-capsule-id|cache::tests::put_capsule_refuses_traversing_package_ids_and_mismatched_bytes|--bin plr"
 "paralean-store|mutate-unchecked-publish-path|t1_refuses_a_marker_with_an_unsafe_file_path|--test file_paths"
)
if printf '%s\n' "${cases[@]}" | grep -q -- '|--test '; then
  if [ -z "${PARALEAN_INSTANCE:-}" ] || [ ! -f "${PARALEAN_FDB_CLUSTER:-}" ]; then
    echo "cluster cases need your own running instance: PARALEAN_INSTANCE=<name> (impl/p2/scripts/up.sh)" >&2
    exit 1
  fi
fi
for entry in "${cases[@]}"; do
  IFS='|' read -r package feature test target <<< "$entry"
  # Each verdict must name the test; a compiler or infrastructure failure is not a kill.
  if cargo test --manifest-path impl/p2/Cargo.toml -j 4 -p "$package" --features "$feature" $target "$test" -- --exact > "$out/$feature.log" 2>&1; then
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
    "private_secret_files": ('if st.st_uid != os.getuid() or stat.S_IMODE(st.st_mode) & 0o077:', 'if False:'),
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
total=$((${#cases[@]} + 3))
echo "W2 security mutations: $total/$total detected"
