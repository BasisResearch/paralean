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
python3 impl/p3-remote/scripts/test-ws.py >> "$out/baseline.log" 2>&1
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
 "paralean-control|mutate-role-keys-unchecked|keys::tests::roles_refuse_key_files_with_other_roles_seeds|--lib"
 "paralean-control|mutate-unchecked-gid|p1::gid_tests::hostile_gid_cannot_escape_the_scratch_store|--lib"
 "paralean-control|mutate-shared-workdir|validator::completed_tests::validator_workdir_must_be_private_and_ours|--lib"
 "paralean-control|mutate-unbounded-poll-responses|controller::snapshot_tests::worker_chosen_poll_tokens_and_finished_work_do_not_grow_the_snapshot|--lib"
 "paralean-control|mutate-no-work-gc|controller::snapshot_tests::worker_chosen_poll_tokens_and_finished_work_do_not_grow_the_snapshot|--lib"
 "s3-guard|mutate-allow-delete|tests::encoded_and_unknown_mutations_are_denied|"
 "s3-guard|mutate-unbounded-body|tests::streamed_body_limit_is_enforced|"
 "s3-guard|mutate-allow-overwrite|tests::overwrites_copies_and_unaddressed_keys_are_denied|"
 "s3-guard|mutate-no-per-source-admission|tests::one_source_cannot_hold_every_connection_slot|"
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
 # Merged W4 controller shards: W2-32 scoping of the validation catalog, W2-33's bound
 # ahead of shard routing.
 "paralean-control|mutate-unscoped-job-keys|sharded_validation_routes_are_scoped_per_workspace|--test durable"
 "paralean-control|mutate-unbounded-poll-responses|overlong_request_id_is_refused_before_shard_routing|--test durable"
 # W2-33's spill keeps W4's replay invariant: a dropped poll token resolves to its first answer.
 "paralean-control|mutate-history-omit-poll-marker|spilled_poll_tokens_keep_their_first_answer|--test durable"
 # W2-41: the controller binary reclaims retired snapshots by default.
 "paralean-control|mutate-gc-off-by-default|tests::controller_collects_unless_told_not_to|--bin paralean-p3"
)
if printf '%s\n' "${cases[@]}" | grep -q -- '|--test '; then
  if [ -z "${PARALEAN_INSTANCE:-}" ] || [ ! -f "${PARALEAN_FDB_CLUSTER:-}" ]; then
    echo "cluster cases need your own running instance: PARALEAN_INSTANCE=<name> (impl/p2/scripts/up.sh)" >&2
    exit 1
  fi
fi
for entry in "${cases[@]}"; do
  IFS='|' read -r package feature test target <<< "$entry"
  log="$out/$feature--${test##*::}.log"
  # Each verdict must name the test; a compiler or infrastructure failure is not a kill.
  if cargo test --manifest-path impl/p2/Cargo.toml -j 4 -p "$package" --features "$feature" $target "$test" -- --exact > "$log" 2>&1; then
    echo "SURVIVED $feature"; exit 1
  fi
  # libtest-mimic suites pad the name column, so match the verdict line by pattern.
  if ! grep -Eq "test[[:space:]]+$test[[:space:]]+\.\.\. FAILED" "$log"; then
    echo "ERROR $feature"; tail -30 "$log"; exit 1
  fi
  echo "detected $feature"
done
python3 - "$out" <<'PY'
from pathlib import Path
import shutil, subprocess, sys, tempfile
# (directory, script, its test, the test's arguments)
boundary = ("impl/p2/scripts", "check-storage-boundary.py", "test-storage-boundary.py", [])
ws = ("impl/p3-remote/scripts", "ws.py", "test-ws.py", ["PublishStagingTest.test_publish_does_not_follow_planted_links"])
raised = "AssertionError: ValueError not raised"
planted = "FAIL: test_publish_does_not_follow_planted_links"
mutations = {
    "private_backend_mode": (boundary, 'if parent.st_uid != os.getuid() or stat.S_IMODE(parent.st_mode) & 0o077:', 'if False:', raised),
    "private_secret_files": (boundary, 'if st.st_uid != os.getuid() or stat.S_IMODE(st.st_mode) & 0o077:', 'if False:', raised),
    "private_backend_tcp": (boundary, 'raise ValueError("direct Garage TCP port is reachable; restart this instance")', 'return', raised),
    # W2-40: garage.toml carries a metrics token, and the running Garage enforces it.
    "metrics_token_required": (boundary, 'if not isinstance(token, str) or len(token) < 32:', 'if False:', raised),
    "metrics_unauthenticated_refused": (boundary, 'if metrics_status(addr, None) not in (401, 403):', 'if False:', raised),
    # W2-20: ws.py stages the receipt and plan outside the working copy, without following links.
    "ws_receipt_private_dir": (ws, 'rpath = os.path.join(staging, "receipt.json")\n            write_new_file(rpath, json.dumps(v))',
                               'rpath = os.path.join(d, "receipt.json")\n            json.dump(v, open(rpath, "w"))', planted),
    "ws_plan_private_dir": (ws, 'plan = os.path.join(staging, "plan.json")', 'plan = os.path.join(d, "plan.json")', planted),
}
for name, ((directory, script, test, args), old, new, verdict) in mutations.items():
    source = Path(directory)
    text = (source / script).read_text()
    assert text.count(old) == 1, name
    with tempfile.TemporaryDirectory(prefix="w2-script-mutation-") as tmp:
        dest = Path(tmp)
        (dest / script).write_text(text.replace(old, new))
        shutil.copyfile(source / test, dest / test)
        result = subprocess.run([sys.executable, str(dest / test), *args], capture_output=True, text=True)
        (Path(sys.argv[1]) / (name + ".log")).write_text(result.stdout + result.stderr)
        assert result.returncode != 0 and verdict in result.stderr and "ERROR:" not in result.stderr, result.stderr
        print("detected", name)
PY
total=$((${#cases[@]} + 7))
echo "W2 security mutations: $total/$total detected"
