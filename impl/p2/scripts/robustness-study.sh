#!/usr/bin/env bash
# Additional P2 fault experiments. Run only against a disposable, private instance.
#
# Prerequisites:
#   gray:         5 FDB processes, netsplit, triple redundancy; Garage may be stopped.
#   coordinator:  6 FDB processes, 5 coordinators, triple redundancy.
#   garage-layout: 3 Garage nodes, replication 3, plus a spare node n3 already started
#                  and connected but not assigned a storage role.
#   segv:         6 FDB processes, triple redundancy, one Garage and s3-guard;
#                 run with a single stress worker under GDB.
#
# The study never creates or starts an instance. Use a unique mp2-* name and port base.
# To avoid exceeding the shared box's process budget, run phases sequentially on
# appropriately shaped instances. Logs are kept in results/p2/robustness-<instance>/.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
[[ "${PARALEAN_INSTANCE:-}" =~ ^mp2-[A-Za-z0-9_-]+$ ]] || {
  echo 'requires PARALEAN_INSTANCE matching ^mp2-[A-Za-z0-9_-]+$' >&2; exit 2;
}
. "$here/env.sh"
H="$PARALEAN_HOME"
P="$PARALEAN_P2_PREFIX"
phase="${1:-}"
out="${OUT:-$here/../../../results/p2/robustness-$PARALEAN_INSTANCE}/$phase"
mkdir -p "$out"
fdbcli() { "$P/bin/fdbcli" -C "$PARALEAN_FDB_CLUSTER" --timeout "${FDBCLI_TIMEOUT:-8}" --exec "$1"; }
garage() { "$P/bin/garage" -c "$H/garage/n0/garage.toml" "$@"; }
proc() { "$here/proc.sh" "$@" | tee -a "$out/events.log"; }
log() { echo "$(date -u +%FT%TZ) $*" | tee -a "$out/events.log"; }
need() { command -v "$1" >/dev/null || { echo "missing $1" >&2; exit 2; }; }
assert_shape() {
  [ "$PARALEAN_FDB_PROCS" -ge "$1" ] && [ "$PARALEAN_FDB_REDUNDANCY" = triple ] || {
    echo "needs >=$1 FDB processes and triple redundancy" >&2; exit 2;
  }
}
status_json() { fdbcli 'status json' 2>/dev/null; }
tolerance() {
  status_json | python3 -c 'import json,sys
try:
 c=json.load(sys.stdin)["cluster"]
 print(c["fault_tolerance"]["max_zone_failures_without_losing_availability"] if c.get("database_available") else -1)
except Exception: print(-1)'
}
write_probe() { fdbcli "writemode on; set robustness-probe $(date +%s%N); get robustness-probe" >/dev/null 2>&1; }
wait_healthy() {
  local start=$SECONDS
  while [ $((SECONDS-start)) -lt "${RECOVERY_TIMEOUT:-600}" ]; do
    if write_probe && [ "$(tolerance)" -ge "$1" ]; then
      log "healthy: write and fault tolerance >=$1 after $((SECONDS-start)) s"
      return 0
    fi
    sleep 2
  done
  log "FAILED to recover writes and fault tolerance >=$1"
  return 1
}
probe_loop() {
  local label=$1 stop="$out/$1.stop" file="$out/$1.probe.tsv" t0 t1 rc
  rm -f "$stop"
  : > "$file"
  while [ ! -e "$stop" ]; do
    t0=$(date +%s%N)
    if write_probe; then rc=0; else rc=1; fi
    t1=$(date +%s%N)
    printf '%s\t%s\t%s\n' "$t0" "$t1" "$rc" >> "$file"
    sleep 1
  done
}
summarize_probe() {
  python3 - "$1" <<'PY'
import json, sys
rows = [(int(a), int(b), int(c)) for a,b,c in
        (line.split() for line in open(sys.argv[1]))]
windows = []
start = None
for i, (_, _, bad) in enumerate(rows + [(0,0,0)]):
    if bad and start is None: start = i
    if not bad and start is not None:
        # A failed probe times out after its own duration. The true outage onset
        # and recovery occur between successful completions; report that bracket,
        # never call the gap between failed start timestamps the outage length.
        prev_ok_end = rows[start-1][1] if start else None
        next_ok_end = rows[i][1] if i < len(rows) else None
        windows.append({"first_failed_start_ns":rows[start][0],
                        "last_failed_end_ns":rows[i-1][1],
                        "failed_samples":i-start,
                        "observed_failure_span_s":round((rows[i-1][1]-rows[start][0])/1e9,3),
                        "last_ok_to_next_ok_s":round((next_ok_end-prev_ok_end)/1e9,3)
                          if prev_ok_end and next_ok_end else None})
        start = None
result = {"probes": len(rows), "failed_probes":sum(r[2] for r in rows),
          "max_probe_duration_s":round(max(((b-a)/1e9 for a,b,_ in rows),default=0),3),
          "failure_windows":windows,
          "measurement_note":"Probe calls are serial, with a one-second gap. A timeout is one failed sample; actual outage is bracketed by adjacent successful probe completions."}
print(json.dumps(result, indent=2))
PY
}
cleanup_probe() {
  if [ -n "${probe_pid:-}" ]; then
    touch "$out/$probe_label.stop"
    wait "$probe_pid" || true
    probe_pid=''
  fi
}
trap cleanup_probe EXIT

case "$phase" in
gray)
  assert_shape 5
  [ "$PARALEAN_NETSPLIT" = 1 ] || { echo 'gray phase needs netsplit' >&2; exit 2; }
  # Pinned 7.3.79 defaults: FlowKnobs FAILURE_DETECTION_DELAY=4.0,
  # CONNECTION_MONITOR_LOOP_TIME=1.0, CONNECTION_MONITOR_TIMEOUT=2.0.
  # Paired mode compares default and a 1.0-s failure delay. Fast mode is a
  # second candidate: shorter network connection monitor timeout and loop.
  [ "${PARALEAN_FDB_KNOBS:-}" = '' ] || { echo 'start gray phase without PARALEAN_FDB_KNOBS set' >&2; exit 2; }
  labels=(baseline tuned)
  if [ "${GRAY_MODE:-paired}" = fast ]; then
    labels=(fast)
    export PARALEAN_FDB_KNOBS='--knob_min_available_space_ratio=0.002 --knob_min_available_space_ratio_safety_buffer=0.001 --knob_min_available_space=200000000 --knob_failure_detection_delay=1.0 --knob_connection_monitor_timeout=0.5 --knob_connection_monitor_loop_time=0.25'
    log "fast candidate knobs: $PARALEAN_FDB_KNOBS"
    RESTART_AT_START=1
  fi
  if [ "${RESTART_AT_START:-0}" = 1 ]; then
    for i in $(seq 0 $((PARALEAN_FDB_PROCS-1))); do
      log "restart fdbserver-$i for ${GRAY_MODE:-paired} starting setting"
      proc fdb kill "$i"; proc fdb start "$i"; wait_healthy 2
    done
  fi
  for label in "${labels[@]}"; do
    for trial in $(seq 1 "${TRIALS:-3}"); do
      wait_healthy 2
      probe_label="$label-$trial"
      status_json > "$out/$probe_label.status.json"
      probe_loop "$probe_label" & probe_pid=$!
      sleep 5
      log "$probe_label: SIGSTOP fdbserver-2 for 15 s"
      printf '%s\t%s\tstop\tbegin\n' "$(date +%s%N)" "$probe_label" >> "$out/faults.tsv"
      proc fdb pause 2; sleep 15; proc fdb resume 2
      printf '%s\t%s\tstop\tend\n' "$(date +%s%N)" "$probe_label" >> "$out/faults.tsv"
      wait_healthy 2
      sleep 5
      log "$probe_label: netsplit fdbserver-3 for 15 s"
      printf '%s\t%s\tsplit\tbegin\n' "$(date +%s%N)" "$probe_label" >> "$out/faults.tsv"
      proc split 3; sleep 15; proc heal
      printf '%s\t%s\tsplit\tend\n' "$(date +%s%N)" "$probe_label" >> "$out/faults.tsv"
      wait_healthy 2
      sleep 5
      cleanup_probe
      summarize_probe "$out/$probe_label.probe.tsv" > "$out/$probe_label.summary.json"
      cat "$out/$probe_label.summary.json" | tee -a "$out/events.log"
    done
    if [ "$label" = baseline ]; then
      # Restart one process at a time so the triple cluster stays available.
      export PARALEAN_FDB_KNOBS='--knob_min_available_space_ratio=0.002 --knob_min_available_space_ratio_safety_buffer=0.001 --knob_min_available_space=200000000 --knob_failure_detection_delay=1.0'
      for i in $(seq 0 $((PARALEAN_FDB_PROCS-1))); do
        log "restart fdbserver-$i with failure_detection_delay=1.0"
        proc fdb kill "$i"; proc fdb start "$i"; wait_healthy 2
      done
    fi
  done
  ;;
coordinator)
  assert_shape 6
  [ "$PARALEAN_FDB_COORDINATORS" -eq 5 ] || { echo 'needs five initial coordinators' >&2; exit 2; }
  wait_healthy 2
  before_token="coord-before-$(date +%s%N)"
  fdbcli "writemode on; set robustness-coordinator-before $before_token" > "$out/preloss-write.txt"
  fdbcli 'get robustness-coordinator-before' > "$out/preloss-read.txt"
  grep -Fq "$before_token" "$out/preloss-read.txt" || { log 'FAILED: pre-loss write not readable'; exit 1; }
  cp "$PARALEAN_FDB_CLUSTER" "$out/coordinators-before.cluster"
  old_first="$(sed 's/.*@//;s/,.*//' "$out/coordinators-before.cluster")"
  log 'permanently kill fdbserver-0 (initial coordinator)'
  proc fdb kill 0
  wait_healthy 1
  log 'run coordinators auto with a majority of old coordinators still available'
  set +e
  fdbcli 'coordinators auto' > "$out/coordinators-auto.log" 2>&1
  rc=$?
  set -e
  cp "$PARALEAN_FDB_CLUSTER" "$out/coordinators-after.cluster"
  status_json > "$out/status-after.json" || true
  cat "$out/coordinators-auto.log" | tee -a "$out/events.log"
  log "coordinators auto exit=$rc; before=$(cat "$out/coordinators-before.cluster"); after=$(cat "$out/coordinators-after.cluster")"
  [ "$rc" -eq 0 ] || { log 'FAILED: coordinators auto exited nonzero'; exit 1; }
  # The lost coordinator was the first listed address. A success message with no changed
  # connection string is not a successful permanent-loss replacement.
  for _ in $(seq 1 30); do
    if ! grep -Fq "$old_first" "$PARALEAN_FDB_CLUSTER"; then break; fi
    sleep 1
  done
  if grep -Fq "$old_first" "$PARALEAN_FDB_CLUSTER"; then
    log 'FAILED: dead coordinator remains in cluster connection string'
    exit 1
  fi
  fdbcli 'get robustness-coordinator-before' > "$out/postloss-read-old.txt"
  grep -Fq "$before_token" "$out/postloss-read-old.txt" || {
    log 'FAILED: acknowledged pre-loss value missing'; exit 1;
  }
  token="coord-$(date +%s%N)"
  fdbcli "writemode on; set robustness-coordinator $token" > "$out/coordinator-write.txt"
  fdbcli 'get robustness-coordinator' > "$out/coordinator-read.txt"
  grep -Fq "$token" "$out/coordinator-read.txt" || { log 'FAILED: value unreadable after coordinator change'; exit 1; }
  log 'coordinator replacement and post-change read/write passed'
  ;;
garage-layout)
  [ "$PARALEAN_GARAGE_NODES" -eq 3 ] && [ "$PARALEAN_GARAGE_REPLICATION" -eq 3 ] || {
    echo 'needs three assigned Garage nodes with replication 3' >&2; exit 2;
  }
  need aws
  export AWS_ACCESS_KEY_ID="$PARALEAN_S3_ACCESS_KEY" AWS_SECRET_ACCESS_KEY="$PARALEAN_S3_SECRET_KEY"
  export AWS_DEFAULT_REGION="$PARALEAN_S3_REGION" AWS_EC2_METADATA_DISABLED=true
  s3() {
    local node=$1; shift
    timeout 35 aws --no-cli-pager --cli-connect-timeout 2 --cli-read-timeout 15 \
      --endpoint-url "http://127.0.0.1:$((PARALEAN_GARAGE_S3_PORT+node))" s3api "$@"
  }
  payload="$out/acknowledged-payload.txt"
  printf 'Garage layout replacement %s\n' "$(date -u +%FT%TZ)" > "$payload"
  key="robustness/layout/$(date +%s%N)"
  s3 0 put-object --bucket "$PARALEAN_S3_BUCKET" --key "$key" --body "$payload" > "$out/put-before.json"
  # Read the acknowledged object through all three original nodes before loss.
  for j in 0 1 2; do
    s3 "$j" get-object --bucket "$PARALEAN_S3_BUCKET" --key "$key" "$out/pre-n$j.txt" > "$out/pre-n$j.json"
    cmp "$payload" "$out/pre-n$j.txt"
  done
  # The fourth node is a spare; do not let up.sh assign it automatically.
  if [ ! -f "$H/garage/n3/garage.toml" ]; then
    mkdir -p "$H/garage/n3/meta" "$H/garage/n3/data"
    python3 - "$H" "$PARALEAN_GARAGE_RPC_PORT" "$PARALEAN_GARAGE_S3_PORT" "$PARALEAN_GARAGE_ADMIN_PORT" <<'PY'
import pathlib, sys
h = pathlib.Path(sys.argv[1])
text = (h / 'garage/n2/garage.toml').read_text()
text = text.replace(str(h / 'garage/n2'), str(h / 'garage/n3'))
for port in map(int, sys.argv[2:]):
    text = text.replace(f'127.0.0.1:{port+2}', f'127.0.0.1:{port+3}')
text = text.replace(f'rpc_bind_addr = "127.0.0.4:{int(sys.argv[2])+2}"',
                    f'rpc_bind_addr = "127.0.0.5:{int(sys.argv[2])+3}"')
(h / 'garage/n3/garage.toml').write_text(text)
PY
  fi
  if [ "${PARALEAN_GARAGE_NETSPLIT:-0}" = 1 ]; then
    proxy_pid_file="$H/run/garage-netsplit.pid"
    [ -f "$proxy_pid_file" ] || { echo 'Garage proxy PID missing' >&2; exit 2; }
    proxy_pid=$(cat "$proxy_pid_file")
    proxy_bin=$(readlink -f "/proc/$proxy_pid/exe")
    proxy_cmd=$(tr '\0' ' ' < "/proc/$proxy_pid/cmdline")
    [[ "$proxy_cmd" == *"$H/run/garage-netsplit.state"* ]] || {
      echo 'Garage proxy PID does not belong to this instance' >&2; exit 2;
    }
    kill "$proxy_pid"
    for _ in $(seq 1 50); do
      kill -0 "$proxy_pid" 2>/dev/null || break
      sleep 0.1
    done
    state="$H/run/garage-netsplit.state"
    setsid nohup "$proxy_bin" --state "$state" \
      --map "0:$PARALEAN_GARAGE_RPC_PORT:127.0.0.2" \
      --map "1:$((PARALEAN_GARAGE_RPC_PORT+1)):127.0.0.3" \
      --map "2:$((PARALEAN_GARAGE_RPC_PORT+2)):127.0.0.4" \
      --map "3:$((PARALEAN_GARAGE_RPC_PORT+3)):127.0.0.5" \
      >> "$H/run/garage-netsplit.log" 2>&1 < /dev/null &
    echo $! > "$proxy_pid_file"
    log "Garage proxy extended to n3 at 127.0.0.1:$((PARALEAN_GARAGE_RPC_PORT+3))"
  fi
  proc garage start 3
  for _ in $(seq 1 30); do
    if "$P/bin/garage" -c "$H/garage/n3/garage.toml" status > "$out/spare-status.txt" 2>&1; then break; fi
    sleep 1
  done
  spare_addr=$("$P/bin/garage" -c "$H/garage/n3/garage.toml" node id -q | head -1)
  garage node connect "$spare_addr" > "$out/spare-connect.txt"
  old=$("$P/bin/garage" -c "$H/garage/n2/garage.toml" node id -q | head -1)
  old="${old%%@*}"
  new="${spare_addr%%@*}"
  [ -n "$old" ] && [ -n "$new" ] || { echo 'could not get Garage node IDs' >&2; exit 2; }
  garage layout show > "$out/layout-before.txt"
  log "permanently kill Garage n2=$old; replace its role with n3=$new"
  proc garage kill 2
  garage layout assign "$new" -z dc2 -c 2G --replace "$old" | tee "$out/layout-stage.txt"
  garage layout show > "$out/layout-staged.txt"
  version=$(sed -n 's/.*[Cc]urrent cluster layout version: *\([0-9]*\).*/\1/p' "$out/layout-staged.txt" | head -1)
  [ -n "$version" ] || { echo 'could not parse Garage layout version' >&2; exit 1; }
  garage layout apply --version "$((version+1))" | tee "$out/layout-apply.txt"
  garage layout show > "$out/layout-after.txt"
  garage status > "$out/status-after.txt"
  "$P/bin/garage" -c "$H/garage/n3/garage.toml" repair --yes blocks > "$out/block-repair.txt" 2>&1
  # The removed identity cannot acknowledge the new layout. Garage requires an
  # explicit skip for a permanently dead node; do not permit missing quorum data.
  garage layout skip-dead-nodes --version "$((version+1))" > "$out/skip-dead-nodes.txt"
  for _ in $(seq 1 90); do
    garage health > "$out/health-after.txt"
    grep -q 'Cluster health: *HEALTHY' "$out/health-after.txt" && break
    sleep 2
  done
  grep -q 'Cluster health: *HEALTHY' "$out/health-after.txt" || {
    log 'FAILED: layout did not return to HEALTHY after replacing dead node'; exit 1;
  }
  for _ in $(seq 1 90); do
    if s3 0 get-object --bucket "$PARALEAN_S3_BUCKET" --key "$key" "$out/post-replacement.txt" > "$out/post-replacement.json" 2>&1 \
      && cmp -s "$payload" "$out/post-replacement.txt"; then break; fi
    sleep 2
  done
  cmp "$payload" "$out/post-replacement.txt" || { log 'FAILED: acknowledged object not readable after layout change'; exit 1; }
  for _ in $(seq 1 90); do
    if s3 3 get-object --bucket "$PARALEAN_S3_BUCKET" --key "$key" "$out/post-replacement-n3.txt" > "$out/post-replacement-n3.json" 2> "$out/post-replacement-n3.err" \
      && cmp -s "$payload" "$out/post-replacement-n3.txt"; then break; fi
    sleep 2
  done
  cmp "$payload" "$out/post-replacement-n3.txt" || { log 'FAILED: replacement node cannot read pre-loss acknowledgement'; exit 1; }
  post_key="robustness/layout/post-$(date +%s%N)"
  s3 0 put-object --bucket "$PARALEAN_S3_BUCKET" --key "$post_key" --body "$payload" > "$out/put-after.json"
  s3 3 get-object --bucket "$PARALEAN_S3_BUCKET" --key "$post_key" "$out/post-write.txt" > "$out/post-write.json"
  cmp "$payload" "$out/post-write.txt"
  log "layout applied version $((version+1)); preack object and postwrite verified"
  ;;
segv)
  assert_shape 6
  need gdb
  need pgrep
  segv_worker="${SEGV_WORKER:-0}"
  segv_seed_base="${SEGV_SEED_BASE:-1}"
  [[ "$segv_worker" =~ ^[0-9]{1,9}$ && "$segv_seed_base" =~ ^[0-9]{1,9}$ ]] || {
    echo 'SEGV_WORKER and SEGV_SEED_BASE must be nonnegative decimal integers with at most nine digits' >&2
    exit 2
  }
  ulimit -c unlimited
  bin="$here/../target/debug/paralean-p2"
  [ -x "$bin" ] || { echo "build $bin first" >&2; exit 2; }
  wait_healthy 2
  export PARALEAN_DEPLOYMENT="segv-$(date +%s)"
  export PARALEAN_KEYS="$out/keys.json"
  "$bin" keys init "$PARALEAN_KEYS" --demo --workspaces 6
  # Host apport may intercept SIGSEGV and ulimit may be hard zero. GDB catches
  # the signal before the kernel handler and writes a core without sysctl changes.
  # One worker at a time repeats run 1's double loss of fdbserver-3 and -5.
  # The original run had six concurrent workers; this study isolates teardown.
  completed=0
  for attempt in $(seq 1 "${SEGV_MAX_STARTS:-30}"); do
    [ "$completed" -lt "${SEGV_ATTEMPTS:-10}" ] || break
    before_acks=$(wc -l < "$out/acks.log" 2>/dev/null || echo 0)
    seed=$((10#$segv_seed_base + attempt - 1))
    log "double disk-loss attempt $attempt: GDB stress worker=$segv_worker seed=$seed starts"
    gdb --batch -q -ex 'set pagination off' -ex 'set disable-randomization off' \
      -ex 'set startup-with-shell off' \
      -ex 'handle SIGSEGV stop print nopass' -ex run \
      -ex 'thread apply all bt full' \
      -ex "generate-core-file $out/core-attempt-$attempt" \
      --args "$bin" stress --worker "$segv_worker" --ops 25 --seed "$seed" --fault-p 0.02 \
      --ack-log "$out/acks.log" > "$out/gdb-$attempt.log" 2>&1 &
    gdb_pid=$!
    worker_pid=''
    for _ in $(seq 1 60); do
      worker_pid=$(pgrep -P "$gdb_pid" -f paralean-p2 | head -1 || true)
      [ -n "$worker_pid" ] && break
      kill -0 "$gdb_pid" 2>/dev/null || break
      sleep 0.05
    done
    if [ -z "$worker_pid" ] || ! kill -0 "$worker_pid" 2>/dev/null; then
      wait "$gdb_pid" || true
      log "attempt $attempt ended before fault injection; retrying"
      continue
    fi
    log "kill and wipe fdbserver-3 and fdbserver-5 while worker pid=$worker_pid is active"
    proc fdb kill 3; proc fdb kill 5
    active_at_wipe=0
    if kill -0 "$worker_pid" 2>/dev/null; then
      proc fdb wipe 3; proc fdb wipe 5
      kill -0 "$worker_pid" 2>/dev/null && active_at_wipe=1
    else
      proc fdb wipe 3; proc fdb wipe 5
    fi
    sleep 5
    proc fdb start 3; proc fdb start 5
    wait "$gdb_pid" || true
    wait_healthy 2
    segv=0
    if rg -q 'received signal SIGSEGV' "$out/gdb-$attempt.log"; then
      if [ ! -s "$out/core-attempt-$attempt" ]; then
        log "FAILED: SIGSEGV reproduced but GDB did not write core-attempt-$attempt"
        exit 1
      fi
      segv=1
    elif ! rg -q 'exited normally' "$out/gdb-$attempt.log"; then
      log "FAILED: GDB inferior did not exit normally; inspect gdb-$attempt.log"
      exit 1
    fi
    if [ -s "$out/acks.log" ]; then
      "$bin" verify-acks "$out/acks.log" > "$out/verify-$attempt.log" 2>&1 || {
        log "FAILED: acknowledged effect missing after attempt $attempt"; exit 1;
      }
    fi
    "$bin" audit > "$out/audit-$attempt.log" 2>&1 || {
      log "FAILED: audit after attempt $attempt"; exit 1;
    }
    if [ "$segv" = 1 ]; then
      log "SIGSEGV reproduced in attempt $attempt; acknowledgements verified, audit clean; inspect gdb log and core"
      exit 139
    fi
    after_acks=$(wc -l < "$out/acks.log" 2>/dev/null || echo 0)
    if [ "$active_at_wipe" != 1 ] || [ "$after_acks" -le "$before_acks" ]; then
      log "attempt $attempt did not overlap the disk wipe with an active acknowledged worker (active=$active_at_wipe, ack delta=$((after_acks-before_acks))); retrying"
      continue
    fi
    completed=$((completed+1))
  done
  [ "$completed" -eq "${SEGV_ATTEMPTS:-10}" ] || {
    log "INCOMPLETE: only $completed overlapping attempts after ${SEGV_MAX_STARTS:-30} worker starts"
    exit 1
  }
  log "no SIGSEGV in $completed double disk-loss attempts; acknowledge logs and audits passed"
  ;;
*)
  echo 'usage: robustness-study.sh gray|coordinator|garage-layout|segv' >&2
  exit 2
  ;;
esac
