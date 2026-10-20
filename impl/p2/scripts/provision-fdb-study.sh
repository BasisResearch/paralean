#!/usr/bin/env bash
# Provision a private FDB-only study instance, without starting Garage.
# Example, after checking that ports and the instance name are unused:
#   PARALEAN_INSTANCE=mp2-gray PARALEAN_PORT_BASE=24100 scripts/provision-fdb-study.sh gray
#   PARALEAN_INSTANCE=mp2-coord PARALEAN_PORT_BASE=24200 scripts/provision-fdb-study.sh coordinator
# Run scripts/down.sh with the same PARALEAN_INSTANCE to stop only this instance.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
mode="${1:-}"
case "$mode" in gray|coordinator) ;; *) echo 'usage: provision-fdb-study.sh gray|coordinator' >&2; exit 2 ;; esac
[[ "${PARALEAN_INSTANCE:-}" =~ ^mp2-[A-Za-z0-9_-]+$ ]] || {
  echo 'requires PARALEAN_INSTANCE matching ^mp2-[A-Za-z0-9_-]+$' >&2; exit 2;
}
base="${PARALEAN_PORT_BASE:?set PARALEAN_PORT_BASE to a free 100-port range}"
[[ "$base" =~ ^[0-9]+$ ]] && [ "$base" -ge 1024 ] && [ "$base" -le 65400 ] || {
  echo 'invalid PARALEAN_PORT_BASE' >&2; exit 2;
}
. "$here/env.sh"
H="$PARALEAN_HOME"
P="$PARALEAN_P2_PREFIX"
[ ! -e "$H" ] || { echo "instance already exists: $H" >&2; exit 2; }
[ -x "$P/bin/fdbserver" ] && [ -x "$P/bin/fdbcli" ] || {
  echo 'run bootstrap.sh to install the pinned FDB binaries first' >&2; exit 2;
}
count=5
[ "$mode" = coordinator ] && count=6
if [ "$mode" = gray ]; then
  ns="$here/../target/release/netsplit"
  [ -x "$ns" ] || (cd "$here/.." && cargo build --release -p netsplit -j 1)
fi
python3 - "$base" "$mode" <<'PY'
import socket, sys
base, mode = int(sys.argv[1]), sys.argv[2]
addresses = [(f'127.0.0.{i+2}', base+i) for i in range(6)] if mode == 'coordinator' else \
            [('127.0.0.1', base+i) for i in range(5)] + [('127.0.0.1', base+10+i) for i in range(5)]
for host, port in addresses:
    with socket.socket() as sock:
        try: sock.bind((host, port))
        except OSError as exc: raise SystemExit(f'{host}:{port} unavailable: {exc}')
PY
mkdir -p "$H/fdb" "$H/run"
cat > "$H/instance.sh" <<EOF
export PARALEAN_FDB_PORT=$base PARALEAN_GARAGE_S3_PORT=$((base+20))
export PARALEAN_GARAGE_RPC_PORT=$((base+30)) PARALEAN_GARAGE_ADMIN_PORT=$((base+40))
export PARALEAN_S3_PORT=$((base+50))
export PARALEAN_FDB_CLUSTER="$H/fdb/fdb.cluster"
export PARALEAN_S3_ENDPOINT="http://127.0.0.1:$((base+50))"
export PARALEAN_FDB_PROCS=$count PARALEAN_FDB_REDUNDANCY=triple
export PARALEAN_FDB_COORDINATORS=5 PARALEAN_NETSPLIT=$([ "$mode" = gray ] && echo 1 || echo 0)
export PARALEAN_GARAGE_NODES=1 PARALEAN_GARAGE_REPLICATION=1
EOF
token="$(head -c 8 /dev/urandom | od -An -tx1 | tr -d ' \n')"
coords=''
for i in 0 1 2 3 4; do
  if [ "$mode" = gray ]; then addr="127.0.0.1:$((base+i))"; else addr="127.0.0.$((i+2)):$((base+i))"; fi
  coords="$coords${coords:+,}$addr"
done
echo "paralean:mp2${mode}${token}@$coords" > "$H/fdb/fdb.cluster"
if [ "$mode" = gray ]; then
  : > "$H/run/netsplit.state"
  maps=()
  for i in 0 1 2 3 4; do maps+=(--map "$i:$((base+i)):$((base+10+i))"); done
  setsid nohup "$ns" --state "$H/run/netsplit.state" "${maps[@]}" \
    > "$H/run/netsplit.log" 2>&1 < /dev/null &
  echo $! > "$H/run/netsplit.pid"
  for i in 0 1 2 3 4; do "$here/proc.sh" fdb start "$i"; done
else
  knobs='--knob_min_available_space_ratio=0.002 --knob_min_available_space_ratio_safety_buffer=0.001 --knob_min_available_space=200000000'
  for i in 0 1 2 3 4 5; do
    addr="127.0.0.$((i+2)):$((base+i))"
    d="$H/fdb/p$i"
    mkdir -p "$d/data" "$d/log"
    setsid nohup "$P/bin/fdbserver" -p "$addr" -C "$H/fdb/fdb.cluster" \
      -d "$d/data" -L "$d/log" --locality-zoneid "z$i" --locality-machineid "m$i" \
      --cache-memory 256MiB --knob_disable_posix_kernel_aio=1 $knobs \
      > "$d/log/stdout.log" 2>&1 < /dev/null &
    echo $! > "$H/run/fdbserver-$i.pid"
  done
fi
"$P/bin/fdbcli" -C "$H/fdb/fdb.cluster" --timeout 60 --exec "configure new triple ${PARALEAN_FDB_ENGINE:-ssd}"
for _ in $(seq 1 90); do
  if "$P/bin/fdbcli" -C "$H/fdb/fdb.cluster" --timeout 5 --exec 'status json' 2>/dev/null |
     python3 -c 'import json,sys
try:
 c=json.load(sys.stdin)["cluster"]
 assert c["database_available"] and c["fault_tolerance"]["max_zone_failures_without_losing_availability"]>=2
except Exception: sys.exit(1)' ; then
    echo "$mode FDB study instance ready: $PARALEAN_INSTANCE, $count fdbservers, fault tolerance 2"
    exit 0
  fi
  sleep 2
done
echo 'FDB did not reach fault tolerance 2; inspect instance logs and stop it with down.sh' >&2
exit 1
