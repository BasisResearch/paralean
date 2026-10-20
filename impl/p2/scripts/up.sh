#!/usr/bin/env bash
# Start a P2 cluster. Idempotent.
#
# Default (PARALEAN_INSTANCE unset): one fdbserver (ssd engine by default, set
# PARALEAN_FDB_ENGINE=memory for memory mode), one Garage node (replication factor 1,
# consistent mode) and the s3-guard gateway that refuses deletes, under $PARALEAN_P2_PREFIX.
#
# Instance (PARALEAN_INSTANCE=<name>, see env.sh): the same services under
# $PARALEAN_P2_PREFIX/inst/<name> with their own ports, credentials and shape:
# PARALEAN_FDB_PROCS fdbservers (one zone each) configured as PARALEAN_FDB_REDUNDANCY with the
# first PARALEAN_FDB_COORDINATORS processes as coordinators, optionally behind netsplit
# (PARALEAN_NETSPLIT=1, for partitions), and PARALEAN_GARAGE_NODES Garage nodes (one zone
# each) with replication factor PARALEAN_GARAGE_REPLICATION. Example:
#   PARALEAN_INSTANCE=ft PARALEAN_PORT_BASE=21100 PARALEAN_FDB_PROCS=6 \
#   PARALEAN_FDB_REDUNDANCY=triple PARALEAN_FDB_COORDINATORS=5 PARALEAN_NETSPLIT=1 \
#   PARALEAN_GARAGE_NODES=3 PARALEAN_GARAGE_REPLICATION=3 scripts/up.sh
set -euo pipefail
umask 077
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
. "$here/private.sh"
P="$PARALEAN_P2_PREFIX"
H="$PARALEAN_HOME"
engine="${PARALEAN_FDB_ENGINE:-ssd}"
[ -x "$P/bin/fdbserver" ] && [ -x "$P/bin/garage" ] || { echo "run bootstrap.sh first" >&2; exit 1; }
fdbcli() { "$P/bin/fdbcli" -C "$PARALEAN_FDB_CLUSTER" "$@"; }
hex() { head -c "$1" /dev/urandom | od -An -tx1 | tr -d ' \n'; }

if [ -n "$PARALEAN_INSTANCE" ]; then
  if [ ! -f "$H/instance.sh" ] && [ -z "${PARALEAN_PORT_BASE:-}" ]; then
    echo "first start of instance $PARALEAN_INSTANCE needs PARALEAN_PORT_BASE" >&2; exit 1
  fi
  mkdir -p "$H/run" "$H/fdb" "$H/garage"
  chmod 700 "$H/garage"
  if [ ! -f "$H/instance.sh" ]; then
    cat > "$H/instance.sh" <<EOF
# Instance $PARALEAN_INSTANCE, written by up.sh on first start.
export PARALEAN_FDB_PORT=$PARALEAN_FDB_PORT PARALEAN_GARAGE_S3_PORT=$PARALEAN_GARAGE_S3_PORT
export PARALEAN_GARAGE_RPC_PORT=$PARALEAN_GARAGE_RPC_PORT PARALEAN_GARAGE_ADMIN_PORT=$PARALEAN_GARAGE_ADMIN_PORT
export PARALEAN_S3_PORT=$PARALEAN_S3_PORT
export PARALEAN_FDB_CLUSTER="$H/fdb/fdb.cluster" PARALEAN_S3_ENDPOINT="http://127.0.0.1:$PARALEAN_S3_PORT"
export PARALEAN_FDB_PROCS=$PARALEAN_FDB_PROCS PARALEAN_FDB_REDUNDANCY=$PARALEAN_FDB_REDUNDANCY
export PARALEAN_FDB_COORDINATORS=$PARALEAN_FDB_COORDINATORS PARALEAN_NETSPLIT=$PARALEAN_NETSPLIT
export PARALEAN_GARAGE_NODES=$PARALEAN_GARAGE_NODES PARALEAN_GARAGE_REPLICATION=$PARALEAN_GARAGE_REPLICATION
export PARALEAN_GARAGE_NETSPLIT=$PARALEAN_GARAGE_NETSPLIT
EOF
  fi
  . "$H/instance.sh"
  if [ ! -f "$H/garage/credentials.sh" ]; then
    ( umask 077; cat > "$H/garage/credentials.sh" <<CREDS
export PARALEAN_GARAGE_RPC_SECRET=$(hex 32)
export PARALEAN_GARAGE_ADMIN_TOKEN=$(hex 32)
export PARALEAN_S3_ACCESS_KEY=GK$(hex 12)
export PARALEAN_S3_SECRET_KEY=$(hex 32)
CREDS
    )
  fi
  . "$H/garage/credentials.sh"
else
  [ "$PARALEAN_FDB_PROCS" = 1 ] && [ "$PARALEAN_GARAGE_NODES" = 1 ] || {
    echo "the default cluster is single-process; set PARALEAN_INSTANCE for a multi-process cluster" >&2; exit 1; }
fi
mkdir -p "$H/run"
alive() { [ -f "$H/run/$1.pid" ] && kill -0 "$(cat "$H/run/$1.pid")" 2>/dev/null; }

# --- FoundationDB
# FDB's ratekeeper keeps 5% of the disk as operating space by default; on the shared box
# /data is ~98% full, so that reserve alone throttles every write to zero. Lower it.
knobs="${PARALEAN_FDB_KNOBS:---knob_min_available_space_ratio=0.002 --knob_min_available_space_ratio_safety_buffer=0.001 --knob_min_available_space=200000000}"
if [ -z "$PARALEAN_INSTANCE" ]; then
  mkdir -p "$P/fdb/data" "$P/fdb/log"
  [ -f "$PARALEAN_FDB_CLUSTER" ] || echo "paralean:p2$(hex 6)@127.0.0.1:$PARALEAN_FDB_PORT" > "$PARALEAN_FDB_CLUSTER"
  if ! alive fdbserver; then
    setsid nohup "$P/bin/fdbserver" -p "127.0.0.1:$PARALEAN_FDB_PORT" -C "$PARALEAN_FDB_CLUSTER" \
      -d "$P/fdb/data" -L "$P/fdb/log" --knob_disable_posix_kernel_aio=1 $knobs \
      > "$P/fdb/log/stdout.log" 2>&1 < /dev/null &
    echo $! > "$P/run/fdbserver.pid"
  fi
  redundancy=single
else
  if [ ! -f "$PARALEAN_FDB_CLUSTER" ]; then
    coords=""
    for i in $(seq 0 $((PARALEAN_FDB_COORDINATORS - 1))); do coords="$coords${coords:+,}127.0.0.1:$((PARALEAN_FDB_PORT + i))"; done
    echo "paralean:p2${PARALEAN_INSTANCE//[^a-zA-Z0-9]/}$(hex 6)@$coords" > "$PARALEAN_FDB_CLUSTER"
  fi
  if [ "$PARALEAN_NETSPLIT" = 1 ] && ! alive netsplit; then
    maps=()
    for i in $(seq 0 $((PARALEAN_FDB_PROCS - 1))); do
      maps+=(--map "$i:$((PARALEAN_FDB_PORT + i)):$((PARALEAN_FDB_PORT + 10 + i))")
    done
    ns="$here/../target/release/netsplit"
    [ -x "$ns" ] || ( cd "$here/.." && cargo build --release -p netsplit )
    touch "$H/run/netsplit.state"
    setsid nohup "$ns" --state "$H/run/netsplit.state" "${maps[@]}" >> "$H/run/netsplit.log" 2>&1 < /dev/null &
    echo $! > "$H/run/netsplit.pid"
  fi
  for i in $(seq 0 $((PARALEAN_FDB_PROCS - 1))); do "$here/proc.sh" fdb start "$i"; done
  redundancy="$PARALEAN_FDB_REDUNDANCY"
fi
if [ ! -f "$H/fdb/.configured" ]; then
  # First start: create the database.
  fdbcli --timeout 60 --exec "configure new $redundancy $engine"
  touch "$H/fdb/.configured"
fi
for i in $(seq 1 90); do
  st="$(fdbcli --timeout 5 --exec "status minimal" 2>/dev/null || true)"
  case "$st" in *"The database is available"*) break ;; esac
  sleep 1
done
fdbcli --timeout 5 --exec "status minimal"

# --- Garage
if [ -n "$PARALEAN_INSTANCE" ] && [ "$PARALEAN_GARAGE_NETSPLIT" = 1 ] && ! alive garage-netsplit; then
  maps=()
  for j in $(seq 0 $((PARALEAN_GARAGE_NODES - 1))); do
    maps+=(--map "$j:$((PARALEAN_GARAGE_RPC_PORT + j)):127.0.0.$((j + 2))")
  done
  proxy="$here/../target/release/garage-netsplit"
  [ -x "$proxy" ] || ( cd "$here/.." && cargo build --release -p garage-netsplit -j 1 )
  touch "$H/run/garage-netsplit.state"
  setsid nohup "$proxy" --state "$H/run/garage-netsplit.state" "${maps[@]}" \
    >> "$H/run/garage-netsplit.log" 2>&1 < /dev/null &
  echo $! > "$H/run/garage-netsplit.pid"
  sleep 0.2
  alive garage-netsplit || { echo 'Garage RPC proxy failed to start' >&2; exit 1; }
fi
if [ -z "$PARALEAN_INSTANCE" ]; then
  if ! alive garage; then
    setsid nohup "$P/bin/garage" -c "$P/garage/garage.toml" server \
      > "$P/garage/log/garage.log" 2>&1 < /dev/null &
    echo $! > "$P/run/garage.pid"
  fi
  garage() { "$P/bin/garage" -c "$P/garage/garage.toml" "$@"; }
  upstreams="unix:$P/garage/s3.sock"
else
  upstreams=""
  for j in $(seq 0 $((PARALEAN_GARAGE_NODES - 1))); do
    n="$H/garage/n$j"; mkdir -p "$n/meta" "$n/data"
    chmod 700 "$n"
    upstreams="$upstreams${upstreams:+,}unix:$n/s3.sock"
    cat > "$n/garage.toml" <<TOML
metadata_dir = "$n/meta"
data_dir = "$n/data"
db_engine = "lmdb"
metadata_fsync = true
data_fsync = true
replication_factor = $PARALEAN_GARAGE_REPLICATION
consistency_mode = "consistent"
rpc_bind_addr = "$(if [ "$PARALEAN_GARAGE_NETSPLIT" = 1 ]; then echo "127.0.0.$((j + 2))"; else echo '127.0.0.1'; fi):$((PARALEAN_GARAGE_RPC_PORT + j))"
rpc_bind_outgoing = $(if [ "$PARALEAN_GARAGE_NETSPLIT" = 1 ]; then echo true; else echo false; fi)
rpc_public_addr = "127.0.0.1:$((PARALEAN_GARAGE_RPC_PORT + j))"
rpc_secret = "$PARALEAN_GARAGE_RPC_SECRET"

[s3_api]
s3_region = "$PARALEAN_S3_REGION"
api_bind_addr = "$n/s3.sock"
root_domain = ".s3.localhost"

[admin]
api_bind_addr = "127.0.0.1:$((PARALEAN_GARAGE_ADMIN_PORT + j))"
admin_token = "$PARALEAN_GARAGE_ADMIN_TOKEN"
TOML
    "$here/proc.sh" garage start "$j"
  done
  garage() { "$P/bin/garage" -c "$H/garage/n0/garage.toml" "$@"; }
fi
for i in $(seq 1 30); do garage status >/dev/null 2>&1 && break; sleep 1; done
if [ -n "$PARALEAN_INSTANCE" ]; then
  # Connect the nodes (node 0 learns every peer; Garage gossips the rest).
  for j in $(seq 1 $((PARALEAN_GARAGE_NODES - 1))); do
    connected=0
    for i in $(seq 1 30); do
      id="$("$P/bin/garage" -c "$H/garage/n$j/garage.toml" node id -q 2>/dev/null | head -1)" || id=''
      if [ -n "$id" ] && garage node connect "$id" >/dev/null 2>&1; then
        connected=1
        break
      fi
      sleep 1
    done
    [ "$connected" = 1 ] || { echo "Garage node $j did not join" >&2; exit 1; }
  done
  for i in $(seq 1 30); do
    [ "$(garage status 2>/dev/null | grep -c '127.0.0.1:')" -ge "$PARALEAN_GARAGE_NODES" ] && break; sleep 1
  done
fi
if garage status 2>/dev/null | grep -q "NO ROLE ASSIGNED"; then
  if [ -z "$PARALEAN_INSTANCE" ]; then
    node="$(garage status 2>/dev/null | awk -v a="127.0.0.1:$PARALEAN_GARAGE_RPC_PORT" '$3==a{print $1}')"
    garage layout assign -z dc1 -c 20G "$node" >/dev/null
  else
    for j in $(seq 0 $((PARALEAN_GARAGE_NODES - 1))); do
      node="$(garage status 2>/dev/null | awk -v a="127.0.0.1:$((PARALEAN_GARAGE_RPC_PORT + j))" '$3==a{print $1}')"
      garage layout assign -z "dc$j" -c 2G "$node" >/dev/null
    done
  fi
  v="$(garage layout show 2>/dev/null | sed -n 's/.*[Cc]urrent cluster layout version: *\([0-9]*\).*/\1/p' | head -1)"
  garage layout apply --version $(( ${v:-0} + 1 )) >/dev/null
fi
garage bucket info "$PARALEAN_S3_BUCKET" >/dev/null 2>&1 || garage bucket create "$PARALEAN_S3_BUCKET" >/dev/null
garage key info "$PARALEAN_S3_ACCESS_KEY" >/dev/null 2>&1 || import_app_key "$PARALEAN_GARAGE_ADMIN_PORT"
garage bucket allow --read --write "$PARALEAN_S3_BUCKET" --key "$PARALEAN_S3_ACCESS_KEY" >/dev/null
if [ -z "$PARALEAN_INSTANCE" ]; then
  make_private "$P/garage" "$P/fdb" "$P/run"
  python3 "$here/check-storage-boundary.py" "$P/garage/garage.toml" "$PARALEAN_GARAGE_S3_PORT" "$PARALEAN_FDB_CLUSTER"
else
  make_private "$H" "$H/fdb" "$H/garage" "$H/run"
  for j in $(seq 0 $((PARALEAN_GARAGE_NODES - 1))); do
    make_private "$H/garage/n$j"
    python3 "$here/check-storage-boundary.py" "$H/garage/n$j/garage.toml" "$((PARALEAN_GARAGE_S3_PORT + j))" "$PARALEAN_FDB_CLUSTER"
  done
fi
echo "garage: $PARALEAN_GARAGE_NODES node(s), replication $PARALEAN_GARAGE_REPLICATION, bucket $PARALEAN_S3_BUCKET"

# --- s3-guard: plain S3 passthrough to Garage that refuses every delete.
guard="$here/../target/release/s3-guard"
# Always refresh this small gateway: an older passthrough cannot use Unix sockets.
( cd "$here/.." && cargo build --release -p s3-guard -j 1 )
if ! alive s3-guard; then
  logdir="$H/garage/log"; mkdir -p "$logdir"
  setsid nohup "$guard" --listen "127.0.0.1:$PARALEAN_S3_PORT" --upstream "$upstreams" \
    >> "$logdir/s3-guard.log" 2>&1 < /dev/null &
  echo $! > "$H/run/s3-guard.pid"
fi
for i in $(seq 1 20); do curl -s -o /dev/null "$PARALEAN_S3_ENDPOINT" && break; sleep 0.5; done
echo "s3: $PARALEAN_S3_ENDPOINT (guard) -> $upstreams (garage)"
echo "fdb: $PARALEAN_FDB_CLUSTER"
