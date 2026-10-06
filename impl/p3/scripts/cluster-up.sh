#!/usr/bin/env bash
# Start this agent's own cluster instance for the P3 tests: one fdbserver (ssd), one Garage
# node (replication 1, consistent mode) and an s3-guard gateway, with data under
# $PARALEAN_P3_PREFIX and the ports of scripts/env.sh. It uses the binaries of P2's
# bootstrap.sh read-only and never touches another instance. Idempotent.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
B="$PARALEAN_P2_BIN_PREFIX/bin"
P="$PARALEAN_P3_PREFIX"
[ -x "$B/fdbserver" ] && [ -x "$B/garage" ] || { echo "no P2 install at $PARALEAN_P2_BIN_PREFIX (impl/p2/scripts/bootstrap.sh)" >&2; exit 1; }
mkdir -p "$P"/{run,fdb/data,fdb/log,garage/meta,garage/data,garage/log}
alive() { [ -f "$P/run/$1.pid" ] && kill -0 "$(cat "$P/run/$1.pid")" 2>/dev/null; }

knobs="--knob_min_available_space_ratio=0.002 --knob_min_available_space_ratio_safety_buffer=0.001 --knob_min_available_space=200000000"
for port in "$PARALEAN_FDB_PORT" "$PARALEAN_GARAGE_S3_PORT" "$PARALEAN_GARAGE_RPC_PORT" "$PARALEAN_GARAGE_ADMIN_PORT" "$PARALEAN_S3_PORT"; do
  # A port in use by a process this instance did not start belongs to someone else.
  if ss -ltn | awk '{print $4}' | grep -q ":$port\$" && ! alive fdbserver && ! alive garage && ! alive s3-guard; then
    echo "port $port is in use by another process; set PARALEAN_P3_*_PORT (scripts/env.sh)" >&2; exit 1
  fi
done
[ -f "$PARALEAN_FDB_CLUSTER" ] || echo "paralean:p3c$(head -c 6 /dev/urandom | od -An -tx1 | tr -d ' \n')@127.0.0.1:$PARALEAN_FDB_PORT" > "$PARALEAN_FDB_CLUSTER"
if ! alive fdbserver; then
  setsid nohup "$B/fdbserver" -p "127.0.0.1:$PARALEAN_FDB_PORT" -C "$PARALEAN_FDB_CLUSTER" \
    -d "$P/fdb/data" -L "$P/fdb/log" --knob_disable_posix_kernel_aio=1 $knobs \
    > "$P/fdb/log/stdout.log" 2>&1 < /dev/null &
  echo $! > "$P/run/fdbserver.pid"
fi
fdbcli() { "$B/fdbcli" -C "$PARALEAN_FDB_CLUSTER" "$@"; }
if [ ! -f "$P/fdb/.configured" ]; then
  fdbcli --timeout 60 --exec "configure new single ssd"
  touch "$P/fdb/.configured"
fi
for i in $(seq 1 60); do
  case "$(fdbcli --timeout 5 --exec "status minimal" 2>/dev/null || true)" in *"The database is available"*) break ;; esac
  sleep 1
done
fdbcli --timeout 5 --exec "status minimal"

if [ ! -f "$P/garage/credentials.sh" ]; then
  hex() { head -c "$1" /dev/urandom | od -An -tx1 | tr -d ' \n'; }
  ( umask 077; cat > "$P/garage/credentials.sh" <<CREDS
export PARALEAN_GARAGE_RPC_SECRET=$(hex 32)
export PARALEAN_GARAGE_ADMIN_TOKEN=$(hex 32)
export PARALEAN_S3_ACCESS_KEY=GK$(hex 12)
export PARALEAN_S3_SECRET_KEY=$(hex 32)
CREDS
  )
fi
. "$P/garage/credentials.sh"
cat > "$P/garage/garage.toml" <<TOML
metadata_dir = "$P/garage/meta"
data_dir = "$P/garage/data"
db_engine = "lmdb"
metadata_fsync = true
data_fsync = true
replication_factor = 1
consistency_mode = "consistent"
rpc_bind_addr = "127.0.0.1:$PARALEAN_GARAGE_RPC_PORT"
rpc_public_addr = "127.0.0.1:$PARALEAN_GARAGE_RPC_PORT"
rpc_secret = "$PARALEAN_GARAGE_RPC_SECRET"

[s3_api]
s3_region = "$PARALEAN_S3_REGION"
api_bind_addr = "127.0.0.1:$PARALEAN_GARAGE_S3_PORT"
root_domain = ".s3.localhost"

[admin]
api_bind_addr = "127.0.0.1:$PARALEAN_GARAGE_ADMIN_PORT"
admin_token = "$PARALEAN_GARAGE_ADMIN_TOKEN"
TOML
garage() { "$B/garage" -c "$P/garage/garage.toml" "$@"; }
if ! alive garage; then
  setsid nohup "$B/garage" -c "$P/garage/garage.toml" server > "$P/garage/log/garage.log" 2>&1 < /dev/null &
  echo $! > "$P/run/garage.pid"
fi
for i in $(seq 1 30); do garage status >/dev/null 2>&1 && break; sleep 1; done
node="$(garage status 2>/dev/null | awk -v a="127.0.0.1:$PARALEAN_GARAGE_RPC_PORT" '$3==a{print $1}')"
if garage status 2>/dev/null | grep -q "NO ROLE ASSIGNED"; then
  garage layout assign -z dc1 -c 20G "$node" >/dev/null
  garage layout apply --version 1 >/dev/null
fi
garage bucket info "$PARALEAN_S3_BUCKET" >/dev/null 2>&1 || garage bucket create "$PARALEAN_S3_BUCKET" >/dev/null
garage key info "$PARALEAN_S3_ACCESS_KEY" >/dev/null 2>&1 || \
  garage key import --yes -n paralean-app "$PARALEAN_S3_ACCESS_KEY" "$PARALEAN_S3_SECRET_KEY" >/dev/null
garage bucket allow --read --write "$PARALEAN_S3_BUCKET" --key "$PARALEAN_S3_ACCESS_KEY" >/dev/null
echo "garage: node $node, bucket $PARALEAN_S3_BUCKET"

guard="$PARALEAN_P2_DIR/target/release/s3-guard"
[ -x "$guard" ] || ( cd "$PARALEAN_P2_DIR" && cargo build --release -p s3-guard )
if ! alive s3-guard; then
  setsid nohup "$guard" --listen "127.0.0.1:$PARALEAN_S3_PORT" --upstream "127.0.0.1:$PARALEAN_GARAGE_S3_PORT" \
    > "$P/garage/log/s3-guard.log" 2>&1 < /dev/null &
  echo $! > "$P/run/s3-guard.pid"
fi
for i in $(seq 1 20); do curl -s -o /dev/null "$PARALEAN_S3_ENDPOINT" && break; sleep 0.5; done
echo "s3: $PARALEAN_S3_ENDPOINT (guard) -> 127.0.0.1:$PARALEAN_GARAGE_S3_PORT (garage)"
echo "fdb: $PARALEAN_FDB_CLUSTER ($(cat "$PARALEAN_FDB_CLUSTER"))"
