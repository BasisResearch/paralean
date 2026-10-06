#!/usr/bin/env bash
# Start the single-machine P2 cluster: one fdbserver (ssd engine by default, set
# PARALEAN_FDB_ENGINE=memory for memory mode), one Garage node (replication factor 1,
# consistent mode) and the s3-guard gateway that refuses deletes. Idempotent.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
P="$PARALEAN_P2_PREFIX"
engine="${PARALEAN_FDB_ENGINE:-ssd}"
[ -x "$P/bin/fdbserver" ] && [ -x "$P/bin/garage" ] || { echo "run bootstrap.sh first" >&2; exit 1; }

alive() { [ -f "$P/run/$1.pid" ] && kill -0 "$(cat "$P/run/$1.pid")" 2>/dev/null; }

# --- FoundationDB
mkdir -p "$P/fdb/data" "$P/fdb/log"
[ -f "$PARALEAN_FDB_CLUSTER" ] || echo "paralean:p2$(head -c 6 /dev/urandom | od -An -tx1 | tr -d ' \n')@127.0.0.1:$PARALEAN_FDB_PORT" > "$PARALEAN_FDB_CLUSTER"
if ! alive fdbserver; then
  setsid nohup "$P/bin/fdbserver" -p "127.0.0.1:$PARALEAN_FDB_PORT" -C "$PARALEAN_FDB_CLUSTER" \
    -d "$P/fdb/data" -L "$P/fdb/log" --knob_disable_posix_kernel_aio=1 \
    > "$P/fdb/log/stdout.log" 2>&1 < /dev/null &
  echo $! > "$P/run/fdbserver.pid"
fi
fdbcli() { "$P/bin/fdbcli" -C "$PARALEAN_FDB_CLUSTER" --timeout 10 "$@"; }
for i in $(seq 1 30); do
  if fdbcli --exec "status minimal" 2>/dev/null | grep -q "The database is available"; then break; fi
  if fdbcli --exec "status minimal" 2>/dev/null | grep -q "unavailable\|no database"; then
    # First start: create the database.
    fdbcli --exec "configure new single $engine" >/dev/null 2>&1 || true
  fi
  sleep 1
done
fdbcli --exec "status minimal"

# --- Garage
if ! alive garage; then
  setsid nohup "$P/bin/garage" -c "$P/garage/garage.toml" server \
    > "$P/garage/log/garage.log" 2>&1 < /dev/null &
  echo $! > "$P/run/garage.pid"
fi
garage() { "$P/bin/garage" -c "$P/garage/garage.toml" "$@"; }
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

# --- s3-guard: plain S3 passthrough to Garage that refuses every delete.
guard="$here/../target/release/s3-guard"
[ -x "$guard" ] || ( cd "$here/.." && cargo build --release -p s3-guard )
if ! alive s3-guard; then
  setsid nohup "$guard" --listen "127.0.0.1:$PARALEAN_S3_PORT" \
    --upstream "127.0.0.1:$PARALEAN_GARAGE_S3_PORT" \
    > "$P/garage/log/s3-guard.log" 2>&1 < /dev/null &
  echo $! > "$P/run/s3-guard.pid"
fi
for i in $(seq 1 20); do curl -s -o /dev/null "$PARALEAN_S3_ENDPOINT" && break; sleep 0.5; done
echo "s3: $PARALEAN_S3_ENDPOINT (guard) -> 127.0.0.1:$PARALEAN_GARAGE_S3_PORT (garage)"
echo "fdb: $PARALEAN_FDB_CLUSTER ($(cat "$PARALEAN_FDB_CLUSTER"))"
