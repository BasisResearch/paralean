#!/usr/bin/env bash
# Install FoundationDB 7.3 (server, cli, client library) and Garage (S3-compatible
# payload store) in user space under $PARALEAN_P2_PREFIX, plus rustup if missing.
# Nothing is installed system-wide and sudo is never used. Idempotent.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
P="$PARALEAN_P2_PREFIX"
mkdir -p "$P"/{dl,bin,lib,fdb/data,fdb/log,run}

fetch() { # url dest
  [ -s "$2" ] || curl -fsSL --retry 3 -o "$2.part" "$1" && { [ -s "$2" ] || mv "$2.part" "$2"; }
}

# --- FoundationDB: release binaries, each checked against its published SHA-256.
fdl="$P/dl/foundationdb-$FDB_VERSION"; mkdir -p "$fdl"
base="https://github.com/apple/foundationdb/releases/download/$FDB_VERSION"
for f in fdbserver.x86_64 fdbcli.x86_64 libfdb_c.x86_64.so; do
  fetch "$base/$f" "$fdl/$f"
  fetch "$base/$f.sha256" "$fdl/$f.sha256"
  want="$(awk '{print $1}' "$fdl/$f.sha256")"
  got="$(sha256sum "$fdl/$f" | awk '{print $1}')"
  if [ "$want" != "$got" ]; then echo "checksum mismatch for $f" >&2; rm -f "$fdl/$f"; exit 1; fi
done
install -m 0755 "$fdl/fdbserver.x86_64" "$P/bin/fdbserver"
install -m 0755 "$fdl/fdbcli.x86_64" "$P/bin/fdbcli"
install -m 0755 "$fdl/libfdb_c.x86_64.so" "$P/lib/libfdb_c.so"
"$P/bin/fdbserver" --version | head -1

# --- Garage (AGPL-3.0), single static binary, pinned by SHA-256.
gdl="$P/dl/garage-$GARAGE_VERSION"; mkdir -p "$gdl"
fetch "https://garagehq.deuxfleurs.fr/_releases/v$GARAGE_VERSION/x86_64-unknown-linux-musl/garage" "$gdl/garage"
got="$(sha256sum "$gdl/garage" | awk '{print $1}')"
if [ "$got" != "$GARAGE_SHA256" ]; then echo "checksum mismatch for garage ($got)" >&2; rm -f "$gdl/garage"; exit 1; fi
install -m 0755 "$gdl/garage" "$P/bin/garage"
"$P/bin/garage" --version | head -1

# --- Garage secrets and the application key. The key gets read and write on the bucket;
# Garage has no deny-delete permission or bucket policy, so deletes are refused by the
# s3-guard gateway that up.sh starts in front of Garage (clients only see the gateway).
mkdir -p "$P/garage/meta" "$P/garage/data" "$P/garage/log"
if [ ! -f "$P/garage/credentials.sh" ]; then
  hex() { head -c "$1" /dev/urandom | od -An -tx1 | tr -d ' \n'; }
  umask 077
  cat > "$P/garage/credentials.sh" <<CREDS
export PARALEAN_GARAGE_RPC_SECRET=$(hex 32)
export PARALEAN_GARAGE_ADMIN_TOKEN=$(hex 32)
export PARALEAN_S3_ACCESS_KEY=GK$(hex 12)
export PARALEAN_S3_SECRET_KEY=$(hex 32)
CREDS
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

# --- Rust toolchain.
if ! command -v cargo >/dev/null 2>&1; then
  curl -fsSL https://sh.rustup.rs | sh -s -- -y --profile minimal
fi
cargo --version
# --- Build the s3-guard gateway (release) so up.sh can start it.
( cd "$here/.." && cargo build --release -p s3-guard )
echo "bootstrap done: $P"
