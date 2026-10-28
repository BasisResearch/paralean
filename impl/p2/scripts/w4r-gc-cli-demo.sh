#!/usr/bin/env bash
# CLI transcript of the store GC on the private w4r-a instance (fresh deployment, private
# FDB-aware guard, temporary GC key). Usage: bash impl/p2/scripts/w4r-gc-cli-demo.sh > log
set -uo pipefail
root="$(cd "$(dirname "$0")/../../.." && pwd)"
source "$root/impl/p3/scripts/w4r-env.sh"
[[ "$PARALEAN_INSTANCE" == w4r-a ]] || exit 2
bin="$root/impl/p2/target/debug/paralean-p2"
garage() { "$PARALEAN_P2_PREFIX/bin/garage" -c "$PARALEAN_HOME/garage/n0/garage.toml" "$@"; }
dep="cli-gc-$(date +%s)"
key="GK$(head -c 12 /dev/urandom | od -An -tx1 | tr -d ' \n')"
secret="$(head -c 32 /dev/urandom | od -An -tx1 | tr -d ' \n')"
garage key import --yes -n w4r-store-gc-cli "$key" "$secret" >/dev/null
garage bucket allow --read --write "$PARALEAN_S3_BUCKET" --key "$key" >/dev/null
port=$(python3 -c 'import socket; s=socket.socket(); s.bind(("127.0.0.1",0)); print(s.getsockname()[1])')
"$root/impl/p2/target/debug/s3-guard" --listen "127.0.0.1:$port" --upstream "unix:$PARALEAN_GARAGE_S3_SOCKET" \
  --gc-access-key "$key" --gc-fdb-cluster "$PARALEAN_FDB_CLUSTER" --gc-deployment "$dep=$PARALEAN_S3_BUCKET/$dep/" 2>/dev/null &
guard=$!
trap 'kill $guard; garage key delete --yes "$key" >/dev/null' EXIT
sleep 0.5
export PARALEAN_DEPLOYMENT="$dep" PARALEAN_S3_ENDPOINT="http://127.0.0.1:$port"
export PARALEAN_GC_S3_ACCESS_KEY="$key" PARALEAN_GC_S3_SECRET_KEY="$secret"
run() { echo "\$ paralean-p2 $*"; "$bin" "$@" 2>&1 | grep -v "PARALEAN_KEYS not set"; echo; }
echo "deployment $dep, private guard 127.0.0.1:$port (store-GC content deletes for this deployment only)"
f=$(mktemp); echo "an abandoned upload" > "$f"
run assign Cli.Target w0
run publish-demo w0 Cli.Target t1
run put capsule "$f"
run gc sweep
run gc enable
run gc backfill
run gc enable
run gc sweep --grace 1
run gc sweep --grace 1 --delete
run gc status
run audit
rm -f "$f"
