#!/usr/bin/env bash
# Run the P2 test suite against the cluster started by up.sh (PARALEAN_INSTANCE selects an
# instance). PARALEAN_PEER_INSTANCE names a second, independent instance: the anti-entropy
# tests then put their second deployment on its FoundationDB and Garage (PARALEAN_PEER_*).
# Extra arguments go to `cargo test` (e.g. `scripts/test.sh --test fixtures`).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
if [ -n "${PARALEAN_PEER_INSTANCE:-}" ]; then
  eval "$(PARALEAN_INSTANCE="$PARALEAN_PEER_INSTANCE" bash -c '. "$1/env.sh"
    for v in FDB_CLUSTER S3_ENDPOINT S3_BUCKET S3_REGION S3_ACCESS_KEY S3_SECRET_KEY; do
      eval "printf \"export PARALEAN_PEER_%s=%q\n\" $v \"\$PARALEAN_$v\""
    done' _ "$here")"
  [ "$PARALEAN_PEER_FDB_CLUSTER" != "$PARALEAN_FDB_CLUSTER" ] || { echo "peer instance is this instance" >&2; exit 1; }
fi
cd "$here/.."
exec cargo test --workspace "$@"
