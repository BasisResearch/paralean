# Settings for the P3 control-plane test cluster: its own FoundationDB and Garage instance,
# with its own data directories and ports, running the binaries P2's bootstrap.sh installed.
# Source it; do not execute it. Every value can be overridden from the environment.
here_p3="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export PARALEAN_P3_ROOT="$(cd "$here_p3/.." && pwd)"
export PARALEAN_P2_DIR="$(cd "$PARALEAN_P3_ROOT/../p2" && pwd)"
# Read-only: the shared P2 install (fdbserver, fdbcli, garage, libfdb_c.so).
export PARALEAN_P2_BIN_PREFIX="${PARALEAN_P2_BIN_PREFIX:-/data/home/kirancodes/paralean-p2}"
# This instance's data, logs, pid files and credentials.
export PARALEAN_P3_PREFIX="${PARALEAN_P3_PREFIX:-/data/home/kirancodes/paralean-p3-control-cluster}"

export PARALEAN_FDB_PORT="${PARALEAN_P3_FDB_PORT:-4989}"
export PARALEAN_GARAGE_S3_PORT="${PARALEAN_P3_GARAGE_S3_PORT:-18739}"
export PARALEAN_GARAGE_RPC_PORT="${PARALEAN_P3_GARAGE_RPC_PORT:-18740}"
export PARALEAN_GARAGE_ADMIN_PORT="${PARALEAN_P3_GARAGE_ADMIN_PORT:-18741}"
export PARALEAN_S3_PORT="${PARALEAN_P3_S3_PORT:-18733}"

export PARALEAN_FDB_CLUSTER="$PARALEAN_P3_PREFIX/fdb/fdb.cluster"
export PARALEAN_S3_ENDPOINT="http://127.0.0.1:$PARALEAN_S3_PORT"
export PARALEAN_S3_BUCKET="${PARALEAN_S3_BUCKET:-paralean}"
export PARALEAN_S3_REGION="${PARALEAN_S3_REGION:-garage}"
if [ -f "$PARALEAN_P3_PREFIX/garage/credentials.sh" ]; then
  . "$PARALEAN_P3_PREFIX/garage/credentials.sh"
fi

export PATH="$HOME/.cargo/bin:$PATH"
export LIBRARY_PATH="$PARALEAN_P2_BIN_PREFIX/lib${LIBRARY_PATH:+:$LIBRARY_PATH}"
export LD_LIBRARY_PATH="$PARALEAN_P2_BIN_PREFIX/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

# The Lean side of the validator: impl/p1's binary and its toolchain (impl/p1/scripts/env.sh;
# PARALEAN_LEAN=fork selects the Paralean fork).
. "$PARALEAN_P3_ROOT/../p1/scripts/env.sh"
