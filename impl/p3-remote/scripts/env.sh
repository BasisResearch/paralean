# Environment for P3 transparent workspaces. Source it; do not execute it.
#
# Store: a P2 cluster instance (impl/p2/scripts/up.sh) with its own prefix and ports. The
# defaults are this branch's instance; override PARALEAN_P2_PREFIX and the port variables
# to use another one. Lean: impl/p1 on the Paralean fork (PARALEAN_LEAN=fork) by default.
here_p3r="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export PARALEAN_P3R_ROOT="$(cd "$here_p3r/.." && pwd)"
export PARALEAN_P2_PREFIX="${PARALEAN_P2_PREFIX:-/data/home/kirancodes/paralean-p3-remote-cluster}"
export PARALEAN_FDB_PORT="${PARALEAN_FDB_PORT:-4789}"
export PARALEAN_GARAGE_S3_PORT="${PARALEAN_GARAGE_S3_PORT:-18539}"
export PARALEAN_GARAGE_RPC_PORT="${PARALEAN_GARAGE_RPC_PORT:-18540}"
export PARALEAN_GARAGE_ADMIN_PORT="${PARALEAN_GARAGE_ADMIN_PORT:-18541}"
export PARALEAN_S3_PORT="${PARALEAN_S3_PORT:-18533}"
. "$PARALEAN_P3R_ROOT/../p2/scripts/env.sh"
export PARALEAN_LEAN="${PARALEAN_LEAN:-fork}"
. "$PARALEAN_P3R_ROOT/../p1/scripts/env.sh"
export PARALEAN_PLR="${PARALEAN_PLR:-$PARALEAN_P3R_ROOT/../p2/target/release/plr}"
export PARALEAN_P3_BIN="${PARALEAN_P3_BIN:-$PARALEAN_P3R_ROOT/../p2/target/release/paralean-p3}"
