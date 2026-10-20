# Source this file; all mutable service state belongs to m-p4.
p4_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
export PARALEAN_INSTANCE=m-p4
export PARALEAN_P2_PREFIX="$p4_root/.runs/m-p4-cluster"
export PARALEAN_FDB_PORT=4799
export PARALEAN_GARAGE_S3_PORT=18639
export PARALEAN_GARAGE_RPC_PORT=18640
export PARALEAN_GARAGE_ADMIN_PORT=18641
export PARALEAN_S3_PORT=18633
export PARALEAN_LEAN=fork
export PARALEAN_JOBS=2
. "$p4_root/impl/p3-remote/scripts/env.sh"
