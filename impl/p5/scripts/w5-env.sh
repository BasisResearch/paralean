# Source from any directory. W5 exclusively owns this local instance.
w5_repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
export PARALEAN_INSTANCE=p5-w5
export PARALEAN_P5_PREFIX="$w5_repo/.runs/w5/cluster"
export PARALEAN_P5_FDB_PORT=23589
export PARALEAN_P5_GARAGE_S3_PORT=23639
export PARALEAN_P5_GARAGE_RPC_PORT=23640
export PARALEAN_P5_GARAGE_ADMIN_PORT=23641
export PARALEAN_P5_S3_PORT=23633
export PARALEAN_VALIDATOR_PORT=23691
export PARALEAN_FORK_PREFIX="${PARALEAN_FORK_PREFIX:-$w5_repo/.deps/lean4-paralean/build/release/stage1}"
export PARALEAN_P5_BRIDGE="$w5_repo/impl/p2/target/release/paralean-p5-store"
export PARALEAN_BIN="$w5_repo/impl/p1/.lake/build/bin/paralean"
export PARALEAN_LIB="$w5_repo/impl/p1/.lake/build/lib/lean"
source "$w5_repo/impl/p5/scripts/env.sh"
