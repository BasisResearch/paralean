# Source this before running this workstream's cluster or tests.
# These defaults never address another manager's services.
export PARALEAN_P3_PREFIX="${PARALEAN_P3_PREFIX:-/data/home/kirancodes/paralean-m-targets-cluster}"
export PARALEAN_P3_FDB_PORT="${PARALEAN_P3_FDB_PORT:-5189}"
export PARALEAN_P3_GARAGE_S3_PORT="${PARALEAN_P3_GARAGE_S3_PORT:-18939}"
export PARALEAN_P3_GARAGE_RPC_PORT="${PARALEAN_P3_GARAGE_RPC_PORT:-18940}"
export PARALEAN_P3_GARAGE_ADMIN_PORT="${PARALEAN_P3_GARAGE_ADMIN_PORT:-18941}"
export PARALEAN_P3_S3_PORT="${PARALEAN_P3_S3_PORT:-18933}"
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-2}"
export PARALEAN_TEST_THREADS="${PARALEAN_TEST_THREADS:-1}"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
. "$(dirname "${BASH_SOURCE[0]}")/env.sh"
