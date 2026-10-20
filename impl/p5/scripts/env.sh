# Source this file. P5 owns only this explicitly named service instance.
p5_here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export PARALEAN_INSTANCE="${PARALEAN_INSTANCE:-p5-m-p5}"
case "$PARALEAN_INSTANCE" in
  p5-*) ;;
  *) echo "P5 requires an instance name beginning p5-" >&2; return 2 ;;
esac
[[ "$PARALEAN_INSTANCE" =~ ^[a-zA-Z0-9_-]+$ ]] || return 2
export PARALEAN_P3_PREFIX="${PARALEAN_P5_PREFIX:-/data/home/kirancodes/paralean-${PARALEAN_INSTANCE}-cluster}"
export PARALEAN_P2_PREFIX="$PARALEAN_P3_PREFIX"
export PARALEAN_P3_FDB_PORT="${PARALEAN_P5_FDB_PORT:-5089}"
export PARALEAN_P3_GARAGE_S3_PORT="${PARALEAN_P5_GARAGE_S3_PORT:-18839}"
export PARALEAN_P3_GARAGE_RPC_PORT="${PARALEAN_P5_GARAGE_RPC_PORT:-18840}"
export PARALEAN_P3_GARAGE_ADMIN_PORT="${PARALEAN_P5_GARAGE_ADMIN_PORT:-18841}"
export PARALEAN_P3_S3_PORT="${PARALEAN_P5_S3_PORT:-18833}"
export PARALEAN_VALIDATOR_PORT="${PARALEAN_VALIDATOR_PORT:-18891}"
export PARALEAN_VALIDATOR="${PARALEAN_VALIDATOR:-127.0.0.1:$PARALEAN_VALIDATOR_PORT}"
export PARALEAN_LEAN="${PARALEAN_LEAN:-fork}"
# The compiler is a read-only, pinned installation. Override on other machines.
export PARALEAN_FORK_PREFIX="${PARALEAN_FORK_PREFIX:-/data/home/kirancodes/Documents/code/paralean-fork/.deps/lean4-paralean/build/release/stage1}"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-2}"
. "$p5_here/../../p3/scripts/env.sh"
# Recovery credentials belong to the controller, separate from workers' S3
# credentials. This existing service secret survives deletion of desktop state.
export PARALEAN_P5_RECOVERY_SECRET="${PARALEAN_P5_RECOVERY_SECRET:-${PARALEAN_GARAGE_ADMIN_TOKEN:-}}"
export PARALEAN_PLR="${PARALEAN_PLR:-$PARALEAN_P2_DIR/target/release/plr}"
export PARALEAN_P3_BIN="${PARALEAN_P3_BIN:-$PARALEAN_P2_DIR/target/release/paralean-p3}"
export PARALEAN_P5_BRIDGE="${PARALEAN_P5_BRIDGE:-$PARALEAN_P2_DIR/target/release/paralean-p5-store}"
# Exports must use the unmodified compiler even though capture uses the fork.
export PARALEAN_STOCK_LAKE="${PARALEAN_STOCK_LAKE:-$HOME/.elan/toolchains/leanprover--lean4-nightly---nightly-2026-10-03/bin/lake}"
