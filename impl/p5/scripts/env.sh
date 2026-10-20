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
export PARALEAN_FORK_PREFIX="${PARALEAN_FORK_PREFIX:-/data/home/kirancodes/Documents/code/paralean-m-p4/.deps/lean4-paralean/build/release/stage1}"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-2}"
. "$p5_here/../../p3/scripts/env.sh"
# Recovery credentials belong to the controller, separate from workers' S3
# credentials and from the Garage administration token. The controller reads a
# random secret from an owner-only file kept with the cluster, so it survives
# deletion of desktop state; it refuses a missing, shared or non-private secret.
export PARALEAN_P5_RECOVERY_SECRET_FILE="${PARALEAN_P5_RECOVERY_SECRET_FILE:-$PARALEAN_P3_PREFIX/p5-recovery-secret}"
# Create the secret once, without replacing any existing name (noclobber uses O_EXCL).
paralean_p5_recovery_secret_init() {
  [ -d "$(dirname "$PARALEAN_P5_RECOVERY_SECRET_FILE")" ] || return 0
  if [ -e "$PARALEAN_P5_RECOVERY_SECRET_FILE" ] || [ -L "$PARALEAN_P5_RECOVERY_SECRET_FILE" ]; then
    return 0
  fi
  ( umask 077; set -o noclobber
    od -An -tx1 -N32 /dev/urandom | tr -d ' \n' > "$PARALEAN_P5_RECOVERY_SECRET_FILE" ) 2>/dev/null \
    || echo "warning: could not create $PARALEAN_P5_RECOVERY_SECRET_FILE" >&2
  return 0
}
paralean_p5_recovery_secret_init
# An older shell may still carry the admin-token-derived value; the controller
# would refuse it, so drop it unless the operator set a separate secret.
if [ -n "${PARALEAN_P5_RECOVERY_SECRET:-}" ] && [ "${PARALEAN_P5_RECOVERY_SECRET}" = "${PARALEAN_GARAGE_ADMIN_TOKEN:-}" ]; then
  unset PARALEAN_P5_RECOVERY_SECRET
fi
export PARALEAN_PLR="${PARALEAN_PLR:-$PARALEAN_P2_DIR/target/release/plr}"
export PARALEAN_P3_BIN="${PARALEAN_P3_BIN:-$PARALEAN_P2_DIR/target/release/paralean-p3}"
export PARALEAN_P5_BRIDGE="${PARALEAN_P5_BRIDGE:-$PARALEAN_P2_DIR/target/release/paralean-p5-store}"
# Exports must use the unmodified compiler even though capture uses the fork.
export PARALEAN_STOCK_LAKE="${PARALEAN_STOCK_LAKE:-$HOME/.elan/toolchains/leanprover--lean4-nightly---nightly-2026-10-03/bin/lake}"
