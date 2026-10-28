#!/usr/bin/env bash
# Source from any directory. Selects only W4-rest's private cluster (w4r-a by default).
w4r_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
export PARALEAN_INSTANCE="${PARALEAN_INSTANCE:-w4r-a}"
case "$PARALEAN_INSTANCE" in
  w4r-a) export PARALEAN_PORT_BASE=32100 ;;
  w4r-b) export PARALEAN_PORT_BASE=32200 ;;
  w4r-c) export PARALEAN_PORT_BASE=32300 ;;
  w4r-d) export PARALEAN_PORT_BASE=32400 ;;
  w4r-*) : "${PARALEAN_PORT_BASE:?set PARALEAN_PORT_BASE for $PARALEAN_INSTANCE}" ;;
  *) echo "w4r-env.sh: refusing instance $PARALEAN_INSTANCE (not w4r-*)" >&2; return 1 ;;
esac
source "$w4r_root/impl/p2/scripts/env.sh"
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-6}"
export TLC_WORKERS="${TLC_WORKERS:-2}" TLC_NEG_WORKERS="${TLC_NEG_WORKERS:-1}" TLC_HEAP="${TLC_HEAP:-4g}"
unset w4r_root
