#!/usr/bin/env bash
# Source from any directory. This selects only W4's isolated cluster.
w4_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
export PARALEAN_INSTANCE=w4-scale
export PARALEAN_PORT_BASE=29500
source "$w4_root/impl/p2/scripts/env.sh"
export CARGO_BUILD_JOBS=1
export TLC_WORKERS=1 TLC_NEG_WORKERS=1 TLC_HEAP=4g
unset w4_root
