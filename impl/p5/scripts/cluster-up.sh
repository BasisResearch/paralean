#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
mkdir -p "$PARALEAN_P3_PREFIX"
marker="$PARALEAN_P3_PREFIX/p5-instance"
if [ -e "$marker" ]; then
  [ "$(cat "$marker")" = "$PARALEAN_INSTANCE" ] || { echo "instance ownership mismatch" >&2; exit 2; }
else
  [ ! -d "$PARALEAN_P3_PREFIX/run" ] || { echo "refusing an unowned existing cluster" >&2; exit 2; }
  printf '%s\n' "$PARALEAN_INSTANCE" > "$marker"
fi
# The prefix now exists: create the controller-only recovery secret once.
paralean_p5_recovery_secret_init
[ -f "$PARALEAN_P5_RECOVERY_SECRET_FILE" ] && [ ! -L "$PARALEAN_P5_RECOVERY_SECRET_FILE" ] \
  || { echo "missing private recovery secret $PARALEAN_P5_RECOVERY_SECRET_FILE" >&2; exit 2; }
# Upstream startup uses these variables and this checkout's binaries.
exec "$here/../../p3/scripts/cluster-up.sh"
