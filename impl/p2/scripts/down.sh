#!/usr/bin/env bash
# Stop the P2 cluster started by up.sh. Data under $PARALEAN_P2_PREFIX is kept
# (GC is disabled; nothing here deletes stored data).
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
P="$PARALEAN_P2_PREFIX"
for s in s3-guard garage fdbserver; do
  f="$P/run/$s.pid"
  if [ -f "$f" ] && kill -0 "$(cat "$f")" 2>/dev/null; then
    kill "$(cat "$f")"; echo "stopped $s"
    for i in $(seq 1 20); do kill -0 "$(cat "$f")" 2>/dev/null || break; sleep 0.25; done
  fi
  rm -f "$f"
done
