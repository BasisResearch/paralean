#!/usr/bin/env bash
# Stop the P2 cluster started by up.sh (the instance named by PARALEAN_INSTANCE, if set).
# Data under $PARALEAN_HOME is kept (GC is disabled; nothing here deletes stored data).
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
H="$PARALEAN_HOME"
if [ -n "$PARALEAN_INSTANCE" ]; then
  names=(s3-guard)
  for f in "$H"/run/garage-*.pid "$H"/run/fdbserver-*.pid "$H"/run/netsplit.pid; do
    [ -f "$f" ] && names+=("$(basename "$f" .pid)")
  done
else
  names=(s3-guard garage fdbserver)
fi
for s in "${names[@]}"; do
  f="$H/run/$s.pid"
  if [ -f "$f" ] && kill -0 "$(cat "$f")" 2>/dev/null; then
    kill -CONT "$(cat "$f")" 2>/dev/null; kill "$(cat "$f")"; echo "stopped $s"
    for i in $(seq 1 20); do kill -0 "$(cat "$f")" 2>/dev/null || break; sleep 0.25; done
  fi
  rm -f "$f"
done
