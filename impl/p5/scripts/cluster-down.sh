#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
[ "$(cat "$PARALEAN_P3_PREFIX/p5-instance")" = "$PARALEAN_INSTANCE" ] || exit 2
# Check PID ownership before using the upstream stop script.
for name in fdbserver garage s3-guard; do
  pidfile="$PARALEAN_P3_PREFIX/run/$name.pid"
  [ -f "$pidfile" ] || continue
  pid="$(cat "$pidfile")"
  [ -e "/proc/$pid/cmdline" ] || continue
  case "$name" in
    fdbserver|garage) expected="$PARALEAN_P3_PREFIX" ;;
    s3-guard) expected="127.0.0.1:$PARALEAN_S3_PORT" ;;
  esac
  tr '\0' '\n' < "/proc/$pid/cmdline" | grep -Fq -- "$expected" || {
    echo "refusing to stop PID $pid: instance ownership mismatch" >&2; exit 2;
  }
done
exec "$here/../../p3/scripts/cluster-down.sh"
