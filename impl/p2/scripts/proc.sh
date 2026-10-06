#!/usr/bin/env bash
# Start and fault individual processes of an instance cluster (PARALEAN_INSTANCE set; see
# env.sh). Used by up.sh and the fault scripts.
#   proc.sh fdb    start|kill|pause|resume|wipe <i>   fdbserver i (wipe: delete its data dir; must be down)
#   proc.sh garage start|kill|pause|resume|wipe <j>   Garage node j (wipe: delete its data blocks, keep its identity)
#   proc.sh split <i>...                              partition fdbservers i... from the rest (netsplit)
#   proc.sh heal                                      remove the partition
#   proc.sh status                                    which processes are up
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
P="$PARALEAN_P2_PREFIX"
H="$PARALEAN_HOME"
[ -n "$PARALEAN_INSTANCE" ] || { echo "proc.sh works on instances only (set PARALEAN_INSTANCE)" >&2; exit 1; }
mkdir -p "$H/run"
knobs="${PARALEAN_FDB_KNOBS:---knob_min_available_space_ratio=0.002 --knob_min_available_space_ratio_safety_buffer=0.001 --knob_min_available_space=200000000}"

pidf() { echo "$H/run/$1.pid"; }
alive() { [ -f "$(pidf "$1")" ] && kill -0 "$(cat "$(pidf "$1")")" 2>/dev/null; }
sig() { # signal name
  if alive "$2"; then kill "-$1" "$(cat "$(pidf "$2")")"; echo "$1 $2"; else echo "$2 is not running"; fi
}

fdb_start() {
  local i=$1 pub=$((PARALEAN_FDB_PORT + $1)) priv=$((PARALEAN_FDB_PORT + 10 + $1))
  local d="$H/fdb/p$i"
  mkdir -p "$d/data" "$d/log"
  alive "fdbserver-$i" && return 0
  local listen=()
  [ "$PARALEAN_NETSPLIT" = 1 ] && listen=(-l "127.0.0.1:$priv")
  setsid nohup "$P/bin/fdbserver" -p "127.0.0.1:$pub" "${listen[@]}" -C "$PARALEAN_FDB_CLUSTER" \
    -d "$d/data" -L "$d/log" --locality-zoneid "z$i" --locality-machineid "m$i" \
    --cache-memory 256MiB --knob_disable_posix_kernel_aio=1 $knobs \
    >> "$d/log/stdout.log" 2>&1 < /dev/null &
  echo $! > "$(pidf "fdbserver-$i")"
  echo "started fdbserver-$i (127.0.0.1:$pub)"
}

garage_start() {
  local j=$1
  alive "garage-$j" && return 0
  setsid nohup "$P/bin/garage" -c "$H/garage/n$j/garage.toml" server \
    >> "$H/garage/n$j/garage.log" 2>&1 < /dev/null &
  echo $! > "$(pidf "garage-$j")"
  echo "started garage-$j"
}

case "${1:-} ${2:-}" in
  "fdb start") fdb_start "$3" ;;
  "fdb kill") sig KILL "fdbserver-$3" ;;
  "fdb pause") sig STOP "fdbserver-$3" ;;
  "fdb resume") sig CONT "fdbserver-$3" ;;
  "fdb wipe")
    alive "fdbserver-$3" && { echo "fdbserver-$3 is running; kill it first" >&2; exit 1; }
    rm -rf "$H/fdb/p$3/data"; echo "wiped fdbserver-$3 data" ;;
  "garage start") garage_start "$3" ;;
  "garage kill") sig KILL "garage-$3" ;;
  "garage pause") sig STOP "garage-$3" ;;
  "garage resume") sig CONT "garage-$3" ;;
  "garage wipe")
    alive "garage-$3" && { echo "garage-$3 is running; kill it first" >&2; exit 1; }
    rm -rf "$H/garage/n$3/data"; mkdir -p "$H/garage/n$3/data"; echo "wiped garage-$3 data blocks" ;;
  "split "*) shift; echo "$*" > "$H/run/netsplit.state"; echo "isolated fdbservers: $*" ;;
  "heal "*) : > "$H/run/netsplit.state"; echo "healed" ;;
  "status "*)
    for f in "$H"/run/*.pid; do
      n="$(basename "$f" .pid)"
      if alive "$n"; then
        st="$(awk '{print $3}' "/proc/$(cat "$f")/stat" 2>/dev/null)"
        echo "$n up${st:+ ($st)}"
      else echo "$n down"; fi
    done
    [ -f "$H/run/netsplit.state" ] && echo "isolated: $(cat "$H/run/netsplit.state")" ;;
  *) sed -n '2,9p' "$0"; exit 2 ;;
esac
