#!/usr/bin/env bash
# store.md P2 obligation "killing FoundationDB processes": run stress workers, SIGKILL the
# fdbserver mid-run, restart it with up.sh, let the workers finish, then audit. In-flight
# commits surface as real commit_unknown_result / transaction errors that the workers must
# resolve before proceeding. (The P2 cluster is one process in `single` mode, so a kill is
# an outage, not a fault inside the redundancy mode.)
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
cd "$here/.."
cargo build -q -p paralean-cli || exit 1
bin="$PWD/target/debug/paralean-p2"
export PARALEAN_DEPLOYMENT="killtest-$(date +%s)"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
export PARALEAN_KEYS="$tmp/keys.json"
"$bin" keys init "$PARALEAN_KEYS" --demo --workspaces 4 >/dev/null
pids=()
for w in 0 1 2 3; do
  "$bin" stress --worker $w --ops "${OPS:-120}" --seed $((w + 7)) --fault-p 0.02 > "$tmp/w$w.log" 2>&1 &
  pids+=($!)
done
sleep "${KILL_AFTER:-2}"
# The cluster's own fdbserver: the default cluster's, or process 0 of an instance.
pidfile="$PARALEAN_HOME/run/fdbserver.pid"
[ -n "$PARALEAN_INSTANCE" ] && pidfile="$PARALEAN_HOME/run/fdbserver-0.pid"
fdbpid="$(cat "$pidfile")"
running=0; for p in "${pids[@]}"; do kill -0 "$p" 2>/dev/null && running=$((running + 1)); done
echo "killing fdbserver $fdbpid with $running of ${#pids[@]} workers running"; kill -9 "$fdbpid"
sleep "${DOWN_FOR:-4}"
"$here/up.sh" >/dev/null 2>&1 && echo "fdbserver restarted"
fail=0
for i in "${!pids[@]}"; do
  if wait "${pids[$i]}"; then
    echo "worker $i: ok; real FDB errors resolved: $(grep -o '"real-commit-unknown-result": [0-9]*\|"fdb-retry": [0-9]*' "$tmp/w$i.log" | tr '\n' ' ')"
  else echo "worker $i: FAILED"; cat "$tmp/w$i.log"; fail=1; fi
done
"$bin" audit || fail=1
exit $fail
