#!/usr/bin/env bash
# Own sshd, keys and roots; requires an installed user-space-capable OpenSSH.
set -euo pipefail
repo="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$repo"
source impl/p5/scripts/w5-env.sh
export LEAN_PARALEAN=1
export LEAN_PATH="$PARALEAN_LIB${LEAN_PATH:+:$LEAN_PATH}"
mkdir -p .runs
run="$(mktemp -d "$repo/.runs/w5-ssh-XXXXXX")"
port="${W5_SSH_PORT:-22956}"
sshd_bin="${W5_SSHD:-/usr/sbin/sshd}"
ssh-keygen -q -t ed25519 -N '' -f "$run/client"
ssh-keygen -q -t ed25519 -N '' -f "$run/host"
cp "$run/client.pub" "$run/authorized_keys"
chmod 600 "$run/authorized_keys"
printf '[127.0.0.1]:%s %s\n' "$port" "$(cat "$run/host.pub")" > "$run/known_hosts"
cat > "$run/sshd_config" <<EOF
Port $port
ListenAddress 127.0.0.1
HostKey $run/host
PidFile $run/sshd.pid
AuthorizedKeysFile $run/authorized_keys
StrictModes yes
PasswordAuthentication no
KbdInteractiveAuthentication no
UsePAM no
AllowUsers $(id -un)
Subsystem sftp internal-sftp
EOF
"$sshd_bin" -D -e -f "$run/sshd_config" > "$run/sshd.log" 2>&1 &
daemon_pid=$!
trap 'kill "$daemon_pid" 2>/dev/null || true; wait "$daemon_pid" 2>/dev/null || true' EXIT
for _ in $(seq 1 30); do
  kill -0 "$daemon_pid" || { cat "$run/sshd.log"; exit 1; }
  if ssh -p "$port" -i "$run/client" -o IdentitiesOnly=yes -o BatchMode=yes \
       -o StrictHostKeyChecking=yes -o "UserKnownHostsFile=$run/known_hosts" \
       127.0.0.1 true 2>/dev/null; then break; fi
  sleep 0.1
done
for delay in 0 40; do
  python3 impl/p4/tests/ssh_gate.py --port "$port" --key "$run/client" \
    --known-hosts "$run/known_hosts" --lean "$PARALEAN_FORK_PREFIX/bin/lean" \
    --delay-ms "$delay" --samples "${W5_SSH_SAMPLES:-10}" \
    --run-dir "$run/delay-$delay" --output "$run/delay-$delay.json"
done
echo "SSH evidence: $run/delay-{0,40}.json"
