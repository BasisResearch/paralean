#!/usr/bin/env bash
# Forged `remote%` uses must fail with an error (never a sorry). Uses alice's copy from
# scripts/run-transparent.sh.
set -u
source "$(dirname "$0")/env.sh"
require_bin
here="$P1_DIR"
W="${1:-$PARALEAN_RUNS/transparent}"; A="$W/alice"
[ -d "$A/store" ] || die "no transparent-workspace run at $W; run scripts/run-transparent.sh first"
P="$PARALEAN_BIN"
F="$W/forgery"; rm -rf "$F"; mkdir -p "$F"
pid=$(python3 -c "
import json,glob
for f in glob.glob('$A/store/meta/*.json'):
    g=json.load(open(f))
    if g['publicNames']==[['Cross','helper']]: print(g['gid'])")
run() { # name, key, file contents
  printf '%s\n' "$3" > "$F/$1.lean"
  out=$(PARALEAN_STORE="$A/store" PARALEAN_RECEIPT_KEY="$2" "$P" capture --store "$F/s-$1" --ws x --root "$F" --remote 1 "$1.lean" 2>&1)
  if echo "$out" | grep -q "\[reject"; then r="REJECTED"; else r="ACCEPTED"; fi
  echo "$1: $r — $(echo "$out" | grep -m1 "\[reject" | sed 's/.*error[^:]*: //' | cut -c1-150)"
}
K="p1-demo-validator-key"
run genuine "$K" "@[simp] theorem Cross.helper (n : Nat) : Cross.helper_b n = n + 1 := remote% \"$pid\""
run unknown_id "$K" "theorem Cross.claim : 1 = 2 := remote% \"$(printf '0%.0s' {1..64})\""
run edited_statement "$K" "@[simp] theorem Cross.helper (n : Nat) : Cross.helper_b n = n + 2 := remote% \"$pid\""
run other_name "$K" "@[simp] theorem Cross.helper2 (n : Nat) : Cross.helper_b n = n + 1 := remote% \"$pid\""
run in_term "$K" "theorem Cross.t (n : Nat) : Cross.helper_b n = n + 1 := by exact remote% \"$pid\""
run wrong_key "not-the-validator" "@[simp] theorem Cross.helper (n : Nat) : Cross.helper_b n = n + 1 := remote% \"$pid\""
mv "$A/store/receipts/$pid.json" "$F/receipt.bak"
run no_receipt "$K" "@[simp] theorem Cross.helper (n : Nat) : Cross.helper_b n = n + 1 := remote% \"$pid\""
mv "$F/receipt.bak" "$A/store/receipts/$pid.json"
# a different local definition of the dependency: the pinned version must not be rebound
run conflicting_local_dep "$K" "def Cross.helper_b (n : Nat) : Nat := n + 2
@[simp] theorem Cross.helper (n : Nat) : Cross.helper_b n = n + 1 := remote% \"$pid\""
# byte-identical header, but placed in another namespace: it would declare Foo.Cross.helper
run wrong_namespace "$K" "namespace Foo
@[simp] theorem Cross.helper (n : Nat) : Cross.helper_b n = n + 1 := remote% \"$pid\"
end Foo"
# byte-identical header whose `+` means something else here (local instance)
run shadowed_meaning "$K" "local instance (priority := high) : HAdd Nat Nat Nat := ⟨Nat.mul⟩
@[simp] theorem Cross.helper (n : Nat) : Cross.helper_b n = n + 1 := remote% \"$pid\""
