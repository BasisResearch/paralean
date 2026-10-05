#!/usr/bin/env bash
# Track B: transparent workspaces. Two working copies (alice = A, bob = B) of one shared
# codebase {A.lean, B.lean, Shared.lean}; B→A→B through remote%; concurrent publications
# exchanged in both orders; projection hashes; standalone elaboration; git projection.
set -u
source "$(dirname "$0")/env.sh"
require_bin
here="$P1_DIR"
W="${1:-$PARALEAN_RUNS/transparent}"
export PARALEAN_RECEIPT_KEY="p1-demo-validator-key" PARALEAN_VISIBILITY=1
P="$PARALEAN_BIN"
rm -rf "$W"; mkdir -p "$W"
A="$W/alice"; B="$W/bob"
cp_() { PARALEAN_STORE="$1/store" PARALEAN_REMOTE_LOG="$W/remote.log" "$P" "${@:2}"; }
"$P" copy-init --copy "$A" --author alice
"$P" copy-init --copy "$B" --author bob

echo "### 1. bob writes helper_b in B.lean and publishes"
cat > "$B/work/B.lean" <<'L'
def Cross.helper_b (n : Nat) : Nat := n + 1
L
cp_ "$B" copy-publish --copy "$B" B.lean

echo "### 2. alice pulls; writes helper (uses bob's helper_b by name) in A.lean; publishes"
cp_ "$A" copy-pull --copy "$A" --from "$B"
cat > "$A/work/A.lean" <<'L'
@[simp] theorem Cross.helper (n : Nat) : Cross.helper_b n = n + 1 := rfl
L
cp_ "$A" copy-publish --copy "$A" A.lean

echo "### 3. bob pulls; appends helper_c (uses alice's helper) to B.lean; publishes"
cp_ "$B" copy-pull --copy "$B" --from "$A"
cat >> "$B/work/B.lean" <<'L'

theorem Cross.helper_c (n : Nat) : Cross.helper_b (Cross.helper_b n) = n + 2 := by
  rw [Cross.helper n]; rfl

-- bob's unfinished draft: incomplete, so it is never published
theorem Cross.wip (n : Nat) : n + 0 = n := by
  sorry
L
cp_ "$B" copy-publish --copy "$B" B.lean
cp_ "$A" copy-pull --copy "$A" --from "$B"

echo "### 4. projections after exchange"
for c in "$A" "$B"; do echo "$(basename "$c"):"; cp_ "$c" copy-hash --copy "$c" A.lean B.lean; done

echo "### 5. concurrent publications at the start of Shared.lean, exchanged in both orders"
for order in AB BA; do
  for who in alice bob; do "$P" copy-init --copy "$W/$order-$who" --author "$who"; done
  cat > "$W/$order-alice/work/Shared.lean" <<'L'
theorem Shared.from_alice : 1 + 1 = 2 := rfl
L
  cat > "$W/$order-bob/work/Shared.lean" <<'L'
theorem Shared.from_bob : 2 + 2 = 4 := rfl
L
  cp_ "$W/$order-alice" copy-publish --copy "$W/$order-alice" Shared.lean >/dev/null
  cp_ "$W/$order-bob" copy-publish --copy "$W/$order-bob" Shared.lean >/dev/null
  if [ "$order" = AB ]; then
    cp_ "$W/$order-bob" copy-pull --copy "$W/$order-bob" --from "$W/$order-alice" >/dev/null
    cp_ "$W/$order-alice" copy-pull --copy "$W/$order-alice" --from "$W/$order-bob" >/dev/null
  else
    cp_ "$W/$order-alice" copy-pull --copy "$W/$order-alice" --from "$W/$order-bob" >/dev/null
    cp_ "$W/$order-bob" copy-pull --copy "$W/$order-bob" --from "$W/$order-alice" >/dev/null
  fi
  for who in alice bob; do
    echo "$order $who $(cp_ "$W/$order-$who" copy-hash --copy "$W/$order-$who" Shared.lean)"
  done
done

echo "### 6. standalone elaboration of every projection file in both copies (remote mode)"
for c in "$A" "$B"; do for f in A.lean B.lean; do
  rm -rf "$W/elab-store"
  t0=$(python3 -c 'import time; print(time.time())')
  env PARALEAN_STORE="$c/store" PARALEAN_REMOTE_LOG="$W/remote-elab.log" \
    "$P" capture --store "$W/elab-store" --ws check --root "$c/work" --remote 1 "$f" 2>&1 | grep -E "=>|reject"
  python3 -c "import time; print('  time %.2f s' % (time.time() - $t0))"
done; done

echo "### 7. git projection (bob's copy)"
git -C "$B/work" log --format='%h %an: %s' ; echo "-- git diff in bob's copy (his drafts only):"; git -C "$B/work" diff --stat; git -C "$B/work" diff | head -20
echo "### 8. bob's working B.lean"; cat "$B/work/B.lean"
echo "### 9. export from alice's store"
"$P" export --store "$A/store" --out "$W/export" | tail -3
