#!/usr/bin/env bash
# Track B, part 2: (A) drafts with namespace blocks + draft re-placement after publishing;
# (B) concurrent unrelated declarations with the same name (rule 4), exchanged in both
# orders; renamed projections identical; uses renamed; standalone elaboration; export.
set -u
source "$(dirname "$0")/env.sh"
require_bin
here="$P1_DIR"
W="${1:-$PARALEAN_RUNS/transparent2}"
export PARALEAN_RECEIPT_KEY="p1-demo-validator-key" PARALEAN_VISIBILITY=1
P="$PARALEAN_BIN"
rm -rf "$W"; mkdir -p "$W"
cp_() { PARALEAN_STORE="$1/store" "$P" "${@:2}"; }
elab() { rm -rf "$W/es"; PARALEAN_STORE="$1/store" "$P" capture --store "$W/es" --ws check --root "$1/work" --remote 1 "$2" 2>&1 | grep -E "=>|\[reject" | cut -c1-200; }

echo "### A. namespace blocks in drafts, draft re-placement"
A="$W/alice"; B="$W/bob"
"$P" copy-init --copy "$A" --author alice >/dev/null; "$P" copy-init --copy "$B" --author bob >/dev/null
cat > "$B/work/B.lean" <<'L'
namespace Cross
def helper_b (n : Nat) : Nat := n + 1
end Cross
L
cp_ "$B" copy-publish --copy "$B" B.lean | grep -E "published|reject"
cp_ "$A" copy-pull --copy "$A" --from "$B" >/dev/null
cat > "$A/work/A.lean" <<'L'
namespace Cross
@[simp] theorem helper (n : Nat) : helper_b n = n + 1 := rfl
end Cross
L
cp_ "$A" copy-publish --copy "$A" A.lean | grep -E "published|reject"
cp_ "$B" copy-pull --copy "$B" --from "$A" >/dev/null
cat >> "$B/work/B.lean" <<'L'

namespace Cross
theorem helper_c (n : Nat) : helper_b (helper_b n) = n + 2 := by
  rw [helper n]; rfl

-- unfinished: stays a draft, and must stay right after helper_c
theorem wip (n : Nat) : n + 0 = n := by
  sorry
end Cross
L
cp_ "$B" copy-publish --copy "$B" B.lean | grep -E "published|reject"
cp_ "$A" copy-pull --copy "$A" --from "$B" >/dev/null
echo "-- bob's working B.lean:"; cat "$B/work/B.lean"
echo "-- standalone elaboration of bob's working B.lean (drafts included):"; elab "$B" B.lean
for c in "$A" "$B"; do echo "$(basename "$c"): $(cp_ "$c" copy-hash --copy "$c" A.lean B.lean | tr '\n' ' ')"; done

echo "### B. concurrent same-name declarations (rule 4), both exchange orders"
for order in AB BA; do
  a="$W/$order-alice"; b="$W/$order-bob"
  "$P" copy-init --copy "$a" --author alice >/dev/null; "$P" copy-init --copy "$b" --author bob >/dev/null
  printf 'theorem Shared.dup : 1 + 1 = 2 := rfl\n' > "$a/work/Shared.lean"
  printf 'theorem Shared.dup : 2 + 2 = 4 := rfl\ntheorem Shared.use_dup : 2 + 2 = 4 := Shared.dup\n' > "$b/work/Shared.lean"
  cp_ "$a" copy-publish --copy "$a" Shared.lean >/dev/null
  cp_ "$b" copy-publish --copy "$b" Shared.lean >/dev/null
  if [ "$order" = AB ]; then
    cp_ "$b" copy-pull --copy "$b" --from "$a" >/dev/null; cp_ "$a" copy-pull --copy "$a" --from "$b" >/dev/null
  else
    cp_ "$a" copy-pull --copy "$a" --from "$b" >/dev/null; cp_ "$b" copy-pull --copy "$b" --from "$a" >/dev/null
  fi
  for c in "$a" "$b"; do echo "$order $(basename "$c"): $(cp_ "$c" copy-hash --copy "$c" Shared.lean)"; done
done
echo "-- rendered Shared.lean (AB-bob):"; grep -v "^--\|^$" "$W/AB-bob/work/Shared.lean"
echo "-- git log (AB-bob):"; git -C "$W/AB-bob/work" log --format='%an: %s' -- Shared.lean
echo "-- last commit diff (the rename arrives as alice's commit):"; git -C "$W/AB-bob/work" show --format= -- Shared.lean | grep "^[-+]theorem"
echo "-- standalone elaboration of Shared.lean in both copies:"; elab "$W/AB-alice" Shared.lean; elab "$W/AB-bob" Shared.lean
echo "-- a draft using the renamed declaration by its rendered name (bob's copy):"
printf '\ntheorem Shared.check : 2 + 2 = 4 := Shared.dup_bob_1\ntheorem Shared.check2 : 1 + 1 = 2 := Shared.dup\n' >> "$W/AB-bob/work/Shared.lean"
elab "$W/AB-bob" Shared.lean
echo "-- export of the merged store:"
"$P" export --store "$W/AB-alice/store" --out "$W/export" | grep -E "^export|^stock|^verify|reject"
