#!/usr/bin/env bash
# Set up everything the P1 scripts need, at the pins in versions.json, inside the repo:
#   1. the elan toolchain leanprover/lean4-nightly:nightly-2026-10-03, checked to be
#      commit 193c3589a4fc16c4059261ab38cfa365eb24f323;
#   2. the core fixture package corpus/fixtures, built with stock `lake build`;
#   3. the paralean binary (impl/p1, `lake build`);
#   4. with --mathlib: Mathlib (mathlib4-nightly-testing at the pinned commit) in
#      .deps/mathlib (or $PARALEAN_MATHLIB), its dependencies, and its .olean cache via
#      `lake exe cache get`. No Mathlib build is started; if the cache does not cover the
#      pin, the script stops and says so.
# Usage: impl/p1/scripts/bootstrap.sh [--mathlib]
set -euo pipefail
source "$(dirname "$0")/env.sh"

want_mathlib=0
for a in "$@"; do
  case "$a" in
    --mathlib) want_mathlib=1 ;;
    *) die "unknown argument $a" ;;
  esac
done

echo "## toolchain $PARALEAN_TOOLCHAIN"
command -v elan >/dev/null 2>&1 || die "elan is not installed (https://github.com/leanprover/elan)"
if ! lean --githash >/dev/null 2>&1; then
  elan toolchain install "$PARALEAN_TOOLCHAIN"
fi
require_toolchain
echo "lean --githash = $(lean --githash) (pinned)"

echo "## core fixtures (stock lake build)"
(cd "$REPO/corpus/fixtures" && lake build)

echo "## paralean binary"
(cd "$P1_DIR" && lake build)
require_bin
echo "paralean: $PARALEAN_BIN"

if [ "$want_mathlib" = 1 ]; then
  read -r ml_repo ml_commit < <(python3 -c 'import json,sys; m=json.load(open(sys.argv[1]))["mathlib"]; print(m["repository"], m["commit"])' "$REPO/versions.json")
  echo "## Mathlib $ml_repo @ $ml_commit -> $PARALEAN_MATHLIB"
  if [ ! -d "$PARALEAN_MATHLIB/.git" ]; then
    mkdir -p "$PARALEAN_MATHLIB"
    git -C "$PARALEAN_MATHLIB" init -q
    git -C "$PARALEAN_MATHLIB" remote add origin "$ml_repo"
  fi
  if [ "$(git -C "$PARALEAN_MATHLIB" rev-parse HEAD 2>/dev/null || true)" != "$ml_commit" ]; then
    git -C "$PARALEAN_MATHLIB" fetch -q --depth 1 origin "$ml_commit"
    git -C "$PARALEAN_MATHLIB" checkout -q --detach "$ml_commit"
  fi
  grep -q "nightly-2026-10-03" "$PARALEAN_MATHLIB/lean-toolchain" \
    || die "Mathlib's lean-toolchain ($(cat "$PARALEAN_MATHLIB/lean-toolchain")) is not the pinned nightly"
  # dependencies at the manifest's revisions, then the prebuilt .olean cache
  (cd "$PARALEAN_MATHLIB" && lake exe cache get)
  # verify the cache covers the corpus modules without building anything
  if ! (cd "$PARALEAN_MATHLIB" && lake build --no-build Mathlib.Order.Basic Mathlib.Logic.Function.Basic \
        Mathlib.Tactic.Attr.Register Mathlib.Algebra.Field.ZMod >/dev/null); then
    die "the Mathlib cache does not cover the pinned commit; a full Mathlib build would be needed (not started)"
  fi
  require_mathlib
  echo "Mathlib ready (LEAN_PATH via 'lake env' in $PARALEAN_MATHLIB)"
fi
echo "bootstrap: OK"
