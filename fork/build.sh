#!/usr/bin/env bash
# Build the Paralean Lean fork (fork/README.md).
#   1. clone leanprover/lean4-nightly at the pin (nightly-2026-10-03, 193c3589), depth 1;
#   2. apply fork/patches/*.patch with `git am`, committer = author and committer date = author
#      date, so the resulting commit is the one recorded in fork/GITHASH;
#   3. `cmake --preset release` and `make stage1` (-j$PARALEAN_JOBS, default 12);
#   4. check that `lean --githash` of the build is fork/GITHASH.
# Usage: fork/build.sh [DIR]   (default <repo>/.deps/lean4-paralean)
# The installation is DIR/build/release/stage1 (bin/lean, bin/lake, lib/lean).
# Needs git, cmake, a C/C++ toolchain and libuv (with headers; set PKG_CONFIG_PATH if it is not
# installed system-wide, see docs/p0-log.md).
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"
PIN=193c3589a4fc16c4059261ab38cfa365eb24f323
URL=https://github.com/leanprover/lean4-nightly.git
DIR="${1:-$REPO/.deps/lean4-paralean}"
JOBS="${PARALEAN_JOBS:-12}"
WANT="$(cat "$HERE/GITHASH")"

if [ ! -d "$DIR/.git" ]; then
  mkdir -p "$DIR"
  git -C "$DIR" init -q
  git -C "$DIR" remote add origin "$URL"
fi
if ! git -C "$DIR" cat-file -e "$PIN^{commit}" 2>/dev/null; then
  git -C "$DIR" fetch -q --depth 1 origin "$PIN"
fi
if [ "$(git -C "$DIR" rev-parse HEAD 2>/dev/null || true)" != "$WANT" ]; then
  [ -z "$(git -C "$DIR" status --porcelain --untracked-files=no 2>/dev/null)" ] \
    || { echo "error: $DIR has local changes; refusing to reset it" >&2; exit 2; }
  git -C "$DIR" checkout -q -B paralean "$PIN"
  # deterministic commits: identity and date come from the patches
  for p in "$HERE"/patches/*.patch; do
    name="$(sed -n 's/^From: \(.*\) <.*>$/\1/p' "$p" | head -1)"
    email="$(sed -n 's/^From: .* <\(.*\)>$/\1/p' "$p" | head -1)"
    GIT_COMMITTER_NAME="$name" GIT_COMMITTER_EMAIL="$email" \
      git -C "$DIR" -c core.autocrlf=false am -q --committer-date-is-author-date "$p"
  done
fi
HEAD="$(git -C "$DIR" rev-parse HEAD)"
[ "$HEAD" = "$WANT" ] || { echo "error: patched tree is $HEAD, fork/GITHASH says $WANT" >&2; exit 1; }
echo "fork source: $DIR @ $HEAD"

cd "$DIR"
[ -f build/release/CMakeCache.txt ] || cmake --preset release
make -C build/release -j"$JOBS" stage1
GOT="$(build/release/stage1/bin/lean --githash)"
[ "$GOT" = "$WANT" ] || { echo "error: lean --githash is $GOT, expected $WANT" >&2; exit 1; }
build/release/stage1/bin/lean --version
echo "fork build: OK ($DIR/build/release/stage1)"
