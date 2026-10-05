# Shared environment for the P1 scripts. Source it; do not execute it.
#
# Every path defaults to a location inside the repository and can be overridden:
#   PARALEAN_RUNS      work directory for stores and exports   (default <repo>/.runs/p1)
#   PARALEAN_BIN       the paralean binary                     (default impl/p1/.lake/build/bin/paralean)
#   PARALEAN_MATHLIB   Mathlib checkout at the versions.json pin (default <repo>/.deps/mathlib)
#   PARALEAN_TOOLCHAIN elan toolchain                           (default leanprover/lean4-nightly:nightly-2026-10-03)
#   PARALEAN_LAKE      lake used for stock export builds        (default: elan's lake, run under PARALEAN_TOOLCHAIN)
#   TMPDIR             scratch space                            (default <repo>/.runs/tmp)
# Run impl/p1/scripts/bootstrap.sh once to create the defaults.

P1_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REPO="$(cd "$P1_DIR/../.." && pwd)"
PIN_COMMIT="193c3589a4fc16c4059261ab38cfa365eb24f323"
export PARALEAN_TOOLCHAIN="${PARALEAN_TOOLCHAIN:-leanprover/lean4-nightly:nightly-2026-10-03}"
# elan proxies (`lean`, `lake`) honour ELAN_TOOLCHAIN over the user's default toolchain.
# paralean locates its Lean sysroot through `lean --print-prefix`, so this matters.
export ELAN_TOOLCHAIN="${ELAN_TOOLCHAIN:-$PARALEAN_TOOLCHAIN}"
export PARALEAN_RUNS="${PARALEAN_RUNS:-$REPO/.runs/p1}"
export PARALEAN_BIN="${PARALEAN_BIN:-$P1_DIR/.lake/build/bin/paralean}"
export PARALEAN_LIB="${PARALEAN_LIB:-$P1_DIR/.lake/build/lib/lean}"
export PARALEAN_MATHLIB="${PARALEAN_MATHLIB:-$REPO/.deps/mathlib}"
export TMPDIR="${TMPDIR:-$REPO/.runs/tmp}"
mkdir -p "$TMPDIR"

die() { echo "error: $*" >&2; exit 2; }

# The pinned toolchain must be the one `lean` resolves to.
require_toolchain() {
  command -v lean >/dev/null 2>&1 || die "no 'lean' on PATH; install elan and run impl/p1/scripts/bootstrap.sh"
  local h; h="$(lean --githash 2>/dev/null)" || die "'lean --githash' failed (toolchain $ELAN_TOOLCHAIN not installed?); run impl/p1/scripts/bootstrap.sh"
  [ "$h" = "$PIN_COMMIT" ] || die "lean resolves to commit $h, expected $PIN_COMMIT (toolchain $ELAN_TOOLCHAIN)"
}

require_bin() {
  require_toolchain
  [ -x "$PARALEAN_BIN" ] || die "paralean binary not found at $PARALEAN_BIN; run impl/p1/scripts/bootstrap.sh (or set PARALEAN_BIN)"
}

# Mathlib checkout with built (cache-fetched) .oleans at the versions.json pin.
require_mathlib() {
  local want; want="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["mathlib"]["commit"])' "$REPO/versions.json")"
  [ -d "$PARALEAN_MATHLIB" ] || die "Mathlib checkout not found at $PARALEAN_MATHLIB; run impl/p1/scripts/bootstrap.sh --mathlib (or set PARALEAN_MATHLIB)"
  local have; have="$(cd "$PARALEAN_MATHLIB" && git rev-parse HEAD 2>/dev/null)" || die "$PARALEAN_MATHLIB is not a git checkout"
  [ "$have" = "$want" ] || die "Mathlib at $PARALEAN_MATHLIB is $have, expected $want"
  [ -f "$PARALEAN_MATHLIB/.lake/build/lib/lean/Mathlib/Order/Basic.olean" ] \
    || die "Mathlib at $PARALEAN_MATHLIB has no built .oleans; run impl/p1/scripts/bootstrap.sh --mathlib"
}

mathlib_lean_path() { (cd "$PARALEAN_MATHLIB" && lake env printenv LEAN_PATH); }
