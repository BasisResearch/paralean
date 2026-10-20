#!/usr/bin/env bash
# Compile the same register_simp_attr command in two Lean modules and check
# the generated initializer bodies contain different module-name literals.
set -euo pipefail
cd "$(dirname "$0")/.."
lean_bin="${1:-lean}"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

"$lean_bin" verification/fixtures/identity/IdentityOriginal.lean > "$tmp/original.log" 2>&1
"$lean_bin" verification/fixtures/identity/IdentityRelocated.lean > "$tmp/relocated.log" 2>&1

python3 - "$tmp/original.log" "$tmp/relocated.log" <<'PY'
from pathlib import Path
import re
import sys

for path, module in zip(sys.argv[1:], ("IdentityOriginal", "IdentityRelocated")):
    lines = Path(path).read_text().splitlines()
    hits = [line for line in lines if "initFn" in line and
            re.search(rf"\._hyg\.\d+: \[{module}\]$", line)]
    if len(hits) != 2:
        raise SystemExit(f"{module}: expected two generated initFn literals; got {len(hits)}\n"
                         + "\n".join(lines[:20]))
    for line in sorted(hits):
        print(line)
print("PASS: generated initializer literals differ with the Lean module")
PY
