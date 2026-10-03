#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .deps .runs
if [[ ! -f .deps/tla2tools.jar ]]; then
  curl -fL https://github.com/tlaplus/tlaplus/releases/download/v1.7.4/tla2tools.jar -o .deps/tla2tools.jar
fi
expected_tla=936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88
if command -v sha256sum >/dev/null; then
  actual_tla="$(sha256sum .deps/tla2tools.jar)"
else
  actual_tla="$(shasum -a 256 .deps/tla2tools.jar)"
fi
[[ "${actual_tla%% *}" == "$expected_tla" ]]
if [[ ! -d .deps/veil/.git ]]; then
  git clone https://github.com/verse-lab/veil.git .deps/veil
fi
git -C .deps/veil checkout d05518f22076b8cc84fb2d2b74d196aa979bfe8f
git -C .deps/veil diff --quiet
git -C .deps/veil diff --cached --quiet
export PATH="$HOME/.elan/bin:$PATH"
(cd .deps/veil && lake build)
