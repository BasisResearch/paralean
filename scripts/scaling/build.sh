#!/usr/bin/env bash
set -euo pipefail
source scripts/scaling/env.sh
wait_for_load() {
  python3 - <<'PY'
import os,time
while os.getloadavg()[0] > 24:
    print(time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()), 'build waiting for load <24:',os.getloadavg(),flush=True)
    time.sleep(30)
PY
}
mkdir -p .runs/scaling
wait_for_load
(cd impl/p1 && lake build) > .runs/scaling/lean-build.log 2>&1
wait_for_load
RUSTC_WRAPPER= cargo build --offline --release --locked --manifest-path impl/p2/Cargo.toml -j2 > .runs/scaling/rust-build.log 2>&1
wait_for_load
CARGO_TARGET_DIR="$PWD/impl/p2/target" RUSTC_WRAPPER= cargo build --offline --release --locked --manifest-path impl/p5/store-bridge/Cargo.toml -j2 > .runs/scaling/bridge-build.log 2>&1
