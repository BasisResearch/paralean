#!/usr/bin/env bash
# Integrated W4-rest run on w4r-d: every suite, then every mutation script.
set -u
cd /data/home/kirancodes/Documents/code/paralean-w4-rest
export PARALEAN_INSTANCE=w4r-d
source impl/p3/scripts/w4r-env.sh
export CARGO_BUILD_JOBS=6
out=/data/home/kirancodes/Documents/code/paralean-w4-rest/results/w4r/rebased; mkdir -p "$out"; df -h /data | tail -1
bash impl/p2/scripts/down.sh > "$out/down.log" 2>&1
bash impl/p2/scripts/up.sh > "$out/up.log" 2>&1 || { echo "up failed"; exit 1; }
run() { local name="$1"; shift; echo "== $name: $*"; ( time "$@" ) > "$out/$name.log" 2>&1; echo "$name exit=$?"; }
cd impl/p2
run store       cargo test -p paralean-store -j6 -- --test-threads=1
run s3-guard    cargo test -p s3-guard -j6
run ae-service  cargo test -p paralean-ae-service -j6 -- --test-threads=1
run control     cargo test -p paralean-control -j6 --lib --test durable --test gc --test w4_history --test w4_dependencies --test w4_processes --test w4_workers --test w4r_shards --test w4r_replay --test strict_signatures --test p5_claims -- --test-threads=1
cd ../..
run mut-storegc  bash impl/p2/scripts/check-w4r-gc-mutations.sh
run mut-s3guard  bash impl/p2/scripts/check-s3-guard-mutations.sh
run mut-store    bash impl/p2/scripts/check-mutations.sh
run mut-shard    bash impl/p3/scripts/check-w4r-shard-mutations.sh
run mut-replay   bash impl/p3/scripts/check-w4r-replay-mutations.sh
run mut-w4       bash impl/p3/scripts/check-w4-mutations.sh
run mut-w4gc     bash impl/p3/scripts/check-w4-gc-mutations.sh
run mut-w4hist   bash impl/p3/scripts/check-w4-history-mutations.sh
echo ALL-DONE
