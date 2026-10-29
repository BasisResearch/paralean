#!/usr/bin/env bash
# After the quiescent-Gone guard fix: the GC-touching suites and mutation scripts on w4r-d.
set -u
cd /data/home/kirancodes/Documents/code/paralean-w4-rest
export PARALEAN_INSTANCE=w4r-d
source impl/p3/scripts/w4r-env.sh
export CARGO_BUILD_JOBS=6
out=/data/home/kirancodes/Documents/code/paralean-w4-rest/results/w4r/rebased/guard-fix; mkdir -p "$out"
run() { local name="$1"; shift; echo "== $name: $*"; ( time "$@" ) > "$out/$name.log" 2>&1; echo "$name exit=$?"; }
cd impl/p2
run store       cargo test -p paralean-store -j6 -- --test-threads=1
run s3-guard    cargo test -p s3-guard -j6
run ae-service  cargo test -p paralean-ae-service -j6 -- --test-threads=1
run control-gc  cargo test -p paralean-control -j6 --test w4r_shards --test gc -- --test-threads=1
cd ../..
run mut-storegc  bash impl/p2/scripts/check-w4r-gc-mutations.sh
run mut-s3guard  bash impl/p2/scripts/check-s3-guard-mutations.sh
echo ALL-DONE
