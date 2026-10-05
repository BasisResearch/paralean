#!/usr/bin/env bash
cd /data/home/kirancodes/Documents/code/paralean/.deps/mathlib-local
export TMPDIR=$HOME/tmp PATH=$HOME/p0-deps/lean-stock-193c3589/bin:$PATH
unset LEAN_PATH LEAN_SYSROOT ELAN_TOOLCHAIN
echo "start $(date -Is)"; which lean lake; lean --version
/usr/bin/time -v lake build 2>&1 &
pid=$!
$HOME/p0-out/sample-rss.sh $HOME/p0-out/mathlib-build-rss.txt $pid &
wait $pid; rc=$?
echo "BUILD_EXIT=$rc end $(date -Is)"
