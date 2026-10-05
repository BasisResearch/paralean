#!/usr/bin/env bash
cd /data/home/kirancodes/Documents/code/paralean/.deps/mathlib-local
export TMPDIR=$HOME/tmp PATH=$HOME/p0-deps/lean-stock-193c3589/bin:$PATH
unset LEAN_PATH LEAN_SYSROOT
echo "start $(date -Is)"
/usr/bin/time -v lake test 2>&1
echo "TEST_EXIT=$? end $(date -Is)"
