# Source from the repository root. All writable service/build paths belong here.
export PARALEAN_INSTANCE=p5-scal-20261028
export PARALEAN_P5_PREFIX="$PWD/.runs/scaling/cluster"
export PARALEAN_P5_FDB_PORT=5289
export PARALEAN_P5_GARAGE_S3_PORT=19839
export PARALEAN_P5_GARAGE_RPC_PORT=19840
export PARALEAN_P5_GARAGE_ADMIN_PORT=19841
export PARALEAN_P5_S3_PORT=19833
export PARALEAN_VALIDATOR_PORT=19891
export PARALEAN_FORK_PREFIX=/data/home/kirancodes/Documents/code/paralean-m-p4/.deps/lean4-paralean/build/release/stage1
export PARALEAN_MATHLIB=/data/home/kirancodes/Documents/code/paralean-m-p4/.deps/mathlib-fork
export LEAN_NUM_THREADS=1
export RAYON_NUM_THREADS=2
export TOKIO_WORKER_THREADS=2
export CARGO_BUILD_JOBS=2
export TMPDIR="$PWD/.runs/scaling/tmp"
source impl/p5/scripts/env.sh
