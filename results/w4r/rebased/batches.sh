#!/usr/bin/env bash
# Main's atomic_batches suite and its controller mutation cases (check-mutations.sh) on w4r-d.
set -u
cd /data/home/kirancodes/Documents/code/paralean-w4-rest
export PARALEAN_INSTANCE=w4r-d
source impl/p3/scripts/w4r-env.sh
source impl/p1/scripts/env.sh
fdb=$PARALEAN_FDB_CLUSTER; s3=$PARALEAN_S3_ENDPOINT
echo "fdb=$fdb s3=$s3"
cd impl/p2
cargo test -q -p paralean-control -j6 --test atomic_batches -- --test-threads=1 2>&1 | tail -15
echo "suite exit=${PIPESTATUS[0]}"
while IFS='|' read -r feat target name; do
  [[ -z "$feat" ]] && continue
  if out="$(cargo test -q -j6 -p paralean-control --features "$feat" --test "$target" -- --exact "$name" --test-threads=1 2>&1)"; then
    echo "SURVIVED $feat"
  elif grep -q "$name.*FAILED\|---- $name" <<<"$out"; then echo "detected $feat ($name)"; else echo "ERROR $feat"; tail -20 <<<"$out"; fi
done < <(grep -o '"[^"]*|atomic_batches|[^"]*"' ../p3/scripts/check-mutations.sh | tr -d '"')
cargo build -q -p paralean-control -j6
