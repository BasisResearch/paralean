#!/usr/bin/env bash
# Sample aggregate RSS (KiB) and process count of all descendants of PID $2 every 5 s.
out=$1 root=$2; : > "$out"
while kill -0 "$root" 2>/dev/null; do
  ps -eo pid=,ppid=,rss= | awk -v r="$root" '{p[$1]=$2; m[$1]=$3} END {
    for (x in p) { y=x; while (y in p && y!=r && y>1) y=p[y]; if (y==r) {t+=m[x]; n++} }
    print t+0, n+0 }' | sed "s/^/$(date +%s) /" >> "$out"
  sleep 5
done
