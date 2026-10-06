#!/usr/bin/env python3
"""Per-operation costs of a gate run (gate.py RUNDIR): latency of each step kind over all
copies (steps.log: one process each), bytes moved (transfer.jsonl) and remote% loads
(remote.log).  Usage: gate-costs.py RUNDIR"""
import json, os, statistics, sys

R = sys.argv[1]
steps, transfers, loads = {}, {}, {"fetched-proof": [], "elaborated": [], "effect": [], "check": []}
for c in sorted(os.listdir(R)):
    d = os.path.join(R, c)
    p = os.path.join(d, "steps.log")
    if os.path.exists(p):
        for l in open(p):
            j = json.loads(l)
            if j["rc"] == 0:
                steps.setdefault(f'{j["cmd"][0]} {j["cmd"][1]}', []).append(j["ms"])
    p = os.path.join(d, "cache", "p3", "transfer.jsonl")
    if os.path.exists(p):
        for l in open(p):
            j = json.loads(l)
            transfers.setdefault(j["kind"], []).append((j["bytes"], j["ms"]))
    p = os.path.join(d, "remote.log")
    if os.path.exists(p):
        for l in open(p):
            w = l.split()
            if w[0] == "load":
                loads[w[2]].append(int(w[3].rstrip("ms")))
                if len(w) > 5:
                    loads["check"].append(int(w[5].rstrip("ms")))


def stat(xs):
    xs = sorted(xs)
    return {"n": len(xs), "median": statistics.median(xs), "p95": xs[min(len(xs) - 1, int(0.95 * len(xs)))], "max": xs[-1]}


out = {"steps_ms": {k: stat(v) for k, v in sorted(steps.items())},
       "transfers": {k: {"n": len(v), "bytes": sum(b for b, _ in v), "bytes_median": statistics.median(b for b, _ in v),
                         "ms_median": round(statistics.median(m for _, m in v), 1)} for k, v in sorted(transfers.items())},
       "remote_loads_ms": {k: stat(v) for k, v in loads.items() if v}}
print(json.dumps(out, indent=1))
