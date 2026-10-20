#!/usr/bin/env python3
"""Run the validator (`paralean check-group`) on every group of a captured store.

Usage: gate_corpus.py STORE OUT.json [PARALEAN_BIN ...]

For each group of the store's current files, the job is the group's dependency closure
(kernel and frontend dependencies), as P3 control builds it. With several binaries (for
example the W2 build and the baseline build) the verdicts are compared, so that groups the
W2 command gate refuses are separated from groups refused before as well.
"""

import json
import os
import subprocess
import sys
from pathlib import Path


def closure(metas, gid):
    out, todo = [], [gid]
    seen = set()
    while todo:
        g = todo.pop()
        if g in seen:
            continue
        seen.add(g)
        out.append(g)
        m = metas[g]
        todo.extend(m["deps"] + m["feDeps"])
    return out


def main():
    store, out, *bins = sys.argv[1:]
    store = Path(store)
    metas = {p.stem: json.loads(p.read_text()) for p in (store / "meta").glob("*.json")}
    files = sorted((store / "files").glob("*.json"), key=lambda p: int(p.stem))
    latest = {}
    for f in files:
        r = json.loads(f.read_text())
        latest[(r["workspace"], r["file"])] = r
    env = {k: v for k, v in os.environ.items() if k != "PARALEAN_MATHLIB"}
    rows = []
    for (_, file), rec in sorted(latest.items()):
        for gid in rec["groups"]:
            g = metas[gid]
            row = {"file": file, "line": g["capsule"]["startLine"], "gid": gid, "decl": g["declId"],
                   "names": [".".join(map(str, n)) for n in g["publicNames"]], "cmd": ".".join(g["cmdKind"]),
                   "verdicts": {}}
            for b in bins:
                r = subprocess.run([b, "check-group", "--store", str(store), "--gids", ",".join(closure(metas, gid)),
                                    "--decl", g["declId"]], capture_output=True, text=True, env=env)
                line = next((l for l in r.stdout.splitlines() if l.startswith("CHECK ")), None)
                res = json.loads(line[6:]) if line else {"ok": False, "diags": [r.stderr[-500:]]}
                row["verdicts"][b] = {"ok": res["ok"], "diags": [d[:300] for d in res.get("diags", [])][:4]}
            rows.append(row)
            print(row["file"], row["line"], row["cmd"], {b: v["ok"] for b, v in row["verdicts"].items()}, flush=True)
    Path(out).write_text(json.dumps(rows, indent=1) + "\n")
    for b in bins:
        print(b, "accepted", sum(r["verdicts"][b]["ok"] for r in rows), "of", len(rows))
    if len(bins) == 2:
        new, old = bins
        changed = [r for r in rows if r["verdicts"][new]["ok"] != r["verdicts"][old]["ok"]]
        print("verdicts that differ:", len(changed))
        for r in changed:
            print("  ", r["file"], r["line"], r["cmd"], r["names"], "new:", r["verdicts"][new]["ok"],
                  (r["verdicts"][new]["diags"] or [""])[0][:200])


if __name__ == "__main__":
    main()
