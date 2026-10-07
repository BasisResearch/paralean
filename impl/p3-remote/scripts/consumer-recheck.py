#!/usr/bin/env python3
"""Re-time the consumer side of a corpus-cost.py run, commands only (import excluded).

For each module directory of RUNDIR: elaborate bob's all-`remote%` projection
(`ws-check`; payloads are already in bob's cache, so this is checking cost, not transfer),
and elaborate the module's original source with the same host in an empty copy. Both runs
report `elabMs` (the commands) and `auditMs` (`collectAxioms` of every constant) separately.

    consumer-recheck.py RUNDIR [M14 ...]      (env: impl/p3-remote/scripts/env.sh)
"""
import json, os, shutil, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
BIN = os.environ["PARALEAN_BIN"]
R = os.path.abspath(sys.argv[1])
os.environ["PARALEAN_KEYS"] = os.path.join(R, "keys.json")
# a run recorded with an older trust-file format may carry a converted copy
os.environ["PARALEAN_TRUST"] = os.path.join(R, "trust-v2.json" if os.path.exists(os.path.join(R, "trust-v2.json")) else "trust.json")
os.environ["PARALEAN_DEPLOYMENT"] = open(os.path.join(R, "deployment")).read().strip()
mathlib = os.environ["PARALEAN_MATHLIB"]
os.environ["LEAN_PATH"] = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=mathlib,
                                         capture_output=True, text=True).stdout.strip()
mods = {l.split()[0]: l.split()[1] for l in open(os.path.join(REPO, "corpus", "modules.txt"))
        if l.strip() and not l.startswith("#")}


def check(copy, file, runs=2):
    env = dict(os.environ, PARALEAN_STORE=os.path.join(copy, "cache"), PARALEAN_VISIBILITY="1",
               PARALEAN_VIS_EXCLUDE=file, PARALEAN_REMOTE_LOG=os.path.join(copy, "recheck.log"))
    best = None
    for _ in range(runs):
        out = subprocess.run([BIN, "ws-check", "--dir", copy, file], capture_output=True, text=True, env=env).stdout
        j = json.loads(out.strip().splitlines()[-1])
        if best is None or j["elabMs"] < best["elabMs"]:
            best = j
    return best


rows = []
for k in sys.argv[2:] or sorted(d for d in os.listdir(R) if d.startswith("M")):
    d = os.path.join(R, k)
    if not os.path.isdir(os.path.join(d, "bob")):
        continue
    file = f"{k}.lean"
    rem = check(os.path.join(d, "bob"), file)
    loc_dir = os.path.join(d, "local")
    shutil.rmtree(loc_dir, ignore_errors=True)
    os.makedirs(os.path.join(loc_dir, "work"))
    os.makedirs(os.path.join(loc_dir, "cache", "p3", "records"))
    src = os.path.join(mathlib, *mods[k].split(".")) + ".lean"
    shutil.copy(src, os.path.join(loc_dir, "work", file))
    loc = check(loc_dir, file)
    row = {"module": k, "remote_elab_ms": rem["elabMs"], "remote_audit_ms": rem["auditMs"],
           "remote_errors": len(rem["errors"]), "loaded_constants": rem["loadedConstants"],
           "local_elab_ms": loc["elabMs"], "local_errors": len(loc["errors"]),
           "ratio": round(rem["elabMs"] / max(1, loc["elabMs"]), 2),
           "loaded_axioms": [".".join(map(str, a)) if isinstance(a, list) else a for a in rem["loadedAxioms"]]}
    print(json.dumps(row), flush=True)
    rows.append(row)
json.dump(rows, open(os.path.join(R, "recheck.json"), "w"), indent=1)
