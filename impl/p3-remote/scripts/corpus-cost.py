#!/usr/bin/env python3
"""Transfer and checking costs of v1 `remote%` on the Mathlib corpus (P3 gate measurement).

For each module: copy `alice` captures the module's source as one shared file and publishes
every group through the store (stage, validator job, T1), one group at a time; a fresh copy
`bob` pulls the publication records (metadata only) and elaborates the all-`remote%`
projection, fetching each group's payload on demand and kernel-checking fetched proofs.
Compared with local capture of the same file and with stock `lean` (`Elab.async=false`).

    corpus-cost.py RUNDIR [M14 M03 ...]
    (env: impl/p3-remote/scripts/env.sh with PARALEAN_LEAN=fork; Mathlib in PARALEAN_MATHLIB)

Writes RUNDIR/costs.tsv and RUNDIR/costs.json.
"""
import json, os, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
WS = os.path.join(HERE, "ws.py")
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
PLR, P3BIN, BIN = os.environ["PARALEAN_PLR"], os.environ["PARALEAN_P3_BIN"], os.environ["PARALEAN_BIN"]
R = os.path.abspath(sys.argv[1])
MODS = sys.argv[2:] or ["M14", "M03", "M15", "M13", "M16", "M01", "M18"]


def modules():
    out = {}
    for l in open(os.path.join(REPO, "corpus", "modules.txt")):
        if l.strip() and not l.startswith("#"):
            k, m = l.split()[:2]
            out[k] = m
    return out


def sh(cmd, env=None, check=True):
    p = subprocess.run(cmd, capture_output=True, text=True, env=env or os.environ)
    if check and p.returncode != 0:
        raise SystemExit(f"{cmd}: {p.stdout[-2000:]} {p.stderr[-2000:]}")
    return p


def jsonl(p):
    return [json.loads(l) for l in open(p)] if os.path.exists(p) else []


def main():
    os.makedirs(R, exist_ok=True)
    mathlib = os.environ["PARALEAN_MATHLIB"]
    lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=mathlib, capture_output=True, text=True).stdout.strip()
    os.environ["LEAN_PATH"] = lean_path
    os.environ["PARALEAN_DEPLOYMENT"] = os.environ.get("PARALEAN_DEPLOYMENT") or f"p3cost{int(time.time())}"
    open(os.path.join(R, "deployment"), "w").write(os.environ["PARALEAN_DEPLOYMENT"])
    keys, trust, rogue = (os.path.join(R, n) for n in ("keys.json", "trust.json", "rogue.json"))
    os.environ["PARALEAN_KEYS"], os.environ["PARALEAN_TRUST"] = keys, trust
    sh([PLR, "keys-init", keys, trust, rogue, "--agents", "alice,bob"])
    port = os.environ.get("PARALEAN_VALIDATOR_PORT", "18592")
    os.environ["PARALEAN_VALIDATOR"] = f"127.0.0.1:{port}"
    vlog = open(os.path.join(R, "validator.log"), "a")
    val = subprocess.Popen([P3BIN, "validator", "--listen", os.environ["PARALEAN_VALIDATOR"], "--key", "v0",
                            "--workdir", os.path.join(R, "validator"), "--max-running", "1"], stdout=vlog, stderr=vlog)
    time.sleep(1.5)
    mods = modules()
    rows = []
    try:
        for k in MODS:
            rows.append(one(k, mods[k], mathlib))
            json.dump(rows, open(os.path.join(R, "costs.json"), "w"), indent=1)
    finally:
        val.terminate()
    cols = ["module", "groups", "published", "rejected", "publish_s", "validate_s_mean", "t1_ms_mean",
            "pull_bytes", "pull_ms", "fetched_groups", "fetched_bytes", "fetch_ms", "remote_elab_s", "local_capture_s",
            "stock_sync_s", "fetched_proof_loads", "elaborated_loads", "load_ms", "check_ms", "errors", "loaded_axioms"]
    with open(os.path.join(R, "costs.tsv"), "w") as f:
        f.write("\t".join(cols) + "\n")
        for r in rows:
            f.write("\t".join(str(r.get(c, "")) for c in cols) + "\n")
    print(open(os.path.join(R, "costs.tsv")).read())


def one(k, module, mathlib):
    d = os.path.join(R, k)
    src = os.path.join(mathlib, *module.split(".")) + ".lean"
    file = f"{k}.lean"
    alice, bob = os.path.join(d, "alice"), os.path.join(d, "bob")
    for c, a in ((alice, "alice"), (bob, "bob")):
        sh([WS, "init", c, a])
    os.makedirs(os.path.join(alice, "work"), exist_ok=True)
    open(os.path.join(alice, "work", file), "w").write(open(src).read())
    # stock Lean, synchronous elaboration, on the original module
    stock = 1e9
    for _ in range(2):  # warm the page cache first; report the faster run
        t = time.time()
        sh(["lean", "-DElab.async=false", src])
        stock = min(stock, time.time() - t)
    # publish everything (alice)
    t = time.time()
    p = sh([WS, "publish", alice, file], check=False)
    pub_s = time.time() - t
    open(os.path.join(d, "publish.out"), "w").write(p.stdout + p.stderr)
    steps = jsonl(os.path.join(alice, "steps.log"))
    cap_ms = sum(s["ms"] for s in steps if s["cmd"][1] == "ws-capture")
    val_ms = [s["ms"] for s in steps if s["cmd"][1] == "validate"]
    t1_ms = [s["ms"] for s in steps if s["cmd"][1] == "publish"]
    vals = [json.loads(l.split(" ", 1)[1]) for l in p.stdout.splitlines() if l.startswith("validate ")]
    capture = [json.loads(l.split(" ", 1)[1]) for l in p.stdout.splitlines() if l.startswith("capture ")]
    # consume (bob): metadata by anti-entropy, payloads on demand while elaborating
    j = sh([WS, "sync", bob]).stdout
    pull = [json.loads(l.split(" ", 1)[1]) for l in j.splitlines() if l.startswith("pull ")][0]
    t = time.time()
    c = sh([WS, "check", bob, file], check=False).stdout
    elab = time.time() - t
    chk = [json.loads(l.split(" ", 1)[1]) for l in c.splitlines() if l.startswith("check ")]
    chk = chk[0] if chk else {"errors": ["no output"], "loadedAxioms": []}
    tr = jsonl(os.path.join(bob, "cache", "p3", "transfer.jsonl"))
    fetched = [x for x in tr if x["kind"] == "fetch-group"]
    loads = [l.split() for l in open(os.path.join(bob, "remote.log"))] if os.path.exists(os.path.join(bob, "remote.log")) else []
    lf = [l for l in loads if l[0] == "load" and l[2] == "fetched-proof"]
    le = [l for l in loads if l[0] == "load" and l[2] in ("elaborated", "effect")]
    ms = lambda s: int(s.rstrip("ms"))
    row = {
        "module": k, "groups": (capture[0]["packages"] if capture else 0),
        "published": sum(1 for v in vals if v["accepted"]), "rejected": sum(1 for v in vals if not v["accepted"]),
        "publish_s": round(pub_s, 1), "validate_s_mean": round(sum(val_ms) / max(1, len(val_ms)) / 1000, 2),
        "t1_ms_mean": round(sum(t1_ms) / max(1, len(t1_ms))),
        "pull_bytes": pull.get("bytes"), "pull_ms": round(pull.get("ms", 0)),
        "fetched_groups": len(fetched), "fetched_bytes": sum(x["bytes"] for x in fetched),
        "fetch_ms": round(sum(x["ms"] for x in fetched)),
        "remote_elab_s": round(elab, 2), "local_capture_s": round(cap_ms / 1000, 2), "stock_sync_s": round(stock, 2),
        "fetched_proof_loads": len(lf), "elaborated_loads": len(le),
        "load_ms": sum(ms(l[3]) for l in lf + le if len(l) > 3),
        "check_ms": sum(ms(l[5]) for l in lf + le if len(l) > 5),
        "errors": len(chk["errors"]), "loaded_axioms": ",".join(".".join(map(str, a)) if isinstance(a, list) else a
                                                             for a in chk.get("loadedAxioms", [])),
        "first_errors": chk["errors"][:3], "rejections": [v["reason"][:300] for v in vals if not v["accepted"]][:5],
    }
    print(json.dumps({k2: row[k2] for k2 in row if k2 not in ("first_errors", "rejections")}), flush=True)
    return row


if __name__ == "__main__":
    main()
