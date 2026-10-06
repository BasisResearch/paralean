#!/usr/bin/env python3
"""One agent's working copy (P3 transparent workspaces).

    ws.py init DIR AGENT
    ws.py publish DIR FILE      capture, then per new group: stage, validate, plan, publish
    ws.py sync DIR [PULL-ARGS]  anti-entropy (plr pull) and working-file update
    ws.py delete DIR FILE NAME  tombstone a live declaration of FILE
    ws.py hash DIR FILE...      published-projection hashes
    ws.py check DIR FILE...     elaborate working files; errors and axioms

Environment (impl/p3-remote/scripts/env.sh): PARALEAN_BIN, PARALEAN_PLR, PARALEAN_KEYS (at
init, the copy takes keys-<agent>.json from its directory: own seeds only),
PARALEAN_TRUST, PARALEAN_DEPLOYMENT, PARALEAN_VALIDATOR (host:port), and the store's.
Each step is a separate process; nothing is shared between copies except the store.
Prints one JSON object per step on stdout (prefixed by the step name).
"""
import json, os, shutil, subprocess, sys, time

BIN = os.environ["PARALEAN_BIN"]
PLR = os.environ["PARALEAN_PLR"]


def env_for(d, file=None):
    e = dict(os.environ)
    e["PARALEAN_STORE"] = os.path.join(d, "cache")
    e["PARALEAN_VISIBILITY"] = "1"
    own = os.path.join(d, "keys.json")
    if os.path.exists(own):
        # the copy's own key file: its workspace and job-issuer seeds, nobody else's
        e["PARALEAN_KEYS"] = own
    if file:
        e["PARALEAN_VIS_EXCLUDE"] = file
    e.setdefault("PARALEAN_REMOTE_LOG", os.path.join(d, "remote.log"))
    return e


def run(cmd, d, file=None, check=True):
    t = time.time()
    p = subprocess.run(cmd, capture_output=True, text=True, env=env_for(d, file))
    ms = (time.time() - t) * 1000
    with open(os.path.join(d, "steps.log"), "a") as f:
        f.write(json.dumps({"cmd": [os.path.basename(cmd[0])] + cmd[1:], "ms": round(ms), "rc": p.returncode,
                            "stderr": p.stderr[-4000:]}) + "\n")
    if check and p.returncode != 0:
        sys.stderr.write(p.stderr)
        raise SystemExit(f"{os.path.basename(cmd[0])} {cmd[1]} failed ({p.returncode}): {p.stdout[-2000:]}")
    out = p.stdout.strip().splitlines()
    try:
        return json.loads(out[-1]) if out else {}
    except json.JSONDecodeError:
        return {"raw": p.stdout}


def emit(step, obj):
    print(step, json.dumps(obj), flush=True)


def cache(d):
    return os.path.join(d, "cache")


def sync(d, pull_args=()):
    r = run([PLR, "pull", "--cache", cache(d), *pull_args], d)
    emit("pull", r)
    if r.get("stale"):
        return r
    s = run([BIN, "ws-sync", "--dir", d], d)
    emit("sync", s)
    return s


def publish(d, file):
    if not os.environ.get("PARALEAN_NO_PULL"):
        run([PLR, "pull", "--cache", cache(d)], d)
    cap = run([BIN, "ws-capture", "--dir", d, file], d, file)
    emit("capture", {"packages": len(cap["packages"]), "rejected": cap["rejected"]})
    published = []
    for p in cap["packages"]:
        pkg = f'{p["group"]}:{p["capsule"]}'
        run([PLR, "stage", "--cache", cache(d), "--pkg", pkg], d)
        v = run([PLR, "validate", "--cache", cache(d), "--ws", os.environ["PARALEAN_AGENT"],
                 "--validator", os.environ["PARALEAN_VALIDATOR"], "--pkg", pkg, "--deps", ",".join(p["deps"])], d,
                check=False)
        if "error" in v:
            # no receipt (refused, inconclusive): the group stays a draft
            v = {"accepted": False, "reason": v["error"]}
        emit("validate", {"names": p["names"], "accepted": v["accepted"], "reason": v.get("reason", "")[:300], "ms": v.get("ms")})
        if not v["accepted"]:
            continue
        if os.environ.get("PARALEAN_PAUSE_BEFORE_PLAN"):
            # test hook: wait for a teammate's publication between the validator's response and
            # its use (the stale-response scenario)
            open(os.environ["PARALEAN_PAUSE_BEFORE_PLAN"] + ".waiting", "w").close()
            while not os.path.exists(os.environ["PARALEAN_PAUSE_BEFORE_PLAN"]):
                time.sleep(0.2)
            run([PLR, "pull", "--cache", cache(d)], d)
        rpath = os.path.join(d, "receipt.json")
        json.dump(v, open(rpath, "w"))
        plan = os.path.join(d, "plan.json")
        pl = run([BIN, "ws-plan", "--dir", d, "--file", file, "--receipts", rpath, "--out", plan], d, file)
        emit("plan", pl)
        if pl.get("planned", 0) == 0:
            continue
        pub = run([PLR, "publish", "--cache", cache(d), "--ws", os.environ["PARALEAN_AGENT"], "--plan", plan], d)
        emit("publish", pub)
        run([PLR, "pull", "--cache", cache(d), "--only", p["group"]], d)
        published.append(p["group"])
    if not os.environ.get("PARALEAN_NO_PULL"):
        sync(d)
    else:
        emit("sync", run([BIN, "ws-sync", "--dir", d], d))
    return published


def main():
    cmd, d = sys.argv[1], os.path.abspath(sys.argv[2])
    if cmd == "init":
        os.makedirs(d, exist_ok=True)
        run([BIN, "ws-init", "--dir", d, "--agent", sys.argv[3]], d)
        own = os.path.join(os.path.dirname(os.environ["PARALEAN_KEYS"]), f"keys-{sys.argv[3]}.json")
        if os.path.exists(own):
            shutil.copy(own, os.path.join(d, "keys.json"))
        with open(os.path.join(d, "agent"), "w") as f:
            f.write(sys.argv[3])
        return
    os.environ["PARALEAN_AGENT"] = open(os.path.join(d, "agent")).read().strip()
    if cmd == "publish":
        emit("published", publish(d, sys.argv[3]))
    elif cmd == "sync":
        sync(d, sys.argv[3:])
    elif cmd == "delete":
        t = run([BIN, "ws-delete", "--dir", d, "--file", sys.argv[3], "--name", sys.argv[4]], d)
        r = run([PLR, "tombstone", "--cache", cache(d), "--ws", os.environ["PARALEAN_AGENT"], "--file", sys.argv[3],
                 "--target", t["target"], "--lamport", str(t["lamport"])], d)
        emit("tombstone", r)
        sync(d)
    elif cmd == "hash":
        p = subprocess.run([BIN, "ws-hash", "--write", os.path.join(d, "projection"), *sys.argv[3:]],
                           capture_output=True, text=True, env=env_for(d), check=True)
        print(p.stdout, end="")
    elif cmd == "check":
        for f in sys.argv[3:]:
            emit("check", run([BIN, "ws-check", "--dir", d, f], d, f, check=False))
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
