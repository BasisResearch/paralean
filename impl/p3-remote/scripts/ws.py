#!/usr/bin/env python3
"""One agent's working copy (P3 transparent workspaces).

    ws.py init DIR AGENT
    ws.py publish DIR FILE      capture, then per new group: stage, validate, plan, publish
    ws.py sync DIR [PULL-ARGS]  anti-entropy (plr pull) and working-file update
    ws.py delete DIR FILE NAME  tombstone a live declaration of FILE
    ws.py move DIR FILE NAME [AFTER]  move a live declaration to file start or after NAME
    ws.py rename DIR FILE OLD NEW [DIR2 FILE2]...
                                rename DIR's published OLD in FILE to NEW, revise the elements
                                of each FILE2 (in copy DIR2) that use it, and publish all of it
                                with the deletion of OLD as one atomic batch
    ws.py hash DIR FILE...      published-projection hashes
    ws.py check DIR FILE...     elaborate working files; errors and axioms

Environment (impl/p3-remote/scripts/env.sh): PARALEAN_BIN, PARALEAN_PLR, PARALEAN_KEYS (at
init, the copy takes keys-<agent>.json from its directory: own seeds only),
PARALEAN_TRUST, PARALEAN_DEPLOYMENT, PARALEAN_VALIDATOR (host:port), and the store's.
For target proofs, set PARALEAN_CONTROLLER. Every captured public name is looked up
in the target registry; target groups are sent to the controller. PARALEAN_TARGETS
may supply optional pinned statement hashes as NAME:STATEMENT_HASH entries.
Each step is a separate process; nothing is shared between copies except the store, and,
during a rename, the coordinator's description of the batch and the new declaration's
records it shares with the other copies (see `rename`).
Prints one JSON object per step on stdout (prefixed by the step name).
"""
import json, os, secrets, shutil, subprocess, sys, tempfile, time

BIN = os.environ["PARALEAN_BIN"]
PLR = os.environ["PARALEAN_PLR"]


def env_for(d, file=None, extra=None):
    e = dict(os.environ)
    e.update(extra or {})
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


def run(cmd, d, file=None, check=True, extra=None):
    t = time.time()
    p = subprocess.run(cmd, capture_output=True, text=True, env=env_for(d, file, extra))
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


def write_new_file(path, text):
    """Create a new owner-only file; an existing name or symlink fails closed."""
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
    with os.fdopen(fd, "w") as f:
        f.write(text)


def read_private(path):
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(fd) as f:
        return f.read()


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
        named = {s.split(":", 1)[0]: s for s in os.environ.get("PARALEAN_TARGETS", "").split(",") if s}
        if named and not os.environ.get("PARALEAN_CONTROLLER"):
            raise SystemExit("PARALEAN_TARGETS requires PARALEAN_CONTROLLER")
        selected = []
        if os.environ.get("PARALEAN_CONTROLLER"):
            for n in p["names"]:
                rec = run([PLR, "target-get", "--name", n], d)
                if rec["exists"]:
                    selected.append(named.get(n, n))
                elif n in named:
                    raise SystemExit(f"target {n} has no controller assignment")
        cmd = [PLR, "validate", "--cache", cache(d), "--ws", os.environ["PARALEAN_AGENT"],
               "--validator", os.environ["PARALEAN_VALIDATOR"], "--pkg", pkg, "--deps", ",".join(p["deps"])]
        if selected:
            cmd += ["--controller", os.environ["PARALEAN_CONTROLLER"], "--targets", ",".join(selected)]
        v = run(cmd, d, check=False)
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
        # The working copy's folder may hold planted symlinks, so the receipt and plan live
        # in a fresh owner-only directory outside it (W2-20), written without following links.
        with tempfile.TemporaryDirectory(prefix="ws-publish-") as staging:
            rpath = os.path.join(staging, "receipt.json")
            write_new_file(rpath, json.dumps(v))
            plan = os.path.join(staging, "plan.json")
            pl = run([BIN, "ws-plan", "--dir", d, "--file", file, "--receipts", rpath, "--out", plan], d, file)
            emit("plan", pl)
            if pl.get("planned", 0) == 0:
                continue
            if selected:
                entries = json.loads(read_private(plan))
                for entry in entries:
                    if entry["group"] == p["group"]:
                        entry["targets"] = v["targets"]
                plan = os.path.join(staging, "plan-targets.json")
                write_new_file(plan, json.dumps(entries))
            pub = run([PLR, "publish", "--cache", cache(d), "--ws", os.environ["PARALEAN_AGENT"], "--plan", plan],
                      d, check=False)
        if "error" in pub:
            emit("publish_rejected", {"group": p["group"], "reason": pub["error"]})
            continue
        emit("publish", pub)
        run([PLR, "pull", "--cache", cache(d), "--only", p["group"]], d)
        published.append(p["group"])
    if not os.environ.get("PARALEAN_NO_PULL"):
        sync(d)
    else:
        emit("sync", run([BIN, "ws-sync", "--dir", d], d))
    return published


def agent(d):
    return open(os.path.join(d, "agent")).read().strip()


def capture_rewritten(d, file, rw, extra=None):
    """Capture `file` after `ws-rename`; stage and return the packages of the rewritten elements."""
    cap = run([BIN, "ws-capture", "--dir", d, file], d, file, extra=extra)
    names = {n for r in rw["rewritten"] for n in r["names"]}
    pkgs = [p for p in cap["packages"] if names & set(p["names"])]
    missing = names - {n for p in pkgs for n in p["names"]}
    if missing or cap["rejected"]:
        raise SystemExit(f"rename: {file} in {d} does not capture {sorted(missing)}: {cap['rejected']}")
    for p in pkgs:
        run([PLR, "stage", "--cache", cache(d), "--pkg", f'{p["group"]}:{p["capsule"]}'], d)
    emit("capture", {"dir": d, "file": file, "packages": [p["names"] for p in pkgs]})
    return pkgs


def rename(d, file, old, new, users):
    """A published rename as one atomic batch (docs/atomic-pub-log.md), coordinated by the
    copy `d` that owns `old`:

    1. `d` replaces `old`'s element in `file` with its source under `new` (`ws-rename`),
       captures it, and has the new declaration checked under a fresh staging ID: a job
       bound to that ID, which no transaction publishes (`plr validate --bind`).
    2. Each other copy gets that declaration's records in `cache/p3/staged/<ID>` (`plr
       batch-share`), rewrites its elements that use `old`, and captures them with
       `PARALEAN_BATCH=<ID>`: name resolution and `remote%` see the staged declaration, with
       its receipt, capsule hash and command gate checked as for a published one.
    3. `d` signs a target-free intent with its job-issuer key: the new declaration (and its
       file's revised users), the deletion of `old`'s position, the other copies' revisions.
       All jobs are bound to the intent and validated in order in one validator batch.
    4. Every copy plans its records and signs its own members' certificates; `d` publishes
       the batch with one T12 transaction. Nothing of it is visible unless all of it is.

    The description stays in `d`'s cache (`p3/batches`, owner-only); receipts and plans are
    staged in fresh owner-only directories outside the copies (W2-20)."""
    copies = [(d, file)] + users
    for c, _ in copies:
        r = run([PLR, "pull", "--cache", cache(c)], c)
        if r.get("stale"):
            raise SystemExit(f"rename: {c}: {r['reason']}")
        run([BIN, "ws-sync", "--dir", c], c)
    staging = secrets.token_hex(32)
    validator = os.environ["PARALEAN_VALIDATOR"]
    rw = run([BIN, "ws-rename", "--dir", d, "--file", file, "--name", old, "--to", new], d)
    if not rw["declares"]:
        raise SystemExit(f"rename: {old} is not declared in {file} of {d}")
    members = {d: capture_rewritten(d, file, rw)}
    decl = next(p for p in members[d] if new in p["names"])
    preview = run([PLR, "validate", "--cache", cache(d), "--ws", agent(d), "--validator", validator,
                   "--pkg", f'{decl["group"]}:{decl["capsule"]}', "--deps", ",".join(decl["deps"]), "--bind", staging],
                  d, check=False)
    emit("validate", {"names": decl["names"], "staging": staging, "accepted": preview.get("accepted", False),
                      "reason": preview.get("reason", preview.get("error", ""))[:300]})
    if not preview.get("accepted"):
        raise SystemExit(f"rename: {new} is not accepted")
    pub = {"error": "not attempted"}
    try:
        for u, ufile in users:
            run([PLR, "batch-share", "--cache", cache(d), "--to", cache(u), "--staging", staging,
                 "--pkg", f'{decl["group"]}:{decl["capsule"]}', "--receipt", preview["receipt"]], d)
            urw = run([BIN, "ws-rename", "--dir", u, "--file", ufile, "--name", old, "--to", new], u)
            members[u] = capture_rewritten(u, ufile, urw, extra={"PARALEAN_BATCH": staging})
            for p in members[u]:
                if decl["capsule"] not in p["deps"] or rw["old"]["capsule"] in p["deps"]:
                    raise SystemExit(f"rename: {p['names']} in {u} does not use {new} in place of {old}")
        t = run([BIN, "ws-delete", "--dir", d, "--file", file, "--name", old], d)
        spec = [f'publish:{p["group"]}:{p["capsule"]}:{agent(d)}:{",".join(p["deps"])}' for p in members[d]]
        spec.append(f'tombstone:{t["target"]}:{t["position"]}:{t["lamport"]}:{agent(d)}:{file}')
        spec += [f'publish:{p["group"]}:{p["capsule"]}:{agent(u)}:{",".join(p["deps"])}' for u, _ in users for p in members[u]]
        intent = run([PLR, "batch-intent", "--cache", cache(d), "--ws", agent(d), "--staging", staging,
                      "--member", *spec], d)
        batch = intent["description"]
        emit("intent", {"batch": intent["batch"], "members": intent["members"]})
        v = run([PLR, "batch-validate", "--cache", cache(d), "--ws", agent(d), "--batch", batch,
                 "--validator", validator], d)
        emit("validate", {"members": [{k: m[k] for k in ("writer", "accepted", "reason")} for m in v["members"]], "ms": v["ms"]})
        if not all(m["accepted"] for m in v["members"]):
            raise SystemExit("rename: a member is not accepted; nothing is published")
        for c, f in copies:
            mine = [m for m in v["members"] if m["writer"] == agent(c)]
            with tempfile.TemporaryDirectory(prefix="ws-rename-") as staging_dir:
                rpath = os.path.join(staging_dir, "receipts.json")
                write_new_file(rpath, json.dumps(mine))
                plan = os.path.join(staging_dir, "plan.json")
                pl = run([BIN, "ws-plan", "--dir", c, "--file", f, "--receipts", rpath, "--out", plan], c, f)
                emit("plan", pl)
                if pl.get("planned", 0) != len(mine):
                    raise SystemExit(f"rename: {c} could not plan its members: {pl.get('rejected')}")
                emit("sign", run([PLR, "batch-sign", "--cache", cache(c), "--ws", agent(c), "--batch", batch,
                                  "--plan", plan], c))
        if os.environ.get("PARALEAN_PAUSE_BEFORE_BATCH"):
            # test hook: forged and partial attempts against the prepared batch
            flag = os.environ["PARALEAN_PAUSE_BEFORE_BATCH"]
            with open(flag + ".waiting", "w") as f:
                json.dump({"description": batch, "batch": intent["batch"]}, f)
            while not os.path.exists(flag):
                time.sleep(0.2)
        pub = run([PLR, "publish-batch", "--cache", cache(d), "--batch", batch], d, check=False)
        emit("publish_batch" if "error" not in pub else "publish_rejected", pub)
    finally:
        # the staged records served the captures only; every copy then syncs, which also
        # ends a planned publication that did not happen (pending.json)
        for u, _ in users:
            shutil.rmtree(os.path.join(cache(u), "p3", "staged", staging), ignore_errors=True)
        for c, _ in copies:
            sync(c)
    return "error" not in pub


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
                 "--target", t["target"], "--position", t["position"], "--lamport", str(t["lamport"])], d)
        emit("tombstone", r)
        sync(d)
    elif cmd == "move":
        pending = os.path.join(d, "pending-move.json")
        if os.path.exists(pending):
            m = json.load(open(pending))
            if m["file"] != sys.argv[3]:
                raise SystemExit(f"finish pending move of {m['file']} before moving another file")
        else:
            plan = [BIN, "ws-move", "--dir", d, "--file", sys.argv[3], "--name", sys.argv[4]]
            if len(sys.argv) > 5:
                plan += ["--after", sys.argv[5]]
            m = run(plan, d)
            with open(pending, "w") as f:
                json.dump(m, f)
        args = [PLR, "move", "--cache", cache(d), "--ws", os.environ["PARALEAN_AGENT"],
                "--file", sys.argv[3], "--target", m["target"], "--position", m["position"],
                "--lamport", str(m["lamport"])]
        if m["anchor"] is not None:
            args += ["--anchor", m["anchor"]]
        emit("move", run(args, d))
        os.remove(pending)
        sync(d)
    elif cmd == "rename":
        rest = sys.argv[6:]
        if len(sys.argv) < 6 or len(rest) % 2:
            raise SystemExit(__doc__)
        users = [(os.path.abspath(rest[i]), rest[i + 1]) for i in range(0, len(rest), 2)]
        emit("renamed", rename(d, sys.argv[3], sys.argv[4], sys.argv[5], users))
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
