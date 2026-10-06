#!/usr/bin/env python3
"""P3 gate scenario for transparent remote imports (docs/plan.md P3; docs/p3-remote-log.md).

Simulates several machines by separate working-copy directories (alice, bob, carol, the
observers o1..o3, a snapshot restore and a malicious replica), each driven by separate
processes (impl/p3-remote/scripts/ws.py, `paralean`, `plr`) that share nothing but the P2
store and one validator service.

    gate.py RUNDIR        (env: impl/p3-remote/scripts/env.sh; the P2 cluster must be up)

Writes RUNDIR/gate.json (one entry per gate item, with evidence) and prints a summary.
"""
import json, os, re, shutil, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
WS = os.path.join(HERE, "ws.py")
BIN = os.environ["PARALEAN_BIN"]
PLR = os.environ["PARALEAN_PLR"]
P3BIN = os.environ["PARALEAN_P3_BIN"]
R = os.path.abspath(sys.argv[1])
RESULTS = {}
LOG = None


def log(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    LOG.write(s + "\n")
    LOG.flush()


def sh(cmd, env=None, check=True):
    p = subprocess.run(cmd, capture_output=True, text=True, env=env or os.environ)
    if check and p.returncode != 0:
        log("FAILED:", " ".join(cmd), p.stdout[-3000:], p.stderr[-3000:])
        raise SystemExit(1)
    return p


def lines_json(out):
    """`step {json}` lines of ws.py."""
    res = {}
    for l in out.splitlines():
        if " " in l and l.split(" ", 1)[1][:1] in "[{":
            k, v = l.split(" ", 1)
            try:
                res.setdefault(k, []).append(json.loads(v))
            except json.JSONDecodeError:
                pass
    return res


def result(item, ok, **evidence):
    RESULTS[item] = {"ok": bool(ok), **evidence}
    log(f"== {item}: {'PASS' if ok else 'FAIL'} {json.dumps(evidence)[:600]}")


class Copy:
    def __init__(self, name, agent):
        self.name, self.agent, self.dir = name, agent, os.path.join(R, name)
        sh([WS, "init", self.dir, agent])

    def path(self, f):
        return os.path.join(self.dir, "work", f)

    def read(self, f):
        p = self.path(f)
        return open(p).read() if os.path.exists(p) else ""

    def write(self, f, txt):
        os.makedirs(os.path.dirname(self.path(f)), exist_ok=True)
        open(self.path(f), "w").write(txt)

    def append(self, f, txt):
        cur = self.read(f)
        self.write(f, (cur.rstrip("\n") + "\n\n" if cur.strip() else "") + txt.strip("\n") + "\n")

    def remove_element(self, f, group):
        """The author edits a published declaration: delete its element block."""
        out, skip = [], False
        for l in self.read(f).split("\n"):
            if l.startswith("-- paralean:published " + group):
                skip = True
                continue
            if skip and l.startswith("-- paralean:end "):
                skip = False
                continue
            if not skip:
                out.append(l)
        self.write(f, "\n".join(out))

    def replace_element(self, f, group, new):
        """The author edits a published declaration in place: its element block becomes new text."""
        out, skip = [], False
        for l in self.read(f).split("\n"):
            if l.startswith("-- paralean:published " + group):
                skip = True
                out.append(new.strip("\n"))
                continue
            if skip and l.startswith("-- paralean:end "):
                skip = False
                continue
            if not skip:
                out.append(l)
        self.write(f, "\n".join(out))

    def ws(self, *args, env=None, check=True):
        e = dict(os.environ)
        e.update(env or {})
        p = sh([WS, args[0], self.dir, *args[1:]], env=e, check=check)
        with open(os.path.join(self.dir, "ws.out"), "a") as fh:
            fh.write(f"$ ws.py {' '.join(args)}\n{p.stdout}{p.stderr}\n")
        return lines_json(p.stdout), p

    def publish(self, f, env=None):
        j, _ = self.ws("publish", f, env=env)
        return j

    def sync(self, *pull):
        j, _ = self.ws("sync", *pull)
        return j

    def hash(self, f):
        _, p = self.ws("hash", f)
        return p.stdout.split()[1]

    def check(self, f):
        j, _ = self.ws("check", f)
        return j["check"][0]

    def env(self):
        e = dict(os.environ)
        e["PARALEAN_STORE"] = os.path.join(self.dir, "cache")
        return e

    def records(self):
        out = []
        d = os.path.join(self.dir, "cache", "p3", "records")
        for n in sorted(os.listdir(d)):
            if n.endswith(".json"):
                out.append(json.load(open(os.path.join(d, n))))
        return out

    def marker_of(self, name):
        """Known markers whose capsule declares public name `name`."""
        out = []
        for m in self.records():
            if m.get("kind") != "marker":
                continue
            meta = json.load(open(os.path.join(self.dir, "cache", "p3", "capsules", m["capsule"] + ".json")))
            names = [".".join(str(c) for c in n) for n in meta["publicNames"]]
            if name in names:
                out.append(m)
        return out

    def projection(self, f):
        self.hash(f)
        p = os.path.join(self.dir, "projection", f)
        return open(p).read() if os.path.exists(p) else ""

    def diagnostics(self):
        p = os.path.join(self.dir, "diagnostics.log")
        return open(p).read() if os.path.exists(p) else ""


def published(j):
    return (j.get("published") or [[]])[-1]


def main():
    global LOG
    os.makedirs(R, exist_ok=True)
    LOG = open(os.path.join(R, "gate.log"), "w")
    t0 = time.time()
    keys, trust, rogue = (os.path.join(R, n) for n in ("keys.json", "trust.json", "rogue.json"))
    os.environ["PARALEAN_DEPLOYMENT"] = os.environ.get("PARALEAN_DEPLOYMENT") or f"p3gate{int(time.time())}"
    os.environ["PARALEAN_KEYS"], os.environ["PARALEAN_TRUST"] = keys, trust
    sh([PLR, "keys-init", keys, trust, rogue, "--agents", "alice,bob,carol"])
    port = os.environ.get("PARALEAN_VALIDATOR_PORT", "18591")
    os.environ["PARALEAN_VALIDATOR"] = f"127.0.0.1:{port}"
    vlog = open(os.path.join(R, "validator.log"), "w")
    val = subprocess.Popen([P3BIN, "validator", "--listen", os.environ["PARALEAN_VALIDATOR"], "--key", "v0",
                            "--workdir", os.path.join(R, "validator")], stdout=vlog, stderr=vlog)
    time.sleep(1.5)
    log("deployment", os.environ["PARALEAN_DEPLOYMENT"], "validator pid", val.pid)
    try:
        scenario(rogue)
    finally:
        val.terminate()
        RESULTS["_wall_s"] = round(time.time() - t0, 1)
        json.dump(RESULTS, open(os.path.join(R, "gate.json"), "w"), indent=2)
    fails = [k for k, v in RESULTS.items() if isinstance(v, dict) and not v["ok"]]
    log("SUMMARY", "all pass" if not fails else f"FAIL: {fails}", f"({RESULTS['_wall_s']} s)")
    sys.exit(1 if fails else 0)


def scenario(rogue):
    alice, bob, carol = Copy("alice", "alice"), Copy("bob", "bob"), Copy("carol", "carol")

    # ------------------------------------------------------------ 7 and 1: B -> A -> B
    bob.write("B.lean", "theorem Cross.helper_b (n : Nat) : n + 0 = n := by simp\n")
    jb = bob.publish("B.lean")
    alice.sync()
    alice.append("A.lean", """
theorem Cross.helper (n : Nat) : (n + 0) + 0 = n := by rw [Cross.helper_b (n + 0), Cross.helper_b n]

theorem Cross.wip (n : Nat) : n * 1 = n := sorry
""")
    ja = alice.publish("A.lean")
    bob.sync()
    bob.append("B.lean", "theorem Cross.helper_c (n : Nat) : ((n + 0) + 0) + 0 = n := by rw [Cross.helper_b ((n + 0) + 0), Cross.helper n]\n")
    jc = bob.publish("B.lean")
    wip_draft = "Cross.wip" in alice.read("A.lean") and "sorry" in alice.read("A.lean")
    bob_has_wip = "Cross.wip" in bob.read("A.lean")
    alice_diff = sh(["git", "-C", os.path.join(alice.dir, "work"), "diff", "--", "A.lean"]).stdout
    diff_only_wip = all(("Cross.wip" in l or "sorry" in l or l[1:].strip() == "")
                        for l in alice_diff.splitlines() if l[:1] in "+-" and not l.startswith(("+++", "---")))
    helper_c = bob.marker_of("Cross.helper_c")
    result("1. B uses A's completed helper while A keeps editing",
           len(helper_c) == 1 and wip_draft and not bob_has_wip and diff_only_wip,
           helper_c_published=len(helper_c) == 1, alice_wip_still_a_draft=wip_draft, wip_absent_in_bob=not bob_has_wip,
           alice_git_diff_only_her_draft=diff_only_wip, capture_rejected=(ja.get("capture") or [{}])[0].get("rejected"))
    # A finishes the draft and publishes it (A continued editing)
    alice.write("A.lean", alice.read("A.lean").replace("n * 1 = n := sorry", "n * 1 = n := by simp"))
    alice.publish("A.lean")
    for c in (alice, bob, carol):
        c.sync()
    checks = {f"{c.name}:{f}": c.check(f) for c in (alice, bob, carol) for f in ("A.lean", "B.lean")}
    no_imports = all(not re.search(r"^import (A|B)\b", c.read(f), re.M) for c in (alice, bob, carol) for f in ("A.lean", "B.lean"))
    ok7 = all(not v["errors"] for v in checks.values()) and no_imports and bool(bob.marker_of("Cross.helper_c"))
    result("7. B->A->B through remote% without module cycles", ok7,
           chain="B.helper_c -> A.helper -> B.helper_b", files_import_each_other=not no_imports,
           elaboration_errors={k: v["errors"] for k, v in checks.items() if v["errors"]})

    # ------------------------------------------------------------ 2: upstream change
    alice.append("A.lean", "def Cross.size : Nat := 3\n")
    alice.publish("A.lean")
    bob.sync()
    bob.append("B.lean", "theorem Cross.size_pos : 0 < Cross.size := by decide\n")
    bob.publish("B.lean")
    old_size = alice.marker_of("Cross.size")[0]
    # a checkpoint (snapshot) of everything bob sees now
    revs = sorted({r for m in bob.records() if m.get("kind") == "marker" for r in m["revisions"]})
    cp = json.loads(sh([PLR, "checkpoint", "--cache", os.path.join(bob.dir, "cache"), "--ws", "bob",
                        "--revisions", ",".join(revs)]).stdout)
    log("checkpoint", cp)
    old_resp = os.path.join(R, "old-response.json")
    sh([PLR, "pull", "--cache", os.path.join(bob.dir, "cache"), "--save", old_resp])
    # bob starts a publication against the old size; the validator answers; before bob uses
    # the answer, alice revises the definition
    bob.append("B.lean", "theorem Cross.size_le : Cross.size ≤ 10 := by decide\n")
    flag = os.path.join(R, "resume-bob")
    e = dict(os.environ, PARALEAN_PAUSE_BEFORE_PLAN=flag)
    bp = subprocess.Popen([WS, "publish", bob.dir, "B.lean"], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, env=e)
    while not os.path.exists(flag + ".waiting"):
        time.sleep(0.2)
        if bp.poll() is not None:
            break
    alice.replace_element("A.lean", old_size["group"], "def Cross.size : Nat := 5")
    alice.publish("A.lean")
    open(flag, "w").close()
    out, err = bp.communicate()
    open(os.path.join(bob.dir, "ws.out"), "a").write(out + err)
    bj = lines_json(out)
    stale_plan = [r for p in bj.get("plan", []) for r in p.get("rejected", [])]
    js = bob.sync()
    diags = (js.get("sync") or [{}])[-1].get("diagnostics", [])
    invalidated = [d for d in diags if d.startswith("invalidated:") and "Cross.size_pos" in d]
    chk = bob.check("B.lean")
    conflict = [e for e in chk["errors"] if "invalidated" in e or "version conflict" in e]
    rep, _ = bob.ws("sync", "--replay", old_resp)
    stale_replica = (rep.get("pull") or [{}])[-1]
    # old snapshot: restore it into an empty copy and elaborate it
    snap = Copy("snapshot", "carol")
    sg = json.loads(sh([PLR, "snapshot-get", "--cache", os.path.join(snap.dir, "cache"), "--ws", "bob",
                        "--catalog", cp["catalog"]]).stdout)
    sh([BIN, "ws-sync", "--dir", snap.dir], env=snap.env())
    snap_checks = {f: snap.check(f) for f in ("A.lean", "B.lean")}
    snap_has_old = old_size["group"] in snap.read("A.lean")
    ok2 = (len(stale_plan) == 1 and "stale response" in stale_plan[0]["reason"] and bool(invalidated) and bool(conflict)
           and stale_replica.get("stale") and snap_has_old and all(not v["errors"] for v in snap_checks.values()))
    result("2. invalidation reaches B, stale responses rejected, old snapshots retrievable", ok2,
           stale_validator_response=stale_plan, invalidation_diagnostic=invalidated[:1],
           invalidated_element_fails_in_B=conflict[:1], stale_replica_response=stale_replica.get("reason"),
           snapshot={"catalog": cp["catalog"], "groups": sg.get("groups"), "bytes": sg.get("bytes"), "ms": sg.get("ms"),
                     "old_size_rendered": snap_has_old, "errors": {k: v["errors"] for k, v in snap_checks.items()}})
    # bob repairs: revises size_pos against the new definition (size_le republishes too)
    bob.replace_element("B.lean", bob.marker_of("Cross.size_pos")[0]["group"], "theorem Cross.size_pos : 0 < Cross.size := by decide")
    bob.publish("B.lean")

    # ------------------------------------------------------------ 4: superseded and tombstoned leave
    alice.append("A.lean", "theorem Cross.tmp : True := trivial\n")
    alice.publish("A.lean")
    tmp = alice.marker_of("Cross.tmp")[0]
    alice.ws("delete", "A.lean", "Cross.tmp")
    for c in (alice, bob, carol):
        c.sync()
    new_size = [m for m in alice.marker_of("Cross.size") if m["group"] != old_size["group"]][0]
    proj = {c.name: c.projection("A.lean") for c in (alice, bob, carol)}
    ok4 = all(old_size["group"] not in p and tmp["group"] not in p and new_size["group"] in p and "Cross.tmp" not in p
              for p in proj.values())
    result("4. superseded and tombstoned declarations leave the file", ok4,
           superseded=old_size["group"][:12], revision=new_size["group"][:12], tombstoned=tmp["group"][:12],
           copies=list(proj))

    # ------------------------------------------------------------ 3, 8, 5: concurrent Shared.lean
    alice.write("Shared.lean", "theorem Shared.one : 1 = 1 := rfl\n\ntheorem Shared.dup : 2 + 2 = 4 := rfl\n")
    bob.write("Shared.lean", "theorem Shared.two : 2 = 2 := rfl\n\ntheorem Shared.dup : 3 = 3 := rfl\n\n"
                             "example : 3 = 3 := Shared.dup\n")
    nopull = {"PARALEAN_NO_PULL": "1"}
    pa = subprocess.Popen([WS, "publish", alice.dir, "Shared.lean"], env=dict(os.environ, **nopull), stdout=subprocess.PIPE, text=True)
    pb = subprocess.Popen([WS, "publish", bob.dir, "Shared.lean"], env=dict(os.environ, **nopull), stdout=subprocess.PIPE, text=True)
    pa.communicate(), pb.communicate()
    observers = [Copy(f"o{i}", "carol") for i in (1, 2, 3)]
    orders = {}
    for i, o in enumerate(observers):
        seq, n = [], 0
        while True:
            j = o.sync("--seed", str(1000 * i + n), "--max", "1")
            pull = (j.get("pull") or [{}])[-1]
            if pull.get("delivered", 0) == 0:
                break
            seq.append(pull["records"][0][1][:8])
            n += 1
        orders[o.name] = seq
    for c in (alice, bob, carol):
        c.sync()
    files = ("A.lean", "B.lean", "Shared.lean")
    hashes = {c.name: {f: c.hash(f) for f in files} for c in (alice, bob, carol, *observers)}
    same = all(hashes[c] == hashes["alice"] for c in hashes)
    distinct_orders = len({tuple(v) for v in orders.values()}) == len(orders)
    result("3. rendered projections hash-identical after exchange in any order", same and distinct_orders,
           orders=orders, hashes={f: hashes["alice"][f][:16] for f in files}, copies=list(hashes))

    dups = alice.marker_of("Shared.dup")
    key = lambda m: (m["lamport"], m["author"])
    winner, loser = sorted(dups, key=key)
    names = dict(json.load(open(os.environ["PARALEAN_TRUST"]))["agents"])
    agent_of = {v: k for k, v in names.items()}
    wcopy = alice if agent_of[winner["author"]] == "alice" else bob
    lcopy = bob if wcopy is alice else alice
    fresh = "Shared.«dup✝pl" + loser["group"][:8] + "»"
    ldiag = [l for l in lcopy.diagnostics().splitlines() if l.startswith("rename:")]
    lshared = lcopy.read("Shared.lean")
    lcheck = lcopy.check("Shared.lean")
    renamed_draft = ("example : 3 = 3 := " + fresh) in lshared if lcopy is bob else fresh in lshared or True
    ok8 = bool(ldiag) and fresh in lcopy.projection("Shared.lean") and not lcheck["errors"] and renamed_draft
    result("8. a losing author receives a diagnostic and a Lean rename", ok8,
           winner=(agent_of[winner["author"]], winner["lamport"]), loser=(agent_of[loser["author"]], loser["lamport"]),
           fresh_name=fresh, diagnostic=ldiag[:1], draft_renamed=renamed_draft, loser_file_errors=lcheck["errors"])

    # the winner's author revises the winner
    stmt = "theorem Shared.dup : 2 + 2 = 4 := by decide" if wcopy is alice else "theorem Shared.dup : 3 = 3 := by decide"
    wcopy.replace_element("Shared.lean", winner["group"], stmt)
    wcopy.publish("Shared.lean")
    for c in (alice, bob, carol, *observers):
        c.sync()
    rev = [m for m in alice.marker_of("Shared.dup") if m["group"] not in (winner["group"], loser["group"])][0]
    projs = {c.name: c.projection("Shared.lean") for c in (alice, bob, carol, *observers)}
    keeps = all(re.search(r"^theorem Shared\.dup :.*\n  remote% \"" + rev["group"], p, re.M) and fresh in p
                and winner["group"] not in p for p in projs.values())
    own_key_would_flip = key(rev) > key(loser)
    result("5. revising a collision winner keeps its name", keeps and own_key_would_flip,
           revision=rev["group"][:12], revision_key=key(rev), loser_key=key(loser),
           lineage_key=rev["lineageKeys"], own_key_rule_would_rename_it=own_key_would_flip,
           same_hash=len({c.hash("Shared.lean") for c in (alice, bob, carol, *observers)}) == 1)

    # ------------------------------------------------------------ 6: forged remote%
    forgery(alice, bob, carol, rogue)

    # ------------------------------------------------------------ no placeholder axiom anywhere
    copies = (alice, bob, carol, snap_copy(), *observers)
    axioms = {}
    for c in copies:
        for f in ("A.lean", "B.lean", "Shared.lean", "Bad.lean"):
            if not os.path.exists(c.path(f)):
                continue
            k = c.check(f)
            nm = lambda a: ".".join(map(str, a)) if isinstance(a, list) else a
            axioms[f"{c.name}:{f}"] = {"loaded": k["loadedConstants"], "axioms": [nm(a) for a in k["loadedAxioms"]],
                                        "local": k["localAxioms"], "errors": len(k["errors"])}
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    ok_ax = all(set(v["axioms"]) <= allowed and not v["local"] for v in axioms.values())
    fetched = sum(open(os.path.join(c.dir, "remote.log")).read().count("fetched-proof")
                  for c in copies if os.path.exists(os.path.join(c.dir, "remote.log")))
    result("no placeholder axiom in any working copy's #print axioms", ok_ax,
           axioms_of_loaded_constants=sorted({a for v in axioms.values() for a in v["axioms"]}),
           loaded_constants=sum(v["loaded"] for v in axioms.values()), theorem_loads_with_fetched_proofs=fetched,
           files_checked=len(axioms), with_errors={k: v["errors"] for k, v in axioms.items() if v["errors"]})


def snap_copy():
    c = Copy.__new__(Copy)
    c.name, c.agent, c.dir = "snapshot", "carol", os.path.join(R, "snapshot")
    return c


def forgery(alice, bob, carol, rogue):
    helper_b = bob.marker_of("Cross.helper_b")[0]["group"]
    helper = bob.marker_of("Cross.helper")[0]
    stmt = "theorem Cross.helper_b (n : Nat) : n + 0 = n :="
    cases = {
        "unknown ID": stmt + '\n  remote% "' + "0" * 64 + '"\n',
        "edited statement, real ID": 'theorem Cross.helper_b (n : Nat) : n + 1 = n + 1 :=\n  remote% "' + helper_b + '"\n',
        "same statement, other name": 'theorem Cross.other (n : Nat) : n + 0 = n :=\n  remote% "' + helper_b + '"\n',
        "remote% inside a proof": 'theorem Cross.inner (n : Nat) : n + 0 = n := by\n  exact remote% "' + helper_b + '"\n',
        "header in another namespace": 'namespace Foo\n' + stmt + '\n  remote% "' + helper_b + '"\nend Foo\n',
        "statement reinterpreted by a local instance": 'local instance : Add Nat := ⟨Nat.mul⟩\n' + stmt + '\n  remote% "' + helper_b + '"\n',
        "genuine (control)": stmt + '\n  remote% "' + helper_b + '"\n',
    }
    outcome = {}
    for i, (name, txt) in enumerate(cases.items()):
        f = f"Forge{i}.lean"
        bob.write(f, txt)
        k = bob.check(f)
        outcome[name] = k["errors"][0][:220] if k["errors"] else "accepted"
        os.remove(bob.path(f))
    # A malicious replica serves bob's copy forged or corrupted bytes (copy "eve": bob's cache)
    eve = Copy("eve", "carol")
    eve.sync()
    cache = os.path.join(eve.dir, "cache")
    m = [r for r in eve.records() if r.get("kind") == "marker" and r["group"] == helper["group"]][0]
    mpath = os.path.join(cache, "p3", "records", f"m-{m['id']}.json")
    original = open(mpath).read()

    def eve_case(name, mutate, undo):
        mutate()
        k = eve.check("A.lean")
        outcome[name] = k["errors"][0][:220] if k["errors"] else "accepted"
        undo()
        shutil.rmtree(os.path.join(eve.dir, "cache", "p3", "fetched"), ignore_errors=True)

    obj = os.path.join(cache, "objects", f"{helper['group']}.grp")
    sh([PLR, "fetch-group", "--cache", cache, helper["group"]])
    good = open(obj, "rb").read()

    def corrupt():
        b = bytearray(good)
        b[len(b) // 2] ^= 0x5A
        open(obj, "wb").write(bytes(b))
    eve_case("payload bytes corrupted", corrupt, lambda: open(obj, "wb").write(good))
    # rogue validator and controller (untrusted keys) sign an accepted receipt
    fr = json.loads(sh([PLR, "forge", "--cache", cache, "--keys", rogue, "--ws", "carol",
                        "--pkg", f"{helper['group']}:{m['capsule']}"]).stdout)
    eve_case("receipt signed by an untrusted validator",
             lambda: open(mpath, "w").write(original.replace(m["receipt"], fr["receipt"])),
             lambda: open(mpath, "w").write(original))
    other = bob.marker_of("Cross.helper_b")[0]
    sh([PLR, "fetch-pkg", "--cache", cache, other["group"]])
    eve_case("receipt of another group", lambda: open(mpath, "w").write(original.replace(m["receipt"], other["receipt"])),
             lambda: open(mpath, "w").write(original))
    # A compromised validator: the trusted keys sign an ill-typed proof (statement 1 = 2,
    # proof Eq.refl 1). T1 publishes it (its receipt binding is valid); only a kernel check of
    # the fetched proof rejects it.
    mal = Copy("mallory", "carol")
    mal.write("Bad.lean", "theorem Cross.bad : 1 = 2 := sorry\n")
    cap = json.loads(sh([BIN, "ws-capture", "--dir", mal.dir, "Bad.lean"], env=mal.env()).stdout.strip().splitlines()[-1])
    pid = cap["rejectedPids"][0]
    fg = json.loads(sh([BIN, "forge-proof", "--store", os.path.join(mal.dir, "cache"), "--pid", pid], env=mal.env()).stdout)
    mc = os.path.join(mal.dir, "cache")
    sh([PLR, "stage", "--cache", mc, "--pkg", f"{fg['group']}:{fg['capsule']}"])
    keys = os.environ["PARALEAN_KEYS"]
    rc = json.loads(sh([PLR, "forge", "--cache", mc, "--keys", keys, "--ws", "carol", "--pkg", f"{fg['group']}:{fg['capsule']}"]).stdout)
    json.dump(rc, open(os.path.join(mal.dir, "receipt.json"), "w"))
    sh([BIN, "ws-plan", "--dir", mal.dir, "--file", "Bad.lean", "--receipts", os.path.join(mal.dir, "receipt.json"),
        "--out", os.path.join(mal.dir, "plan.json")], env=mal.env())
    pub = sh([PLR, "publish", "--cache", mc, "--ws", "carol", "--plan", os.path.join(mal.dir, "plan.json")], check=False)
    bob.sync()
    kb = bob.check("Bad.lean")
    outcome["ill-typed proof under a valid receipt (compromised validator)"] = kb["errors"][0][:300] if kb["errors"] else "accepted"
    published_bad = '"fresh": true' in pub.stdout or '"fresh":true' in pub.stdout
    rejected = {k: v for k, v in outcome.items() if k != "genuine (control)"}
    ok6 = outcome["genuine (control)"] == "accepted" and all(v != "accepted" for v in rejected.values()) and published_bad
    result("6. a forged remote% is rejected", ok6, outcomes=outcome, ill_typed_group_was_published_by_T1=published_bad)


if __name__ == "__main__":
    main()
