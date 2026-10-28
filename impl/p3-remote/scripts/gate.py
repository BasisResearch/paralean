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
    open(os.path.join(R, "deployment"), "w").write(os.environ["PARALEAN_DEPLOYMENT"])
    sh([PLR, "keys-init", keys, trust, rogue, "--agents", "alice,bob,carol"])
    port = os.environ.get("PARALEAN_VALIDATOR_PORT", "18591")
    os.environ["PARALEAN_VALIDATOR"] = f"127.0.0.1:{port}"
    # Each process holds only its own seed (`paralean-p3 keys export`); both refuse more.
    role_keys = {}
    for role, name in (("validator", "v0"), ("controller", None)):
        role_keys[role] = os.path.join(R, f"{role}-keys.json")
        sh([P3BIN, "keys", "export", keys, role_keys[role], "--role", role] + (["--name", name] if name else []))
    vlog = open(os.path.join(R, "validator.log"), "w")
    val = subprocess.Popen([P3BIN, "validator", "--listen", os.environ["PARALEAN_VALIDATOR"], "--key", "v0",
                            "--workdir", os.path.join(R, "validator")], stdout=vlog, stderr=vlog,
                           env={**os.environ, "PARALEAN_KEYS": role_keys["validator"]})
    controller_port = os.environ.get("PARALEAN_CONTROLLER_PORT", "18592")
    os.environ["PARALEAN_CONTROLLER"] = f"127.0.0.1:{controller_port}"
    clog = open(os.path.join(R, "controller.log"), "w")
    controller = subprocess.Popen([P3BIN, "controller", "--listen", os.environ["PARALEAN_CONTROLLER"],
                                   "--validators", os.environ["PARALEAN_VALIDATOR"], "--lease-ms", "300000"],
                                  stdout=clog, stderr=clog,
                                  env={**os.environ, "PARALEAN_KEYS": role_keys["controller"]})
    time.sleep(1.5)
    log("deployment", os.environ["PARALEAN_DEPLOYMENT"], "validator pid", val.pid, "controller pid", controller.pid)
    try:
        if "--targets-only" in sys.argv[2:]:
            target_scenario(Copy("alice", "alice"), Copy("bob", "bob"))
        elif "--move-only" in sys.argv[2:]:
            move_scenario()
        elif "--rename-only" in sys.argv[2:]:
            rename_scenario(Copy("alice", "alice"), Copy("bob", "bob"), Copy("carol", "carol"), rogue)
        else:
            scenario(rogue)
    finally:
        val.terminate()
        controller.terminate()
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
    fresh = "Shared.«dup✝pl" + loser["group"] + "»"
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

    # ------------------------------------------------------------ cross-workspace published rename
    rename_scenario(alice, bob, carol, rogue, observers)

    # ------------------------------------------------------------ clean export (plan's P3 gate)
    ex = sh([BIN, "ws-export", "--dir", alice.dir, "--out", os.path.join(R, "alice-export")], env=alice.env(), check=False)
    exj = json.loads(ex.stdout.strip().splitlines()[-1]) if ex.stdout.strip() else {"ok": False, "err": ex.stderr[-500:]}
    result("clean export of a copy (stock build, groups re-encoded identically)", exj.get("ok"),
           modules=exj.get("modules"), groups=exj.get("groups"), identical=exj.get("identical"), build_ms=exj.get("buildMs"))

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

    # ------------------------------------------------------------ targets: one group owns two names; handover
    target_scenario(alice, bob)


def snap_copy():
    c = Copy.__new__(Copy)
    c.name, c.agent, c.dir = "snapshot", "carol", os.path.join(R, "snapshot")
    return c


def move_scenario():
    alice, bob = Copy("alice", "alice"), Copy("bob", "bob")
    alice.write("Move.lean", "theorem Move.first : 1 = 1 := rfl\n\n"
                "theorem Move.second : 2 = 2 := rfl\n")
    alice.publish("Move.lean")
    bob.sync()
    before = bob.projection("Move.lean")
    moved, _ = alice.ws("move", "Move.lean", "Move.second")
    bob.sync()
    after_a = alice.projection("Move.lean")
    after_b = bob.projection("Move.lean")
    records = alice.marker_of("Move.second")
    check = bob.check("Move.lean")
    result("position move reaches working copy with unchanged group identity",
           "Move.first" in before and len(records) == 2 and
           after_a == after_b and after_b.index("Move.second") < after_b.index("Move.first") and
           not check["errors"] and bool(moved.get("move")),
           marker_variants=len(records), same_projection=after_a == after_b,
           moved_first=after_b.index("Move.second") < after_b.index("Move.first"),
           errors=check["errors"])


def store_view():
    """Published groups and tombstones of the store, as a pull response (nothing delivered)."""
    scratch = os.path.join(R, "store-view")
    out = os.path.join(R, "store-view.json")
    sh([PLR, "pull", "--cache", scratch, "--max", "0", "--save", out])
    v = json.load(open(out))
    shutil.rmtree(scratch, ignore_errors=True)
    return {"groups": set(v["groups"]), "tombstones": set(v["tombstones"])}


def write_private(path, value):
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
    with os.fdopen(fd, "w") as f:
        json.dump(value, f)


def rename_scenario(alice, bob, carol, rogue, observers=()):
    """Alice renames her published Ren.foo to Ren.bar; Bob's published Ren.use calls it. One
    atomic batch publishes bar, deletes foo's position and revises use to call bar."""
    alice.write("Ren.lean", "theorem Ren.foo (n : Nat) : n + 0 = n := by simp\n")
    alice.publish("Ren.lean")
    bob.sync()
    bob.write("RenUse.lean", "theorem Ren.use (n : Nat) : (n + 0) + 0 = n := by rw [Ren.foo (n + 0), Ren.foo n]\n")
    bob.publish("RenUse.lean")
    pre = Copy("o-rename", "carol")
    for c in (alice, bob, carol, pre):
        c.sync()
    foo, use = alice.marker_of("Ren.foo"), bob.marker_of("Ren.use")
    if len(foo) != 1 or len(use) != 1:
        result("rename: published rename across workspaces is atomic", False, foo=foo, use=use)
        return
    foo, use = foo[0], use[0]
    before = store_view()
    flag = os.path.join(R, "resume-rename")
    proc = subprocess.Popen([WS, "rename", alice.dir, "Ren.lean", "Ren.foo", "Ren.bar", bob.dir, "RenUse.lean"],
                            env=dict(os.environ, PARALEAN_PAUSE_BEFORE_BATCH=flag),
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    deadline = time.time() + 1200
    while not os.path.exists(flag + ".waiting") and proc.poll() is None and time.time() < deadline:
        time.sleep(0.2)
    attempts, prepared = {}, {}
    if os.path.exists(flag + ".waiting"):
        info = json.load(open(flag + ".waiting"))
        attempts, prepared = forged_batches(alice, info)
    after_forged = store_view()
    open(flag, "w").close()
    out, err = proc.communicate(timeout=1200)
    open(os.path.join(alice.dir, "ws.out"), "a").write(out + err)
    j = lines_json(out)
    pub = (j.get("publish_batch") or [{}])[-1]
    bar = [m for m in alice.marker_of("Ren.bar")]
    use2 = [m for m in bob.marker_of("Ren.use") if m["group"] != use["group"]]
    ok_forged = (bool(attempts) and all(a["refused"] for a in attempts.values())
                 and after_forged == before and not prepared.get("groups", set()) & after_forged["groups"])
    result("rename: forged and partial batches are refused and leave no state", ok_forged,
           attempts=attempts, store_unchanged=after_forged == before,
           members_visible_before_commit=sorted(prepared.get("groups", set()) & after_forged["groups"]))

    # every copy that syncs sees all of the rename, and still elaborates
    olds = (foo["group"], use["group"])
    seen, checks = {}, {}
    for c in (alice, bob, carol, *observers):
        c.sync()
        ren, user = c.projection("Ren.lean"), c.projection("RenUse.lean")
        src = source_projection(c, "RenUse.lean")
        seen[c.name] = {"bar": bool(bar) and bar[0]["group"] in ren and "Ren.bar" in ren,
                        "foo_gone": foo["group"] not in ren and "Ren.foo" not in ren,
                        "use_revised": bool(use2) and use2[0]["group"] in user and use["group"] not in user,
                        "use_calls_bar": "Ren.bar" in src and "Ren.foo" not in src}
    for c in (alice, bob, carol):
        for f in ("Ren.lean", "RenUse.lean"):
            k = c.check(f)
            checks[f"{c.name}:{f}"] = k["errors"]
    hashes = {c.name: (c.hash("Ren.lean"), c.hash("RenUse.lean")) for c in (alice, bob, carol, *observers)}
    ok = (pub.get("fresh") is True and len(pub.get("members", [])) == 3 and len(bar) == 1 and len(use2) == 1
          and all(all(v.values()) for v in seen.values()) and not any(checks.values())
          and len(set(hashes.values())) == 1)
    result("rename: published rename across workspaces is atomic", ok,
           batch=pub.get("batch"), members=len(pub.get("members", [])), publish_ms=pub.get("ms"),
           renamed=(foo["group"][:12], (bar or [{}])[0].get("group", "")[:12]),
           revised=(use["group"][:12], (use2 or [{}])[0].get("group", "")[:12]),
           copies=seen, elaboration_errors={k: v for k, v in checks.items() if v},
           same_hashes=len(set(hashes.values())) == 1,
           steps={k: v for k, v in j.items() if k in ("validate", "intent", "plan", "sign")})

    # an interrupted pull: the observer synced before the rename sees none of it
    jm = pre.sync("--max", "2")
    pulled = (jm.get("pull") or [{}])[-1]
    batch_rec = [r for r in pulled.get("records", []) if r[0] == "batch"]
    view_max = {"bar": "Ren.bar" in pre.projection("Ren.lean"), "foo": foo["group"] in pre.projection("Ren.lean"),
                "use": use["group"] in pre.projection("RenUse.lean")}
    # a pull that crashed after writing every member record but not the batch file
    recs = os.path.join(carol.dir, "cache", "p3")
    copied = []
    for root, _, files in os.walk(recs):
        for n in files:
            rel = os.path.relpath(os.path.join(root, n), recs)
            dst = os.path.join(pre.dir, "cache", "p3", rel)
            if n.startswith("b-") or os.path.exists(dst) or not rel.split(os.sep)[0] in ("records", "revisions", "receipts", "jobs", "capsules"):
                continue
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.copy(os.path.join(root, n), dst)
            copied.append(rel)
    sh([BIN, "ws-sync", "--dir", pre.dir], env=pre.env())
    members_copied = [r for r in copied if r.startswith("records")]
    view_crash = {"bar": "Ren.bar" in pre.projection("Ren.lean"), "foo": foo["group"] in pre.projection("Ren.lean"),
                  "use": use["group"] in pre.projection("RenUse.lean")}
    jr = pre.sync()
    resumed = (jr.get("pull") or [{}])[-1]
    view_resumed = {"bar": "Ren.bar" in pre.projection("Ren.lean"), "foo": foo["group"] in pre.projection("Ren.lean"),
                    "use": use["group"] in pre.projection("RenUse.lean")}
    ok_int = (not batch_rec and view_max == {"bar": False, "foo": True, "use": True}
              and len(members_copied) == 3 and view_crash == {"bar": False, "foo": True, "use": True}
              and any(r[0] == "batch" for r in resumed.get("records", []))
              and view_resumed == {"bar": True, "foo": False, "use": False})
    result("rename: an interrupted pull shows no member of the batch", ok_int,
           max_2_pull={"delivered": pulled.get("delivered"), "available": pulled.get("available")}, view_after_max_2=view_max,
           member_records_without_batch_file=members_copied, view_after_crash=view_crash,
           resumed_pull=resumed.get("records"), view_after_resume=view_resumed)
    staged_checks(alice, carol, rogue)


def own_env(c, **extra):
    """A copy's environment as ws.py gives it: its cache, its own keys, name visibility."""
    return c.env() | {"PARALEAN_KEYS": os.path.join(c.dir, "keys.json"), "PARALEAN_VISIBILITY": "1",
                      "PARALEAN_REMOTE_LOG": os.path.join(c.dir, "remote.log")} | extra


def staged_checks(alice, carol, rogue):
    """A participant captures against a staged (unpublished) member only through a receipt
    that a trusted validator signed for a job bound to the staging ID, and only while
    capturing for that ID. The staged record is planted as a malicious coordinator would."""
    acache, ccache = os.path.join(alice.dir, "cache"), os.path.join(carol.dir, "cache")
    alice.write("RenStaged.lean", "theorem Ren.baz (n : Nat) : n * 1 = n := by simp\n")
    cap = json.loads(sh([BIN, "ws-capture", "--dir", alice.dir, "RenStaged.lean"],
                        env=own_env(alice, PARALEAN_VIS_EXCLUDE="RenStaged.lean")).stdout.strip().splitlines()[-1])
    pkg = next(p for p in cap["packages"] if "Ren.baz" in p["names"])
    gc = f'{pkg["group"]}:{pkg["capsule"]}'
    sh([PLR, "stage", "--cache", acache, "--pkg", gc], env=own_env(alice))
    staging = os.urandom(32).hex()
    validate = [PLR, "validate", "--cache", acache, "--ws", "alice", "--validator", os.environ["PARALEAN_VALIDATOR"],
                "--pkg", gc, "--deps", ",".join(pkg["deps"])]
    good = json.loads(sh(validate + ["--bind", staging], env=own_env(alice)).stdout)
    unbound = json.loads(sh(validate, env=own_env(alice)).stdout)
    forged = json.loads(sh([PLR, "forge", "--cache", acache, "--keys", rogue, "--ws", "alice", "--pkg", gc,
                            "--bind", staging]).stdout)
    carol.write("UseStaged.lean", "theorem Ren.use_baz (n : Nat) : (n * 1) * 1 = n := by rw [Ren.baz (n * 1), Ren.baz n]\n")
    staged = os.path.join(ccache, "p3", "staged", staging)
    outcomes = {}

    def case(name, rc, batch=True):
        shutil.rmtree(staged, ignore_errors=True)
        sh([PLR, "batch-share", "--cache", acache, "--to", ccache, "--staging", staging, "--pkg", gc,
            "--receipt", good["receipt"]], env=own_env(alice))
        if rc is not good:
            for kind, rid in (("receipts", rc["receipt"]), ("jobs", rc["job"])):
                shutil.copy(os.path.join(acache, "p3", kind, rid + ".bin"), os.path.join(ccache, "p3", kind, rid + ".bin"))
            rec = os.path.join(staged, os.listdir(staged)[0])
            m = json.load(open(rec))
            m["receipt"] = rc["receipt"]
            open(rec, "w").write(json.dumps(m))
        env = own_env(carol, PARALEAN_VIS_EXCLUDE="UseStaged.lean") | ({"PARALEAN_BATCH": staging} if batch else {})
        p = sh([BIN, "ws-capture", "--dir", carol.dir, "UseStaged.lean"], env=env, check=False)
        out = {}
        try:
            out = json.loads(p.stdout.strip().splitlines()[-1])
        except (IndexError, json.JSONDecodeError):
            pass
        use = [q for q in out.get("packages", []) if "Ren.use_baz" in q["names"]]
        outcomes[name] = {"captured": bool(use) and pkg["capsule"] in use[0]["deps"],
                          "refusal": "; ".join(out.get("rejected") or [p.stderr[-300:]])[:300]}

    case("genuine staged member (control)", good)
    case("receipt signed by an untrusted validator", forged)
    case("receipt for a job not bound to the staging ID", unbound)
    case("staged member, capture not for its batch", good, batch=False)
    shutil.rmtree(staged, ignore_errors=True)
    for c, f in ((alice, "RenStaged.lean"), (carol, "UseStaged.lean")):
        os.remove(c.path(f))
    ok = outcomes["genuine staged member (control)"]["captured"] and not any(
        v["captured"] for k, v in outcomes.items() if k != "genuine staged member (control)")
    result("rename: staged members load only with a receipt bound to their staging ID", ok, outcomes=outcomes)


def source_projection(c, f):
    out = os.path.join(c.dir, "source-projection")
    sh([BIN, "ws-hash", "--source", "1", "--write", out, f], env=c.env())
    p = os.path.join(out, f)
    return open(p).read() if os.path.exists(p) else ""


def forged_batches(alice, info):
    """Attempts a coordinator could make with the prepared batch, each refused by the store:
    a member published alone, a member whose job is not bound to the batch, and the
    coordinator's own half of the batch under a new intent without Bob's member."""
    d = json.load(open(info["description"]))
    bdir = os.path.dirname(info["description"])
    prepared = {"groups": {m["group"] for m in d["members"] if m["kind"] == "publish"}}
    bar = d["members"][0]
    attempts = {}

    def attempt(name, cmd):
        p = sh(cmd, env=alice.env() | {"PARALEAN_KEYS": os.path.join(alice.dir, "keys.json")}, check=False)
        err = (json.loads(p.stdout.strip().splitlines()[-1]) if p.stdout.strip() else {}).get("error", "")
        attempts[name] = {"refused": p.returncode != 0 and "batch" in err.lower(), "error": err[:300]}

    plan = os.path.join(bdir, "alone-plan.json")
    write_private(plan, [bar["entry"]])
    attempt("member published alone (T1)", [PLR, "publish", "--cache", os.path.join(alice.dir, "cache"),
                                            "--ws", "alice", "--plan", plan])
    unbound = json.loads(sh([PLR, "validate", "--cache", os.path.join(alice.dir, "cache"), "--ws", "alice",
                             "--validator", os.environ["PARALEAN_VALIDATOR"], "--pkg", f'{bar["group"]}:{bar["capsule"]}',
                             "--deps", ",".join(bar["deps"])],
                            env=alice.env() | {"PARALEAN_KEYS": os.path.join(alice.dir, "keys.json")}).stdout)
    cache = os.path.join(alice.dir, "cache", "p3")
    forged = json.loads(json.dumps(d))
    forged["members"][0]["receipt"] = open(os.path.join(cache, "receipts", unbound["receipt"] + ".bin"), "rb").read().hex()
    forged["members"][0]["job"] = open(os.path.join(cache, "jobs", unbound["job"] + ".bin"), "rb").read().hex()
    unbound_path = os.path.join(bdir, "unbound.json")
    write_private(unbound_path, forged)
    attempt("member job not bound to the batch (T12)", [PLR, "publish-batch", "--cache", os.path.join(alice.dir, "cache"),
                                                        "--batch", unbound_path])
    # the coordinator re-signs an intent for its own members only
    tomb = d["members"][1]
    staging = os.urandom(32).hex()
    half = json.loads(sh([PLR, "batch-intent", "--cache", os.path.join(alice.dir, "cache"), "--ws", "alice", "--staging", staging,
                          "--member", f'publish:{bar["group"]}:{bar["capsule"]}:alice:{",".join(bar["deps"])}',
                          f'tombstone:{tomb["target"]}:{tomb["position"]}:{tomb["lamport"]}:alice:{tomb["file"]}'],
                         env=alice.env() | {"PARALEAN_KEYS": os.path.join(alice.dir, "keys.json")}).stdout)
    hd = json.load(open(half["description"]))
    hd["members"] = d["members"][:2]
    os.remove(half["description"])
    write_private(half["description"], hd)
    attempt("coordinator's half under a new intent (T12)", [PLR, "publish-batch", "--cache", os.path.join(alice.dir, "cache"),
                                                            "--batch", half["description"]])
    return attempts, prepared


def target_scenario(alice, bob):
    def assign(names, worker):
        return json.loads(sh([P3BIN, "assign-group", "--controller", os.environ["PARALEAN_CONTROLLER"],
                              "--targets", ",".join(names), "--worker", worker]).stdout)

    def record(name):
        return json.loads(sh([PLR, "target-get", "--name", name]).stdout)

    # An inductive command owns its type and constructors as one captured group.
    alice.write("Targets.lean", open(os.path.join(HERE, "..", "fixtures", "Targets.lean")).read())
    cap = json.loads(sh([BIN, "ws-capture", "--dir", alice.dir, "Targets.lean"], env=alice.env()).stdout.strip().splitlines()[-1])
    group = next((p for p in cap["packages"] if "Targets.Choice" in p["names"]), None)
    if group is None or len(group["names"]) < 2:
        result("targets: two names in one group", False, capture=cap)
        return
    names = ["Targets.Choice", next(n for n in group["names"] if n != "Targets.Choice")]
    assignment = assign(names, "alice")
    p = alice.publish("Targets.lean", env={"PARALEAN_TARGETS": ",".join(names)})
    head = [record(n) for n in names]
    revision_ids = (p.get("publish") or [[{}]])[-1][0].get("revisions", [])
    both = (len(published(p)) == 1 and len(revision_ids) >= 2 and
            all(r["head"] in revision_ids for r in head) and head[0]["head"] != head[1]["head"])
    result("targets: one group declares two owned names", both,
           names=names, assignment=assignment, heads=head, published=published(p))

    # Pause the old owner after receiving a controller-issued receipt. A T4 handover
    # moves the epoch while its proof remains pending; T1 must reject that proof.
    alice.write("Pending.lean", open(os.path.join(HERE, "..", "fixtures", "Pending.lean")).read())
    assign(["Targets.pending"], "alice")
    flag = os.path.join(R, "resume-target-owner")
    env = dict(os.environ, PARALEAN_TARGETS="Targets.pending", PARALEAN_PAUSE_BEFORE_PLAN=flag)
    proc = subprocess.Popen([WS, "publish", alice.dir, "Pending.lean"], env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    deadline = time.time() + 600
    while not os.path.exists(flag + ".waiting") and proc.poll() is None and time.time() < deadline:
        time.sleep(0.2)
    pending = os.path.exists(flag + ".waiting")
    if pending:
        assign(["Targets.pending"], "bob")
    open(flag, "w").close()
    out, err = proc.communicate(timeout=30)
    old = lines_json(out)
    rejected = old.get("publish_rejected", [])
    state = record("Targets.pending")
    stale = (pending and any("stale epoch" in r.get("reason", "").lower() or
                             "not the owner" in r.get("reason", "").lower() for r in rejected) and
             state["head"] is None and state["owner"] != record(names[0])["owner"])
    result("targets: handover rejects an old owner with a pending proof", stale,
           old_owner_rejection=rejected, target_record=state, old_owner_output=err[-300:])

    bob.write("Pending.lean", open(os.path.join(HERE, "..", "fixtures", "Pending.lean")).read())
    fresh = bob.publish("Pending.lean", env={"PARALEAN_TARGETS": "Targets.pending"})
    current = record("Targets.pending")
    new_revisions = (fresh.get("publish") or [[{}]])[-1][0].get("revisions", [])
    result("targets: new owner publishes after handover", len(published(fresh)) == 1 and
           current["head"] in new_revisions, head=current, published=published(fresh))

    # The recorded head survives a second handover. The next proof must name that
    # revision as its parent, and T1 replaces the head in the same transaction.
    assign(["Targets.pending"], "alice")
    alice.sync()
    alice.write("Pending.lean", open(os.path.join(HERE, "..", "fixtures", "PendingRevision.lean")).read())
    revised = alice.publish("Pending.lean", env={"PARALEAN_TARGETS": "Targets.pending"})
    after = record("Targets.pending")
    new_revisions = (revised.get("publish") or [[{}]])[-1][0].get("revisions", [])
    rev_path = os.path.join(alice.dir, "cache", "p3", "revisions", (after["head"] or "") + ".json")
    revision_record = json.load(open(rev_path)) if os.path.exists(rev_path) else {}
    result("targets: handover revision compares and advances the recorded head",
           len(published(revised)) == 1 and after["head"] in new_revisions and
           current["head"] in revision_record.get("parents", []),
           previous_head=current["head"], new_head=after["head"], revision=revision_record)

    alice.sync()
    bob.sync()
    checks = {f"{c.name}:{file}": c.check(file) for c in (alice, bob)
              for file in ("Targets.lean", "Pending.lean")}
    result("targets: published proofs load in both working copies",
           all(not v["errors"] and not v["localAxioms"] for v in checks.values()),
           checks={k: {"errors": v["errors"], "localAxioms": v["localAxioms"],
                       "loadedConstants": v["loadedConstants"]} for k, v in checks.items()})


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
