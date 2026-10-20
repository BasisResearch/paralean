#!/usr/bin/env python3
"""W5 live method discovery and legacy recapture gate. Source w5-env.sh first.

Run `method OUT` with the normal runtime. To make a genuinely signed legacy package,
copy impl/p1 to a private build directory (including its private .lake), replace the
single `fieldRefs := some fieldRefs` in its Paralean/Capture.lean with
`fieldRefs := none`, and run `$PARALEAN_FORK_PREFIX/bin/lake build paralean` there.
Set PARALEAN_BIN and PARALEAN_LIB to that private build for `legacy-prepare OUT`.
Restore those two environment variables to the normal W5 runtime, then run
`legacy-verify OUT`. Neither step edits the signed capsule or production build.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
WS = ROOT / "impl/p3-remote/scripts/ws.py"


def run(args, *, env=None, check=True):
    p = subprocess.run([str(x) for x in args], capture_output=True, text=True, env=env or os.environ)
    if check and p.returncode:
        raise RuntimeError(f"{args}: {p.returncode}\n{p.stdout[-2500:]}\n{p.stderr[-2500:]}")
    return p


def ws(kind, copy, *args, env=None):
    p = run([WS, kind, copy, *args], env=env)
    rows = []
    for line in p.stdout.splitlines():
        if " " in line:
            key, value = line.split(" ", 1)
            try:
                rows.append((key, json.loads(value)))
            except json.JSONDecodeError:
                pass
    return rows


def value(rows, key):
    found = [v for k, v in rows if k == key]
    if not found:
        raise RuntimeError(f"missing {key}: {rows}")
    return found[-1]


def write(copy, file, source):
    path = copy / "work" / file
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source)


def markers(copy, name):
    out = []
    for path in (copy / "cache/p3/records").glob("*.json"):
        r = json.loads(path.read_text())
        if r.get("kind") != "marker":
            continue
        capsule = copy / "cache/p3/capsules" / (r["capsule"] + ".json")
        g = json.loads(capsule.read_text())
        if name in [".".join(map(str, n)) for n in g["publicNames"]]:
            out.append((r, g, capsule))
    return out


def setup(out):
    if os.environ.get("PARALEAN_INSTANCE") != "p5-w5":
        raise RuntimeError("source impl/p5/scripts/w5-env.sh; only p5-w5 instance is allowed")
    out.mkdir(parents=True, exist_ok=False)
    keys, trust, rogue = [out / x for x in ("keys.json", "trust.json", "rogue.json")]
    os.environ.update(PARALEAN_KEYS=str(keys), PARALEAN_TRUST=str(trust),
                      PARALEAN_DEPLOYMENT=f"w5recapture-{out.name}-{int(time.time())}",
                      PARALEAN_VALIDATOR="127.0.0.1:23691")
    run([os.environ["PARALEAN_PLR"], "keys-init", keys, trust, rogue,
         "--agents", "alice,bob"])
    copies = {a: out / a for a in ("alice", "bob")}
    for a, copy in copies.items():
        ws("init", copy, a)
    return copies


def validator(out):
    log = (out / "validator.log").open("w")
    p = subprocess.Popen([os.environ["PARALEAN_P3_BIN"], "validator", "--listen",
                          os.environ["PARALEAN_VALIDATOR"], "--key", "v0",
                          "--workdir", str(out / "validator")], stdout=log, stderr=log)
    time.sleep(1.5)
    if p.poll() is not None:
        raise RuntimeError((out / "validator.log").read_text())
    return p, log


def stop_validator(pair):
    p, log = pair
    p.terminate()
    p.wait(timeout=10)
    log.close()


def method(out):
    copies = setup(out)
    alice, bob = copies["alice"], copies["bob"]
    server = validator(out)
    try:
        write(alice, "Base.lean", "structure Foo where\n  n : Nat\n")
        value(ws("publish", alice, "Base.lean"), "published")
        write(alice, "Method.lean", "def Foo.field (x : Foo) : Nat := x.n + 1\n")
        value(ws("publish", alice, "Method.lean"), "published")
        ws("sync", bob)
        write(bob, "Use.lean", "def use (x : Foo) : Nat := x.field\n")
        published = value(ws("publish", bob, "Use.lean"), "published")
        if not published:
            raise RuntimeError("unloaded method did not publish")
        use_group = markers(bob, "use")[-1][1]
        if not any(ref.get("target", [None])[-1] == "field" for ref in
                   use_group.get("fieldRefs", []) or []):
            raise RuntimeError("method reference was not captured with a resolved target")
        checked = value(ws("check", bob, "Use.lean"), "check")
        if checked.get("errors"):
            raise RuntimeError(f"unloaded method did not elaborate: {checked}")
        (out / "result.json").write_text(json.dumps({"method": "PASS", "published": published,
                                                      "check": checked}, indent=2) + "\n")
    finally:
        stop_validator(server)


def legacy_prepare(out):
    copies = setup(out)
    alice, bob = copies["alice"], copies["bob"]
    server = validator(out)
    try:
        write(alice, "Base.lean", "structure Foo where n : Nat\nstructure Other where n : Nat\n"
              "def Other.field (x : Other) : Nat := x.n\n")
        value(ws("publish", alice, "Base.lean"), "published")
        ws("sync", bob)
        other = markers(bob, "Other.field")[-1][0]["group"]
        write(alice, "Fields.lean", "def Foo.field (x : Foo) : Nat := x.n + 1\n")
        write(bob, "Fields.lean", f'remote_decl% "{other}"\n'
              "def BobPad : Nat := 0\n"
              "def Foo.field (x : Foo) : Nat := x.n + 2\n"
              "def Foo.use (x : Foo) (y : Other) : Nat := x.field + y.field\n")
        env = dict(os.environ, PARALEAN_NO_PULL="1")
        value(ws("publish", alice, "Fields.lean", env=env), "published")
        value(ws("publish", bob, "Fields.lean", env=env), "published")
        rec, g, path = markers(bob, "Foo.use")[-1]
        if g.get("fieldRefs", "missing") is not None:
            raise RuntimeError("fixture was not captured with legacy fieldRefs = none")
        ids = {"group": rec["group"], "capsule": rec["capsule"],
               "capsuleSha256": hashlib.sha256(path.read_bytes()).hexdigest(),
               "receipt": rec["receipt"]}
        (out / "manifest.json").write_text(json.dumps({"ids": ids,
             "deployment": os.environ["PARALEAN_DEPLOYMENT"], "keys": str(out / "keys.json"),
             "trust": str(out / "trust.json")}, indent=2) + "\n")
    finally:
        stop_validator(server)


def legacy_verify(out):
    manifest = json.loads((out / "manifest.json").read_text())
    os.environ.update(PARALEAN_KEYS=manifest["keys"], PARALEAN_TRUST=manifest["trust"],
                      PARALEAN_DEPLOYMENT=manifest["deployment"])
    alice, bob = out / "alice", out / "bob"
    ws("sync", alice)
    ws("sync", bob)
    ids = manifest["ids"]
    rec, g, path = markers(bob, "Foo.use")[-1]
    if {"group": rec["group"], "capsule": rec["capsule"],
        "capsuleSha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "receipt": rec["receipt"]} != ids:
        raise RuntimeError("signed legacy capsule or receipt changed during recapture")
    if g.get("fieldRefs", "missing") is not None:
        raise RuntimeError("recapture overwrote signed fieldRefs")
    source = out / "source"
    env = dict(os.environ, PARALEAN_STORE=str(bob / "cache"))
    run([os.environ["PARALEAN_BIN"], "ws-hash", "--write", source, "--source", "1",
         "Fields.lean"], env=env)
    text = (source / "Fields.lean").read_text()
    if "x.«field✝pl" not in text or "+ y.field" not in text:
        raise RuntimeError(f"derived field spans did not select original target: {text}")
    checked = value(ws("check", bob, "Fields.lean"), "check")
    if checked.get("errors"):
        raise RuntimeError(f"recaptured legacy projection did not elaborate: {checked}")
    write(bob, "Probe.lean", f'remote_decl% "{ids["group"]}"\n'
          "example : Foo.use ⟨0⟩ ⟨0⟩ = 2 := by decide\n")
    probe = value(ws("check", bob, "Probe.lean"), "check")
    if probe.get("errors"):
        raise RuntimeError(f"recaptured group did not load directly: {probe}")
    bad_env = dict(os.environ, PARALEAN_BIN="/bin/false", PARALEAN_STORE=str(bob / "cache"),
                   PARALEAN_KEYS=str(bob / "keys.json"), PARALEAN_VISIBILITY="1",
                   PARALEAN_VIS_EXCLUDE="Probe.lean")
    bad = json.loads(run([os.environ["PARALEAN_BIN"], "ws-check", "--dir", bob,
                          "Probe.lean"], env=bad_env).stdout)
    if not any("needs recapture" in e for e in bad.get("errors", [])):
        raise RuntimeError(f"failed recapture did not preserve refusal: {bad}")
    (out / "result.json").write_text(json.dumps({"recapture": "PASS", "identity": ids,
                                                   "check": checked, "probe": probe,
                                                   "failedReplay": bad}, indent=2) + "\n")


if __name__ == "__main__":
    action, out = sys.argv[1], Path(sys.argv[2]).resolve()
    {"method": method, "legacy-prepare": legacy_prepare,
     "legacy-verify": legacy_verify}[action](out)
