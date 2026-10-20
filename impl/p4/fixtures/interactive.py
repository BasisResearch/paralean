#!/usr/bin/env python3
"""Build isolated P4 Lean fixtures on this workstream's P2 cluster.

Source impl/p4/scripts/env.sh first, then run one of:

    interactive.py instances OUTDIR
    interactive.py open17 OUTDIR
    interactive.py collision OUTDIR
    interactive.py revocation OUTDIR
    interactive.py revoke OUTDIR/manifest.json

Each build starts one temporary validator and writes a machine-readable manifest.
The revoke operation is intentionally separate, for an editor test to invoke between
two document versions of a still-open Lean server.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
WS = ROOT / "impl/p3-remote/scripts/ws.py"


def run(args, *, env=None, check=True):
    p = subprocess.run([str(a) for a in args], env=env or os.environ, text=True,
                       capture_output=True)
    if check and p.returncode:
        raise RuntimeError(f"{args}: {p.returncode}\n{p.stdout[-2000:]}\n{p.stderr[-2000:]}")
    return p


def ws(kind, copy, *args, env=None):
    p = run([WS, kind, copy, *args], env=env)
    records = []
    for line in p.stdout.splitlines():
        if " " in line:
            label, value = line.split(" ", 1)
            try:
                records.append((label, json.loads(value)))
            except json.JSONDecodeError:
                pass
    return records


def field(records, label):
    values = [value for key, value in records if key == label]
    if not values:
        raise RuntimeError(f"missing {label}: {records}")
    return values[-1]


def write(copy, file, source):
    path = copy / "work" / file
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source)
    return path


def marker(copy, name):
    base = copy / "cache/p3"
    out = []
    for path in (base / "records").glob("*.json"):
        r = json.loads(path.read_text())
        if r.get("kind") != "marker":
            continue
        c = json.loads((base / "capsules" / (r["capsule"] + ".json")).read_text())
        names = [".".join(str(x) for x in n) for n in c["publicNames"]]
        if name in names:
            out.append(r)
    return out


def publish(copy, file, *, no_pull=False):
    env = dict(os.environ)
    if no_pull:
        env["PARALEAN_NO_PULL"] = "1"
    return field(ws("publish", copy, file, env=env), "published")


def setup(out):
    out.mkdir(parents=True, exist_ok=False)
    for key in ("PARALEAN_BIN", "PARALEAN_PLR", "PARALEAN_P3_BIN", "PARALEAN_INSTANCE"):
        if key not in os.environ:
            raise RuntimeError(f"source impl/p4/scripts/env.sh ({key} missing)")
    if os.environ["PARALEAN_INSTANCE"] != "m-p4":
        raise RuntimeError("fixtures must run only on PARALEAN_INSTANCE=m-p4")
    binary = Path(os.environ["PARALEAN_BIN"]).resolve()
    library = Path(os.environ["PARALEAN_LIB"]).resolve()
    runtime = binary.parent.parent if binary.parent.name == "bin" else binary.parent
    keys, trust, rogue = [out / n for n in ("keys.json", "trust.json", "rogue.json")]
    deployment = f"p4interactive-{out.name}-{int(time.time())}"
    os.environ.update(PARALEAN_KEYS=str(keys), PARALEAN_TRUST=str(trust),
                      PARALEAN_DEPLOYMENT=deployment,
                      PARALEAN_VALIDATOR="127.0.0.1:18691")
    run([os.environ["PARALEAN_PLR"], "keys-init", keys, trust, rogue,
         "--agents", "alice,bob"])
    copies = {}
    for agent in ("alice", "bob"):
        copies[agent] = out / agent
        ws("init", copies[agent], agent)
    return copies, {"deployment": deployment, "keys": str(keys),
                    "trust": str(trust), "validator": os.environ["PARALEAN_VALIDATOR"],
                    "runtime": str(runtime), "binary": str(binary),
                    "library": str(library), "p3_bin": os.environ["PARALEAN_P3_BIN"],
                    "p2_environment": {k: os.environ[k] for k in
                                       ("PARALEAN_FDB_CLUSTER", "LD_LIBRARY_PATH")
                                       if k in os.environ}}


def build(kind, out):
    copies, manifest = setup(out)
    manifest["kind"] = kind
    with (out / "validator.log").open("w") as log:
        validator = subprocess.Popen([os.environ["PARALEAN_P3_BIN"], "validator",
                                      "--listen", os.environ["PARALEAN_VALIDATOR"],
                                      "--key", "v0", "--workdir", str(out / "validator")],
                                     stdout=log, stderr=log)
        try:
            time.sleep(1.5)
            if validator.poll() is not None:
                raise RuntimeError("validator exited: " + (out / "validator.log").read_text())
            if kind == "instances":
                instances(copies, manifest)
            elif kind == "open17":
                open17(copies, manifest)
            elif kind == "revocation":
                revocation(copies, manifest)
            elif kind == "collision":
                collision(copies, manifest)
            else:
                raise RuntimeError(kind)
        finally:
            validator.terminate()
            validator.wait(timeout=10)
    manifest["revoke_command"] = [sys.executable, str(Path(__file__).resolve()),
                                  "revoke", str(out / "manifest.json")]
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps(manifest, indent=2))


def instances(copies, manifest):
    alice, bob = copies["alice"], copies["bob"]
    write(alice, "Base.lean", """\
class GlobalTag (α : Type) where
  value : Nat
instance : GlobalTag Nat where
  value := 41
def GlobalProbe.value : Nat := GlobalTag.value Nat
""")
    publish(alice, "Base.lean")
    ws("sync", bob)
    class_group = marker(bob, "GlobalTag")[-1]["group"]
    group = marker(bob, "GlobalProbe.value")[-1]["group"]
    source = (f'remote_decl% "{class_group}"\n' +
              "local instance rootPoison : GlobalTag Nat where value := 999\n" +
              f'remote_decl% "{group}"\n' +
              "example : GlobalProbe.value = 41 := by decide\n")
    document = write(bob, "P4Instance.lean", source)
    manifest.update(workspace_root=str(bob / "work"), document=str(document),
                    class_group=class_group, group=group,
                    expected_value="41", expected_diagnostics=[])


def open17(copies, manifest):
    alice, bob = copies["alice"], copies["bob"]
    write(alice, "Base.lean", """\
structure Foo where n : Nat
structure Other where n : Nat
def Other.field (x : Other) : Nat := x.n
""")
    publish(alice, "Base.lean")
    ws("sync", bob)
    other_group = marker(bob, "Other.field")[-1]["group"]
    a = "def Foo.field (x : Foo) : Nat := x.n + 1\n"
    b = f'''\
remote_decl% "{other_group}"
def BobPad : Nat := 0
def Foo.field (x : Foo) : Nat := x.n + 2
def Foo.use (x : Foo) (y : Other) : Nat := x.field + y.field
'''
    write(alice, "Fields.lean", a)
    write(bob, "Fields.lean", b)
    publish(alice, "Fields.lean", no_pull=True)
    publish(bob, "Fields.lean", no_pull=True)
    ws("sync", alice)
    ws("sync", bob)
    fields = marker(bob, "Foo.field")
    trust = json.loads(Path(manifest["trust"]).read_text())["agents"]
    by_key = {key: agent for agent, key in trust}
    winner, loser = sorted(fields, key=lambda r: (r["lamport"], r["author"]))
    losing_agent = by_key[loser["author"]]
    if losing_agent != "bob":
        raise RuntimeError("OPEN17 fixture expected Bob's higher Lamport field to lose")
    losing_copy = copies[losing_agent]
    renamed = f'Foo.«field✝pl{loser["group"][:8]}»'
    document = losing_copy / "work/Fields.lean"
    dependent = marker(bob, "Foo.use")
    if len(dependent) != 1:
        raise RuntimeError("OPEN17 dependent field-use group was not published")
    projection_dir = document.parents[2] / "source-projection"
    projection_env = dict(os.environ, PARALEAN_STORE=str(losing_copy / "cache"))
    run([os.environ["PARALEAN_BIN"], "ws-hash", "--write", projection_dir,
         "--source", "1", "Fields.lean"], env=projection_env)
    source_projection = (projection_dir / "Fields.lean").read_text()
    rewritten_use = f'x.«field✝pl{loser["group"][:8]}» + y.field'
    if rewritten_use not in source_projection:
        raise RuntimeError("OPEN17 source projection did not selectively rewrite Foo.field")
    with document.open("a") as fh:
        fh.write("\nexample : Foo.use ⟨0⟩ ⟨0⟩ = 2 := by decide\n")
    check = field(ws("check", losing_copy, "Fields.lean"), "check")
    manifest.update(workspace_root=str(losing_copy / "work"), document=str(document),
                    group=loser["group"], winner_group=winner["group"],
                    other_group=other_group, dependent_group=dependent[0]["group"],
                    renamed=renamed, expected_tokens=[renamed, "y.field"],
                    rewritten_use=rewritten_use, source_projection=str(projection_dir / "Fields.lean"),
                    source=document.read_text(), check=check,
                    loser_agent=losing_agent)
    if check.get("errors"):
        raise RuntimeError("OPEN17 projection did not elaborate: " + str(check["errors"]))


def revocation(copies, manifest):
    alice, bob = copies["alice"], copies["bob"]
    write(alice, "Revoked.lean", """\
def Revoked.value : Nat := 7
def Revoked.use : Nat := Revoked.value + 1
""")
    publish(alice, "Revoked.lean")
    ws("sync", bob)
    group = marker(bob, "Revoked.use")[-1]["group"]
    document = write(bob, "P4Revocation.lean", f'remote_decl% "{group}"\n#check Revoked.use\n')
    manifest.update(workspace_root=str(bob / "work"), document=str(document),
                    group=group, expected_diagnostics_before=[],
                    expected_diagnostics_after=["revoked"])


def collision(copies, manifest):
    alice, bob = copies["alice"], copies["bob"]
    write(alice, "Shared.lean", "theorem Shared.dup : 2 = 2 := rfl\n")
    write(bob, "Shared.lean", """\
def BobPad : Nat := 0
theorem Shared.dup : 3 = 3 := rfl
example : 3 = 3 := Shared.dup
""")
    publish(alice, "Shared.lean", no_pull=True)
    publish(bob, "Shared.lean", no_pull=True)
    ws("sync", alice)
    ws("sync", bob)
    contenders = marker(bob, "Shared.dup")
    winner, loser = sorted(contenders, key=lambda r: (r["lamport"], r["author"]))
    trust = json.loads(Path(manifest["trust"]).read_text())["agents"]
    by_key = {key: agent for agent, key in trust}
    if by_key[loser["author"]] != "bob":
        raise RuntimeError("collision fixture expected Bob to lose")
    renamed = f'Shared.«dup✝pl{loser["group"][:8]}»'
    document = bob / "work/Shared.lean"
    source = document.read_text()
    check = field(ws("check", bob, "Shared.lean"), "check")
    if renamed not in source or check.get("errors"):
        raise RuntimeError("collision loser draft did not rename and elaborate: " + str(check))
    manifest.update(copy=str(bob), workspace_root=str(bob / "work"), document=str(document),
                    group=loser["group"], winner_group=winner["group"],
                    renamed=renamed, expected_tokens=[renamed], source=source, check=check)


def revoke(path):
    manifest = json.loads(path.read_text())
    os.environ.update(PARALEAN_DEPLOYMENT=manifest["deployment"],
                      PARALEAN_KEYS=manifest["keys"], PARALEAN_TRUST=manifest["trust"])
    os.environ.update(manifest["p2_environment"])
    p = run([manifest["p3_bin"], "keys", "revoke-validator", "v0",
             "P4 live revocation test"])
    print(p.stdout)


if __name__ == "__main__":
    action = sys.argv[1]
    if action == "revoke":
        revoke(Path(sys.argv[2]).resolve())
    elif action in {"instances", "open17", "collision", "revocation"}:
        build(action, Path(sys.argv[2]).resolve())
    else:
        raise SystemExit(__doc__)
