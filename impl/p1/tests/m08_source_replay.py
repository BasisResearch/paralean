#!/usr/bin/env python3
"""Exercise M08's exact source replay and reject changes to its macro body."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


P1 = Path(__file__).resolve().parents[1]
REPO = P1.parents[1]
SOURCE = "Mathlib/Tactic/ByCases.lean"


def run(cmd, *, cwd, env, code=0):
    result = subprocess.run(cmd, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode != code:
        raise AssertionError(f"exit {result.returncode}, expected {code}: {cmd}\n{result.stdout}")
    return result.stdout


def check_json(output):
    lines = [line.removeprefix("CHECK ") for line in output.splitlines()
             if line.startswith("CHECK ")]
    if len(lines) != 1:
        raise AssertionError(f"expected one CHECK result:\n{output}")
    return json.loads(lines[0])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bin", type=Path, required=True)
    parser.add_argument("--sysroot", type=Path, required=True)
    parser.add_argument("--mathlib", type=Path, required=True)
    parser.add_argument("--work", type=Path)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--expected-gid")
    parser.add_argument("--expected-decl")
    args = parser.parse_args()

    binary = args.bin.resolve()
    sysroot = args.sysroot.resolve()
    mathlib = args.mathlib.resolve()
    work = args.work.resolve() if args.work else None
    if work:
        work.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["PATH"] = f"{sysroot / 'bin'}:{env.get('PATH', '')}"
    env["LEAN_PARALEAN"] = "1"
    env["PARALEAN_SYSROOT"] = str(sysroot)
    env["PARALEAN_LIB"] = str(binary.parent.parent / "lib" / "lean")
    lean_path = subprocess.run([str(sysroot / "bin" / "lake"), "env", "printenv", "LEAN_PATH"],
                               cwd=mathlib, env=env, check=True, text=True,
                               stdout=subprocess.PIPE).stdout.strip()
    env["LEAN_PATH"] = lean_path

    with tempfile.TemporaryDirectory(prefix="m08-replay-", dir=work) as temporary:
        root = Path(temporary)
        fixture_store = root / "fixture"
        fixture_capture = run([str(binary), "capture", "--store", str(fixture_store),
                               "--ws", "fixture", "--root", str(P1 / "fixtures" / "m08"),
                               "MacroLiteral.lean"], cwd=REPO, env=env)
        fixture_replay = run([str(binary), "replay", "--store", str(fixture_store),
                              "--isolated", "1"], cwd=REPO, env=env)
        if "source replay: 2/2" not in fixture_replay or "isolated replay (exact deps only): 2/2" not in fixture_replay:
            raise AssertionError(f"fixture replay failed:\n{fixture_capture}\n{fixture_replay}")

        store = root / "m08"
        capture = run([str(binary), "capture", "--store", str(store), "--ws", "M08",
                       "--root", str(mathlib), SOURCE], cwd=mathlib, env=env)
        replay = run([str(binary), "replay", "--store", str(store), "--isolated", "1"],
                     cwd=mathlib, env=env)
        if "source replay: 3/3" not in replay or "isolated replay (exact deps only): 3/3" not in replay:
            raise AssertionError(f"M08 exact replay failed:\n{capture}\n{replay}")

        groups = [json.loads(p.read_text()) for p in (store / "meta").glob("*.json")]
        macro, = [g for g in groups if g["cmdKind"][-1] == "macro_rules"]
        if args.expected_gid and macro["gid"] != args.expected_gid:
            raise AssertionError(f"M08 gid changed: {macro['gid']}")
        if args.expected_decl and macro["declId"] != args.expected_decl:
            raise AssertionError(f"M08 declaration ID changed: {macro['declId']}")
        closure = [g["gid"] for g in groups if g["gid"] in set(macro["deps"] + macro["feDeps"])]
        closure.append(macro["gid"])
        check_args = ["--gids", ",".join(closure), "--decl", macro["declId"]]
        positive = check_json(run([str(binary), "check-group", "--store", str(store),
                                   *check_args], cwd=mathlib, env=env))
        if not positive["ok"] or positive["declId"] != macro["declId"]:
            raise AssertionError(f"M08 check-group rejected: {positive}")

        context_env = env.copy()
        context_env["LEAN_PATH"] = f"{env['PARALEAN_LIB']}:{lean_path}"
        context = run([str(sysroot / "bin" / "lean"), "--run",
                       str(P1 / "tests" / "M08ReplayContext.lean"), str(store)],
                      cwd=mathlib, env=context_env)
        if "old synthetic context rejected" not in context:
            raise AssertionError(f"old replay context did not fail:\n{context}")

        changed_store = root / "changed"
        shutil.copytree(store, changed_store)
        meta = changed_store / "meta" / f"{macro['gid']}.json"
        changed = json.loads(meta.read_text())
        old = "on_goal 2 => try_push_neg_at"
        if changed["capsule"]["text"].count(old) != 1:
            raise AssertionError("M08 macro body has changed; update the mutation")
        changed["capsule"]["text"] = changed["capsule"]["text"].replace(
            old, "on_goal 1 => try_push_neg_at")
        meta.write_text(json.dumps(changed, indent=2))
        negative = check_json(run([str(binary), "check-group", "--store", str(changed_store),
                                   *check_args], cwd=mathlib, env=env, code=1))
        if negative["ok"] or not any("capsule:replay-mismatch" in d for d in negative["diags"]):
            raise AssertionError(f"changed macro body escaped exact ID check: {negative}")

        report = {
            "gid": macro["gid"], "declId": macro["declId"],
            "fixture": fixture_replay.strip(), "capture": capture.strip(),
            "replay": replay.strip(), "check": positive,
            "context": context.strip(), "changedBody": negative,
        }
        if args.out:
            args.out.parent.mkdir(parents=True, exist_ok=True)
            args.out.write_text(json.dumps(report, indent=2) + "\n")
        print(f"M08 exact replay passed: {macro['gid']} / {macro['declId']}")
        print(context.strip())
        print("M08 changed-body check: rejected with replay-mismatch")


if __name__ == "__main__":
    main()
