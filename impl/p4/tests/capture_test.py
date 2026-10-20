#!/usr/bin/env python3
"""Exercise the persistent Lean capture worker with real elaboration.

Requires a built PARALEAN_BIN, PARALEAN_LIB and matching PARALEAN_SYSROOT. This
worker captures editor buffers; publishing remains a separate explicit action.
"""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time


def run(cmd, env):
    p = subprocess.run(cmd, text=True, capture_output=True, env=env)
    if p.returncode:
        raise AssertionError(f"{cmd} failed: {p.stdout[-1000:]} {p.stderr[-2000:]}")
    return json.loads(p.stdout.strip().splitlines()[-1]) if p.stdout.strip() else None


def request(server, file, text, version, environment="test-env", generation=1):
    payload = {"file": file, "text": text, "version": version,
               "environment": environment, "generation": generation}
    server.stdin.write(json.dumps(payload) + "\n")
    server.stdin.flush()
    line = server.stdout.readline()
    if not line:
        raise AssertionError(f"capture worker died with status {server.poll()}")
    return json.loads(line)


def names(result):
    return sorted(name for package in result["capture"]["packages"]
                  for name in package.get("names", []))


def percentile(values, pct):
    values = sorted(values)
    rank = (len(values) - 1) * pct / 100
    lo = int(rank)
    hi = min(lo + 1, len(values) - 1)
    return values[lo] + (values[hi] - values[lo]) * (rank - lo)


def main(args):
    binary = Path(os.environ.get("PARALEAN_BIN", "impl/p1/.lake/build/bin/paralean")).resolve()
    assert binary.is_file(), f"build {binary} first"
    env = dict(os.environ)
    prefix = "import Mathlib.Order.Basic\n" if args.label.lower() == "mathlib" else ""
    with tempfile.TemporaryDirectory(prefix="paralean-p4-capture-") as tmp:
        copy = Path(tmp) / "copy"
        if args.published_copy:
            source = args.published_copy.resolve()
            shutil.copytree(source, copy)
            env["PARALEAN_KEYS"] = str(copy / "keys.json")
            env.setdefault("PARALEAN_TRUST", str(source.parent / "trust.json"))
            if "PARALEAN_DEPLOYMENT" not in env:
                deployment_file = source.parent / "deployment"
                env["PARALEAN_DEPLOYMENT"] = (deployment_file.read_text().strip()
                    if deployment_file.is_file() else
                    json.loads((source.parent / "manifest.json").read_text())["deployment"])
            base = (copy / "work" / args.file).read_text().rstrip() + "\n\n"
            assert "remote%" in base, "published copy must contain a remote% source"
        else:
            run([binary, "ws-init", "--dir", copy, "--agent", "alice"], env)
            base = ""
        env["PARALEAN_STORE"] = str(copy / "cache")
        file = copy / "work" / args.file
        file.parent.mkdir(parents=True, exist_ok=True)
        text1 = prefix + base + "def P4.first : Nat := 1\ndef P4.second : Nat := P4.first + 1\n"
        text3 = prefix + base + "def P4.first : Nat := 1\n"
        records_before = {p.name for p in (copy / "cache/p3/records").glob("*.json")}
        server = subprocess.Popen([binary, "ws-capture-server", "--dir", copy],
                                  env=env, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=subprocess.DEVNULL, text=True, bufsize=1)
        try:
            start = time.monotonic()
            first = request(server, args.file, text1, 1)
            first_wall = round((time.monotonic() - start) * 1000, 2)
            assert "error" not in first and first["newCommands"] > 0, first
            edit_walls = []
            for version in range(2, args.samples + 2):
                text2 = text1.replace("P4.first + 1", f"P4.first + {version}")
                start = time.monotonic()
                edited = request(server, args.file, text2, version)
                edit_walls.append((time.monotonic() - start) * 1000)
                assert "error" not in edited and edited["reusedCommands"] > 0, edited
                assert edited["newCommands"] > 0, edited
            clean = Path(tmp) / "clean"
            if args.published_copy:
                shutil.copytree(args.published_copy.resolve(), clean)
            else:
                run([binary, "ws-init", "--dir", clean, "--agent", "alice"], env)
            clean_file = clean / "work" / args.file
            clean_file.parent.mkdir(parents=True, exist_ok=True)
            clean_file.write_text(text2)
            clean_env = dict(env, PARALEAN_STORE=str(clean / "cache"))
            if args.published_copy:
                clean_env["PARALEAN_KEYS"] = str(clean / "keys.json")
            fresh = run([binary, "ws-capture", "--dir", clean, args.file], clean_env)
            def package_ids(result):
                return sorted((p["pid"], p["group"], p["capsule"])
                              for p in result["packages"])
            assert package_ids(edited["capture"]) == package_ids(fresh), (edited, fresh)
            stale = request(server, args.file, text1, args.samples + 1)
            assert "stale document version" in stale.get("error", ""), stale
            wrong_env = request(server, args.file, text1, args.samples + 2, "different-env")
            assert "restart the worker" in wrong_env.get("error", ""), wrong_env
            wrong_gen = request(server, args.file, text1, args.samples + 2, generation=2)
            assert "restart the worker" in wrong_gen.get("error", ""), wrong_gen
            removed = request(server, args.file, text3, args.samples + 2)
            assert "error" not in removed, removed
            assert "P4.second" not in names(removed), names(removed)
            assert {p.name for p in (copy / "cache/p3/records").glob("*.json")} == records_before, "capture published a record"
        finally:
            server.stdin.close()
            server.wait(timeout=10)
        print(json.dumps({"gate": "pass", "benchmark": args.label,
                          "published_copy": bool(args.published_copy),
                          "first_ms": first_wall,
                          "edit_p50_ms": round(percentile(edit_walls, 50), 2),
                          "edit_p95_ms": round(percentile(edit_walls, 95), 2),
                          "edit_samples_ms": [round(x, 2) for x in edit_walls],
                          "first": {"new": first["newCommands"], "reused": first["reusedCommands"]},
                          "edit": {"new": edited["newCommands"], "reused": edited["reusedCommands"]}}, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--label", default="Init", choices=("Init", "Mathlib"))
    parser.add_argument("--samples", type=int, default=10)
    parser.add_argument("--published-copy", type=Path,
                        help="capture edits in a real published remote%% working copy")
    parser.add_argument("--file", default="A.lean")
    main(parser.parse_args())
