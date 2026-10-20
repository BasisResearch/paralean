#!/usr/bin/env python3
"""Capture the pinned M01--M18 sample serially for validator-throughput measurements.

Source m-targets-env.sh (PARALEAN_LEAN=fork) first and set PARALEAN_MATHLIB to
a private, prebuilt Mathlib checkout. Capture writes to the supplied output
directory; Lake may update configuration/cache metadata while resolving LEAN_PATH.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import time

repo = Path(__file__).resolve().parents[3]
out = Path(sys.argv[1]).resolve()
out.mkdir(parents=True, exist_ok=True)
mathlib = Path(os.environ["PARALEAN_MATHLIB"])
env = dict(os.environ)
env["LEAN_PATH"] = subprocess.check_output(
    ["lake", "env", "printenv", "LEAN_PATH"], cwd=mathlib, text=True).strip()
pin = json.loads((repo / "versions.json").read_text())["mathlib"]["commit"]
actual = subprocess.check_output(["git", "-C", str(mathlib), "rev-parse", "HEAD"], text=True).strip()
if actual != pin:
    raise SystemExit(f"Mathlib pin mismatch: {actual} != {pin}")
rows = []
for line in (repo / "corpus/modules.txt").read_text().splitlines():
    if not line.startswith("M"):
        continue
    key, module, *_ = line.split()
    directory = out / key
    directory.mkdir(exist_ok=True)
    start = time.monotonic()
    with (directory / "capture.log").open("w") as log:
        result = subprocess.run([
            os.environ["PARALEAN_BIN"], "capture", "--store", str(directory / "store"),
            "--ws", key, "--root", str(mathlib), module.replace(".", "/") + ".lean",
        ], env=env, stdout=log, stderr=subprocess.STDOUT)
    row = {"module": key, "source": module, "seconds": time.monotonic() - start,
           "exit_code": result.returncode,
           "groups": len(list((directory / "store/meta").glob("*.json")))}
    rows.append(row)
    (out / "capture.json").write_text(json.dumps(rows, indent=2) + "\n")
    print(json.dumps(row), flush=True)
    if result.returncode:
        raise SystemExit(f"capture failed; inspect {directory / 'capture.log'}")
