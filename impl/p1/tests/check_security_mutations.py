#!/usr/bin/env python3
"""Compile receipt guard mutants in temporary oleans and require named Lean failures."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


P1 = Path(__file__).resolve().parents[1]
REPO = P1.parents[1]
OUT = REPO / "results" / "w2" / "p1-security-mutations.json"
LOGS = REPO / "results" / "w2" / "p1-security-mutation-logs"

CASES = [
    ("varint_canonical", "P3.lean",
     'if index > 0 && low == 0 then throw "receipt: nonminimal varint"',
     'if false then throw "receipt: nonminimal varint"',
     "nonminimal varint: accepted invalid input"),
    ("varint_overflow", "P3.lean",
     'if index == 9 && low > 1 then throw "receipt: varint overflow"',
     'if false then throw "receipt: varint overflow"',
     "varint overflow: accepted invalid input"),
    ("target_authority", "P3.lean",
     "let permitted := if job.hasTargets then #[t.authority] else keys",
     "let permitted := keys", "issuer target job: accepted invalid input"),
    ("target_exact_bytes", "P3.lean",
     'unless r.target == job.targetSlot do throw "the receipt\'s target binding differs from its job\'s"',
     'unless r.target.isNone == !job.hasTargets do throw "the receipt\'s target binding differs from its job\'s"',
     "mismatched target bytes: accepted invalid input"),
    ("cached_job_id", "P3.lean",
     'unless toHex job.id == toHex req do return .error "the cached job is not the one the receipt names"',
     "pure ()", "replaced cached job: accepted invalid input"),
    ("cached_receipt_signature", "P3.lean",
     'unless Ed25519.verify r.key r.id r.sig do throw "the receipt\'s signature does not verify"',
     "pure ()", "weak-key cached receipt: accepted invalid input"),
    ("ed25519_small_order", "Ed25519.lean",
     "if A.double.double.double.encode == 1 || R.double.double.double.encode == 1 then false else",
     "if false then false else", "weak-key signature accepted"),
    ("ed25519_scalar_range", "Ed25519.lean",
     "if s ≥ L then false else", "if false then false else",
     "vector S_malleated_plus_L: Lean Ed25519 result differs"),
    ("ed25519_canonical_y", "Ed25519.lean",
     "if y ≥ p then none else", "if false then none else",
     "vector noncanonical_A_y0_sign0: noncanonical point decoded"),
    ("ed25519_negative_zero", "Ed25519.lean",
     "if x == 0 && sign == 1 then none", "if false then none",
     "vector negative_zero_A: noncanonical point decoded"),
]


def run(args: list[str], env: dict[str, str], cwd: Path = P1) -> subprocess.CompletedProcess[str]:
    return subprocess.run(args, cwd=cwd, env=env, capture_output=True, text=True)


def main() -> int:
    LOGS.mkdir(parents=True, exist_ok=True)
    base = run([sys.executable, "tests/p3_security.py"], dict(os.environ))
    (LOGS / "baseline.log").write_text(base.stdout + base.stderr)
    if base.returncode != 0 or "P3 security checks passed" not in base.stdout:
        raise RuntimeError("P1 baseline failed; see " + str(LOGS / "baseline.log"))
    lake_env = run(["lake", "env", "env"], dict(os.environ))
    if lake_env.returncode != 0:
        raise RuntimeError("cannot obtain Lean library path: " + lake_env.stderr)
    paths = [line.removeprefix("LEAN_PATH=") for line in lake_env.stdout.splitlines()
             if line.startswith("LEAN_PATH=")]
    if len(paths) != 1:
        raise RuntimeError("lake env did not provide one LEAN_PATH")
    base_lib = Path(paths[0].split(os.pathsep)[0])
    lean_bin = run(["elan", "which", "lean"], dict(os.environ))
    if lean_bin.returncode != 0:
        raise RuntimeError("cannot find pinned Lean executable: " + lean_bin.stderr)
    lean = lean_bin.stdout.strip()
    rows = []
    with tempfile.TemporaryDirectory(prefix="w2-p1-mutations-") as temp:
        root = Path(temp)
        for name, target, old, new, expected in CASES:
            case = root / name
            module = case / "Paralean"
            module.mkdir(parents=True)
            for dep in (base_lib / "Paralean").rglob("*"):
                if not dep.is_file():
                    continue
                relative = dep.relative_to(base_lib / "Paralean")
                if relative.name.startswith("P3.") or relative.name.startswith("Ed25519."):
                    continue
                link = module / relative
                link.parent.mkdir(parents=True, exist_ok=True)
                link.symlink_to(dep)
            p3 = module / "P3.lean"
            ed = module / "Ed25519.lean"
            shutil.copy2(P1 / "Paralean" / "P3.lean", p3)
            if target == "Ed25519.lean":
                shutil.copy2(P1 / "Paralean" / "Ed25519.lean", ed)
            else:
                for dep in (base_lib / "Paralean").glob("Ed25519.*"):
                    (module / dep.name).symlink_to(dep)
            source = module / target
            text = source.read_text()
            if text.count(old) != 1:
                raise RuntimeError(f"{name}: mutation anchor missing or ambiguous")
            source.write_text(text.replace(old, new, 1))
            env = {**os.environ, "LEAN_PATH": f"{case}:{paths[0]}",
                   "PARALEAN_P1_TEST_LEAN_PATH": f"{case}:{paths[0]}",
                   "PARALEAN_P1_TEST_LEAN": lean}
            compile_log = ""
            if target == "Ed25519.lean":
                build = run([lean, "-o", str(module / "Ed25519.olean"), str(ed)], env, case)
                compile_log += build.stdout + build.stderr
                if build.returncode != 0:
                    raise RuntimeError(f"{name}: mutated Ed25519 compilation failed:\n{compile_log}")
            build = run([lean, "-o", str(module / "P3.olean"), str(p3)], env, case)
            compile_log += build.stdout + build.stderr
            if build.returncode != 0:
                raise RuntimeError(f"{name}: mutated P3 compilation failed:\n{compile_log}")
            result = run([sys.executable, "tests/p3_security.py"], env)
            output = compile_log + result.stdout + result.stderr
            logfile = LOGS / f"{name}.log"
            logfile.write_text(output)
            passed = result.returncode != 0 and f"uncaught exception: {expected}" in output
            rows.append({"name": name, "assertion": expected, "exit_code": result.returncode,
                         "passed": passed, "log": str(logfile.relative_to(REPO))})
            print(f"{name}: {'PASS' if passed else 'FAIL'}")
    OUT.write_text(json.dumps({"baseline": "P3 security checks passed", "cases": rows,
                               "passed": all(row["passed"] for row in rows)}, indent=2) + "\n")
    print(OUT)
    return 0 if all(row["passed"] for row in rows) else 1


if __name__ == "__main__":
    raise SystemExit(main())
