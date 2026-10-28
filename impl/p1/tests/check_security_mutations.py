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
# PARALEAN_P1_MUTATION_OUT: another results directory (default: the W2 archive).
OUT_DIR = Path(os.environ.get("PARALEAN_P1_MUTATION_OUT", REPO / "results" / "w2"))
OUT = OUT_DIR / "p1-security-mutations.json"
LOGS = OUT_DIR / "p1-security-mutation-logs"

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
    # atomic batches (docs/atomic-pub-log.md)
    ("job_batch_tag", "P3.lean",
     "unless tag == 1 do throw", "unless true do throw",
     "job with trailing tag 2: accepted invalid input"),
    ("record_job_batch", "P3.lean",
     'unless job.batch == (staged <|> m.batch) do return .error "the record\'s batch differs from its job\'s"',
     "pure ()", "record with another batch: accepted invalid input"),
    ("batch_file_filter", "P3.lean",
     "unless ← filed dir m.batch m.id true do continue", "pure ()",
     "unfiled batch marker: accepted invalid input"),
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


# W2 Lean fixes (A-6, A-7, A-8, A-11, A-28), detected by tests/lean_security.py. Any
# Paralean module may be the target: it and every module of the test's import closure
# that depends on it are recompiled in the temporary tree; the rest are linked.
W2_CASES = [
    ("rel_path_dot_component", "Safety.lean",
     'if c == "." || c == ".." then throw "dot component in path"',
     'if false then throw "dot component in path"',
     'relative path "../x.lean": accepted invalid input'),
    ("marker_file_rule", "P3.lean",
     'receipt := ← jId j "receipt", file := ← jFile j "file", anchor',
     'receipt := ← jId j "receipt", file := ← jStr j "file", anchor',
     "marker file ../../.bashrc: accepted invalid input"),
    ("safe_join_symlink", "Safety.lean",
     "if md.type == .symlink then", "if false then",
     "join through a symlinked directory: accepted invalid input"),
    ("export_module_path", "Export.lean",
     "    match safeModulePath out m.name with\n"
     "    | .ok p => paths := paths.push p\n"
     '    | .error e => throw <| IO.userError s!"export: unsafe module name: {e}"',
     "    paths := paths.push (modulePath out m.name)",
     "export of module «..».«..».victim: accepted invalid input"),
    ("capsule_module_matches_file", "Safety.lean",
     "unless m == module do throw", "unless true do throw",
     "capsule module differs from its file: accepted invalid input"),
    ("meta_package_id", "Store.lean",
     "unless g.gid == gid && g.packageIdOf == gid do", "unless g.gid == gid do",
     "forged metadata under another package's ID: accepted invalid input"),
    ("meta_hex_id", "Store.lean",
     'unless Safety.isHexId gid do throw <| IO.userError s!"store: bad package ID {repr (gid.take 80).toString}"',
     "pure ()", "package ID ../escape: refused for another reason"),
    ("payload_varint_overflow", "Encode.lean",
     'if index == 9 && low > 1 then throw "decode: uvarint overflows u64"',
     'if false then throw "decode: uvarint overflows u64"', "varint overflow: accepted invalid input"),
    ("payload_varint_canonical", "Encode.lean",
     'if index > 0 && b == 0 then throw "decode: non-minimal uvarint"',
     'if false then throw "decode: non-minimal uvarint"', "nonminimal varint: accepted invalid input"),
    ("gate_command_allowlist", "Gate.lean",
     "else unless allowedCommands.contains k do", "else unless true do",
     "gate: #print: accepted invalid input"),
    ("gate_option_name", "Gate.lean",
     'unless safeOption o do return some s!"sets option',
     'unless true do return some s!"sets option',
     "gate: set_option «debug».skipKernelTC: accepted invalid input"),
    ("consumer_gate_call", "Remote.lean",
     "if let .error e ← Gate.checkCommand self cmd then",
     "if let .error e ← (pure (.ok ()) : IO (Except String Unit)) then",
     "eval consumer: the capsule's code ran"),
    ("validator_gate_call", "Validate.lean",
     """      let sr ← sourceReplay cat clo imports (materialize? := some (materialize store))
        (gate? := some Gate.checkCommand)""",
     "      let sr ← sourceReplay cat clo imports (materialize? := some (materialize store))",
     "eval validator: the capsule's code ran"),
    ("validator_initializer_refusal", "Validate.lean",
     "    if hasInitEffect (cat.get! gid) then", "    if false then",
     "init-touched validator: "),
]

W2_TEST_ROOTS = ["Paralean.Safety", "Paralean.Gate", "Paralean.P3", "Paralean.Store", "Paralean.Encode",
                 "Paralean.Export", "Paralean.Validate", "Paralean.Remote"]


def import_graph() -> dict[str, list[str]]:
    graph = {}
    for f in (P1 / "Paralean").glob("*.lean"):
        deps = []
        for line in f.read_text().splitlines():
            words = line.split()
            while words and words[0] in ("public", "meta"):
                words = words[1:]
            if len(words) >= 2 and words[0] == "import" and words[-1].startswith("Paralean."):
                deps.append(words[-1])
        graph["Paralean." + f.stem] = deps
    return graph


def closure(graph: dict[str, list[str]], roots: list[str]) -> list[str]:
    """Modules reachable from `roots`, dependencies first."""
    order, seen = [], set()
    def visit(m: str) -> None:
        if m in seen:
            return
        seen.add(m)
        for d in graph.get(m, []):
            visit(d)
        order.append(m)
    for r in roots:
        visit(r)
    return order


def run_w2_cases(root: Path, paths: list[str], base_lib: Path, lean: str, rows: list) -> None:
    graph = import_graph()
    needed = closure(graph, W2_TEST_ROOTS)
    for name, target, old, new, expected in W2_CASES:
        mutated = "Paralean." + target.removesuffix(".lean")
        affected = [m for m in needed if m == mutated or mutated in closure(graph, [m])]
        case = root / name
        module = case / "Paralean"
        module.mkdir(parents=True)
        stems = {m.removeprefix("Paralean.") for m in affected}
        for dep in (base_lib / "Paralean").rglob("*"):
            if not dep.is_file() or dep.name.split(".")[0] in stems:
                continue
            link = module / dep.relative_to(base_lib / "Paralean")
            link.parent.mkdir(parents=True, exist_ok=True)
            link.symlink_to(dep)
        env = {**os.environ, "LEAN_PATH": f"{case}:{paths[0]}",
               "PARALEAN_P1_TEST_LEAN_PATH": f"{case}:{paths[0]}", "PARALEAN_P1_TEST_LEAN": lean}
        compile_log = ""
        for m in affected:
            stem = m.removeprefix("Paralean.")
            src = module / f"{stem}.lean"
            text = (P1 / "Paralean" / f"{stem}.lean").read_text()
            if m == mutated:
                if text.count(old) != 1:
                    raise RuntimeError(f"{name}: mutation anchor missing or ambiguous")
                text = text.replace(old, new, 1)
            src.write_text(text)
            build = run([lean, "-o", str(module / f"{stem}.olean"), "-i", str(module / f"{stem}.ilean"), str(src)],
                        env, case)
            compile_log += f"== {stem}\n" + build.stdout + build.stderr
            if build.returncode != 0:
                raise RuntimeError(f"{name}: mutated {stem} compilation failed:\n{compile_log[-4000:]}")
        result = run([sys.executable, "tests/lean_security.py"], env)
        output = compile_log + result.stdout + result.stderr
        logfile = LOGS / f"{name}.log"
        logfile.write_text(output)
        passed = result.returncode != 0 and expected in output
        rows.append({"name": name, "assertion": expected, "exit_code": result.returncode,
                     "passed": passed, "log": str(logfile.relative_to(REPO)), "recompiled": affected})
        print(f"{name}: {'PASS' if passed else 'FAIL'}", flush=True)


def run(args: list[str], env: dict[str, str], cwd: Path = P1) -> subprocess.CompletedProcess[str]:
    return subprocess.run(args, cwd=cwd, env=env, capture_output=True, text=True)


def main() -> int:
    LOGS.mkdir(parents=True, exist_ok=True)
    base = run([sys.executable, "tests/p3_security.py"], dict(os.environ))
    (LOGS / "baseline.log").write_text(base.stdout + base.stderr)
    if base.returncode != 0 or "P3 security checks passed" not in base.stdout:
        raise RuntimeError("P1 baseline failed; see " + str(LOGS / "baseline.log"))
    w2 = run([sys.executable, "tests/lean_security.py"], dict(os.environ))
    (LOGS / "baseline-w2.log").write_text(w2.stdout + w2.stderr)
    if w2.returncode != 0 or "Lean W2 security checks passed" not in w2.stdout:
        raise RuntimeError("W2 Lean baseline failed; see " + str(LOGS / "baseline-w2.log"))
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
            print(f"{name}: {'PASS' if passed else 'FAIL'}", flush=True)
        if os.environ.get("PARALEAN_P1_MUTATIONS", "all") in ("all", "w2"):
            run_w2_cases(root, paths, base_lib, lean, rows)
    OUT.write_text(json.dumps({"baseline": "P3 security checks passed; Lean W2 security checks passed", "cases": rows,
                               "passed": all(row["passed"] for row in rows)}, indent=2) + "\n")
    print(OUT)
    return 0 if all(row["passed"] for row in rows) else 1


if __name__ == "__main__":
    raise SystemExit(main())
