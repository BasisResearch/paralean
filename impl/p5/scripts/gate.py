#!/usr/bin/env python3
"""P5 live gate: ordinary CLI workers, desktop loss, store recovery, stock export.

The caller starts its own PARALEAN_INSTANCE cluster and sources its environment.
This script neither starts nor stops storage services. It records gate.json in RUN_DIR.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import signal
import subprocess
import sys
import time
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
CLI = ROOT / "impl/p5/paralean.py"
TASK = ROOT / "impl/p5/tasks/add_comm_eight.toml"


def read_json(path: Path) -> dict:
    try:
        return json.loads(path.read_text())
    except (OSError, json.JSONDecodeError):
        return {}


def groups(state: dict) -> dict[str, str]:
    return {name: item["group"] for name, item in state.get("targets", {}).items()
            if isinstance(item, dict) and isinstance(item.get("group"), str) and item["group"]}


def run_cmd(cmd: list[str], log: Path, timeout: int, env: dict[str, str]) -> subprocess.CompletedProcess[str]:
    start = time.monotonic()
    p = subprocess.run(cmd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                       timeout=timeout, env=env)
    log.write_text(p.stdout)
    if p.returncode:
        raise RuntimeError(f"{cmd[2]} failed ({p.returncode}) after {time.monotonic()-start:.1f}s; see {log}")
    return p


def wait_for_partial(proc: subprocess.Popen, state_file: Path, target_count: int, timeout: int) -> dict:
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        state = read_json(state_file)
        n = len(groups(state))
        if 2 <= n < target_count:
            return state
        if proc.poll() is not None:
            raise RuntimeError(f"controller exited before a partial task could be interrupted (rc={proc.returncode})")
        time.sleep(0.25)
    raise TimeoutError("controller did not publish a partial task before timeout")


def kill_desktop(proc: subprocess.Popen) -> None:
    # CLI workers create their own process groups. Walk only this controller's
    # descendants before killing; the separate storage cluster remains untouched.
    listing = subprocess.check_output(["ps", "-eo", "pid=,ppid=,pgid="], text=True)
    children: dict[int, list[tuple[int, int]]] = {}
    for line in listing.splitlines():
        try:
            pid, ppid, pgid = map(int, line.split())
        except ValueError:
            continue
        children.setdefault(ppid, []).append((pid, pgid))
    groups = set()
    stack = [proc.pid]
    while stack:
        parent = stack.pop()
        for pid, pgid in children.get(parent, []):
            stack.append(pid)
            if pgid != proc.pid:
                groups.add(pgid)
    for pgid in groups:
        try:
            os.killpg(pgid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    os.killpg(proc.pid, signal.SIGKILL)
    try:
        proc.wait(timeout=15)
    except subprocess.TimeoutExpired:
        raise RuntimeError("desktop process group did not terminate")


def check_export(out: Path, result: dict) -> dict:
    lean_files = sorted(out.rglob("*.lean")) if out.exists() else []
    toolchain = out / "lean-toolchain"
    lakefile = out / "lakefile.toml"
    olean_files = sorted((out / ".lake/build/lib/lean").rglob("*.olean"))
    source = "\n".join(p.read_text(errors="replace") for p in lean_files)
    return {"ok": bool(result.get("ok")) and bool(lean_files) and toolchain.exists()
            and lakefile.exists() and bool(olean_files) and "sorry" not in source,
            "result": result, "lean_files": [str(p.relative_to(out)) for p in lean_files],
            "olean_count": len(olean_files), "toolchain": toolchain.read_text().strip() if toolchain.exists() else None}


def check_dependency_closure(state_dir: Path, targets: list[dict], published: dict[str, str]) -> dict:
    """Check every frozen DAG edge in trusted P1 package metadata, by package ID."""
    meta_by_group = {}
    for file in state_dir.glob("w*/cache/p3/capsules/*.json"):
        meta = read_json(file)
        if isinstance(meta.get("declId"), str) and isinstance(meta.get("gid"), str):
            meta_by_group[meta["declId"]] = meta
    edges = []
    for target in targets:
        name = target["name"]
        meta = meta_by_group.get(published.get(name, ""), {})
        actual = set(meta.get("deps", [])) | set(meta.get("feDeps", []))
        for dep in target.get("deps", []):
            predecessor = meta_by_group.get(published.get(dep, ""), {})
            gid = predecessor.get("gid")
            edges.append({"target": name, "depends_on": dep, "package": gid,
                          "present_in_checked_closure": bool(gid and gid in actual)})
    return {"ok": bool(edges) and all(edge["present_in_checked_closure"] for edge in edges),
            "edges": edges, "packages_found": len(meta_by_group)}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("run_dir", type=Path)
    ap.add_argument("--task", type=Path, default=TASK)
    ap.add_argument("--controller", type=Path, default=CLI)
    ap.add_argument("--worker", choices=("codex", "claude", "command"), default="codex")
    ap.add_argument("--timeout", type=int, default=1800)
    ap.add_argument("--parallelism", type=int, default=2,
                    help="maximum simultaneous CLI worker processes")
    ap.add_argument("--lsp-worker", action="store_true",
                    help="also run a scripted worker that edits and publishes through real LSP")
    ap.add_argument("--lsp-ssh-host")
    ap.add_argument("--lsp-ssh-user")
    ap.add_argument("--lsp-ssh-port", type=int, default=22)
    ap.add_argument("--lsp-ssh-identity", type=Path)
    ap.add_argument("--lsp-ssh-known-hosts", type=Path)
    ap.add_argument("--lsp-ssh-root", type=Path)
    ap.add_argument("--lsp-lean-server")
    ap.add_argument("--lsp-revoke-policy", action="store_true")
    ap.add_argument("--rename-check", action="store_true",
                    help="also rename published declarations across two workspaces atomically (rename_gate.py)")
    args = ap.parse_args()
    if not os.environ.get("PARALEAN_INSTANCE"):
        ap.error("PARALEAN_INSTANCE must identify this run's private cluster")
    run_dir = args.run_dir.resolve()
    # This fault test deletes the whole desktop. Refuse any preexisting path.
    run_dir.mkdir(parents=True, exist_ok=False)
    state_dir = run_dir
    export_dir = run_dir / "export"
    task = args.task.resolve()
    task_data = tomllib.loads(task.read_text())
    task_id = task_data["task"]["id"]
    targets = task_data["targets"]
    names = {x["name"] for x in targets}
    local_task = run_dir / "TASK.toml"
    shutil.copy2(task, local_task)
    evidence_dir = run_dir.with_name(run_dir.name + "-evidence")
    evidence_dir.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env["PARALEAN_DEPLOYMENT"] = env.get("PARALEAN_DEPLOYMENT") or f"p5gate-{int(time.time())}-{os.getpid()}"
    cmd = [sys.executable, str(args.controller)]
    result: dict = {"task": str(task), "worker": args.worker, "deployment": env["PARALEAN_DEPLOYMENT"],
                    "checks": {}, "versions": {}}
    try:
        result["versions"]["git"] = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        result["versions"]["origin_main"] = subprocess.check_output(["git", "rev-parse", "origin/main"], cwd=ROOT, text=True).strip()
        with (evidence_dir / "first-controller.log").open("w") as log:
            proc = subprocess.Popen(cmd + ["run", str(local_task), "--state", str(state_dir), "--worker", args.worker,
                                    "--parallelism", str(args.parallelism), "--no-export"],
                                    stdout=log, stderr=subprocess.STDOUT, env=env,
                                    start_new_session=True)
            try:
                partial = wait_for_partial(proc, state_dir / "run.json", len(names), args.timeout)
            finally:
                if proc.poll() is None:
                    kill_desktop(proc)
        prior = groups(partial)
        result["checks"]["partial_before_loss"] = {"ok": 2 <= len(prior) < len(names), "groups": prior}
        shutil.rmtree(state_dir)
        result["checks"]["desktop_state_removed"] = {"ok": not state_dir.exists() and not local_task.exists(),
                                                        "lost_task_file": str(local_task)}
        state_dir.mkdir(parents=True)
        discovered = run_cmd(cmd + ["list"], evidence_dir / "discovery.log", args.timeout, env)
        catalog = json.loads(discovered.stdout)
        tasks = catalog.get("tasks", [])
        found_ids = [item.get("task") for item in tasks if isinstance(item, dict)]
        discovered_id = found_ids[0] if len(found_ids) == 1 else None
        result["checks"]["store_task_discovery"] = {"ok": discovered_id == task_id,
                                                       "catalog": tasks, "discovered_id": discovered_id}
        if discovered_id != task_id:
            raise RuntimeError("store catalogue did not recover the unique lost task ID")
        run_cmd(cmd + ["recover", discovered_id, "--state", str(state_dir), "--worker", args.worker,
                       "--parallelism", str(args.parallelism), "--no-export"],
                evidence_dir / "recovery.log", args.timeout, env)
        recovered = read_json(state_dir / "run.json")
        found = groups(recovered)
        statuses = {n: recovered.get("targets", {}).get(n, {}).get("status") for n in names}
        contract = recovered.get("contract_validation") or {}
        target_checks = contract.get("targets") or {}
        pinned = all(target_checks.get(n, {}).get("ok") is True and
                     isinstance(target_checks.get(n, {}).get("statement_hash"), str) and
                     len(target_checks[n]["statement_hash"]) == 64 and
                     bool(target_checks[n].get("head")) for n in names)
        result["checks"]["all_contracts"] = {"ok": set(found) == names and
                                                all(s == "done" for s in statuses.values()) and
                                                contract.get("ok") is True and pinned,
                                                "groups": found, "statuses": statuses,
                                                "validation": contract}
        result["checks"]["store_recovery"] = {"ok": all(found.get(n) == g for n, g in prior.items()),
                                                "retained": prior, "recovered": found}
        result["checks"]["dependency_closure"] = check_dependency_closure(state_dir, targets, found)
        export = run_cmd(cmd + ["export", discovered_id, "--state", str(state_dir), "--out", str(export_dir)],
                         evidence_dir / "export.log", args.timeout, env)
        export_result = read_json(state_dir / "run.json").get("export") or {}
        if not export_result:
            try:
                export_result = json.loads(export.stdout.strip().splitlines()[-1])
            except (ValueError, IndexError):
                pass
        result["checks"]["stock_export"] = check_export(export_dir, export_result)
        remote = []
        for p in state_dir.rglob("*.lean"):
            if "remote%" in p.read_text(errors="replace"):
                remote.append(str(p.relative_to(state_dir)))
        result["checks"]["remote_helpers"] = {"ok": bool(remote), "files": remote}
        result["metrics"] = recovered.get("metrics", {})
        if args.lsp_worker:
            lsp_dir = run_dir.with_name(run_dir.name + "-lsp")
            lsp_cmd = [sys.executable, str(ROOT / "impl/p5/scripts/lsp_gate.py"), str(lsp_dir)]
            if args.lsp_lean_server:
                lsp_cmd += ["--lean-server", args.lsp_lean_server]
            if args.lsp_revoke_policy:
                lsp_cmd += ["--revoke-policy"]
            if args.lsp_ssh_host:
                lsp_cmd += ["--remote-dependent"]
                lsp_cmd += ["--ssh-host", args.lsp_ssh_host,
                            "--ssh-user", args.lsp_ssh_user or "",
                            "--ssh-port", str(args.lsp_ssh_port),
                            "--ssh-identity", str(args.lsp_ssh_identity or ""),
                            "--ssh-known-hosts", str(args.lsp_ssh_known_hosts or ""),
                            "--ssh-root", str(args.lsp_ssh_root or "")]
            run_cmd(lsp_cmd, evidence_dir / "lsp-worker.log", args.timeout, env)
            lsp_result = read_json(lsp_dir / "lsp-gate.json")
            result["checks"]["lsp_worker"] = {
                "ok": lsp_result.get("ok") is True,
                "provenance": "scripted JSON-RPC worker",
                "transport": lsp_result.get("transport"),
                "evidence": str(lsp_dir / "lsp-gate.json"),
                "details": lsp_result.get("checks")}
        if args.rename_check:
            rename_dir = run_dir.with_name(run_dir.name + "-rename")
            run_cmd([sys.executable, str(ROOT / "impl/p5/scripts/rename_gate.py"), str(rename_dir)],
                    evidence_dir / "published-rename.log", args.timeout, env)
            rename = read_json(rename_dir / "rename-gate.json")
            result["checks"]["published_rename"] = {
                "ok": rename.get("ok") is True, "evidence": str(rename_dir / "rename-gate.json"),
                "tests": {name: test.get("status") for name, test in rename.get("tests", {}).items()}}
    except Exception as exc:
        result["error"] = f"{type(exc).__name__}: {exc}"
    result["ok"] = "error" not in result and all(v["ok"] for v in result["checks"].values())
    (run_dir / "gate.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"ok": result["ok"], "checks": result["checks"], "error": result.get("error")}, indent=2))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
