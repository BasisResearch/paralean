#!/usr/bin/env python3
"""Reproducible P5 scaling runs using real CLI workers and isolated deployments.

The caller starts its own PARALEAN_INSTANCE cluster and sources its environment.
Each trial gets a fresh task ID and deployment. Results distinguish actual agent
runs from any command-worker replay; the latter is never labelled an agent result.
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import re
import statistics
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
CLI = ROOT / "impl/p5/paralean.py"
TASK = ROOT / "impl/p5/tasks/add_comm_eight.toml"
COUNTS = (1, 2, 4, 8)


def task_copy(original: Path, destination: Path, task_id: str, workers: int) -> None:
    text = original.read_text()
    text, n_id = re.subn(r'(?m)^id = "[^"]+"$', f'id = "{task_id}"', text, count=1)
    text, n_workers = re.subn(r'(?m)^workers = \d+$', f'workers = {workers}', text, count=1)
    if n_id != 1 or n_workers != 1:
        raise ValueError("task must contain one task.id and controller.workers line")
    destination.write_text(text)


def git_rev(rev: str) -> str:
    return subprocess.check_output(["git", "rev-parse", rev], cwd=ROOT, text=True).strip()


def trial(args: argparse.Namespace, workers: int, rep: int, series: str) -> dict:
    name = f"{series}-w{workers}-r{rep}"
    directory = args.run_dir / name
    directory.mkdir(parents=True, exist_ok=False)
    task = directory / "task.toml"
    task_copy(args.task, task, name, workers)
    state = directory / "state"
    env = dict(os.environ)
    env["PARALEAN_DEPLOYMENT"] = name
    parallelism = min(workers, args.max_parallel)
    cmd = [sys.executable, str(args.controller), "run", str(task), "--state", str(state),
           "--workers", str(workers), "--parallelism", str(parallelism), "--worker", args.worker]
    start = time.monotonic()
    with (directory / "controller.log").open("w") as log:
        try:
            p = subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT, env=env, timeout=args.timeout)
            rc = p.returncode
        except subprocess.TimeoutExpired:
            rc = 124
    elapsed = round(time.monotonic() - start, 3)
    try:
        run = json.loads((state / "run.json").read_text())
    except (OSError, ValueError):
        run = {}
    targets = run.get("targets", {})
    metrics = run.get("metrics", {})
    export = run.get("export") or {}
    done = sum(v.get("status") == "done" for v in targets.values() if isinstance(v, dict))
    row = {"trial": name, "workers": workers, "parallelism": parallelism, "repeat": rep, "kind": args.worker,
           "provenance": "ordinary-agent-cli" if args.worker in ("codex", "claude") else "command-worker",
           "deployment": name, "returncode": rc, "ok": rc == 0 and run.get("phase") == "complete"
           and done == len(targets) and bool(targets) and bool(export.get("ok")),
           "targets_done": done, "targets_total": len(targets), "wall_s": elapsed,
           "controller_wall_s": metrics.get("wall_s"), "worker_wall_s": metrics.get("worker_wall_s"),
           "transfer_bytes": metrics.get("transfer_bytes"), "transfer_ms": metrics.get("transfer_ms"),
           "check_ms": metrics.get("check_ms"),
           "export_build_ms": export.get("buildMs"), "groups": export.get("groups"),
           "state": str(state), "log": str(directory / "controller.log")}
    (directory / "result.json").write_text(json.dumps(row, indent=2, sort_keys=True) + "\n")
    return row


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("run_dir", type=Path)
    ap.add_argument("--task", type=Path, default=TASK)
    ap.add_argument("--controller", type=Path, default=CLI)
    ap.add_argument("--worker", choices=("codex", "claude", "command"), default="codex")
    ap.add_argument("--repeats", type=int, default=1)
    ap.add_argument("--max-parallel", type=int, default=4,
                    help="simultaneous CLI workers; default protects the shared box")
    ap.add_argument("--timeout", type=int, default=1800)
    ap.add_argument("--series", default=None)
    args = ap.parse_args()
    if not os.environ.get("PARALEAN_INSTANCE"):
        ap.error("PARALEAN_INSTANCE must identify this run's private cluster")
    if args.repeats < 1 or args.max_parallel < 1:
        ap.error("--repeats and --max-parallel must be positive")
    args.run_dir = args.run_dir.resolve()
    args.task = args.task.resolve()
    args.run_dir.mkdir(parents=True, exist_ok=True)
    series = args.series or f"p5bench-{int(time.time())}-{os.getpid()}"
    rows = []
    for workers in COUNTS:
        for rep in range(1, args.repeats + 1):
            row = trial(args, workers, rep, series)
            rows.append(row)
            print(json.dumps(row), flush=True)
    fields = ["trial", "workers", "parallelism", "repeat", "kind", "provenance", "deployment", "returncode", "ok",
              "targets_done", "targets_total", "wall_s", "controller_wall_s", "worker_wall_s",
              "transfer_bytes", "transfer_ms", "check_ms", "export_build_ms", "groups", "state", "log"]
    with (args.run_dir / f"{series}.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)
    result = {"series": series, "worker": args.worker, "repeats": args.repeats,
              "git": git_rev("HEAD"), "origin_main": git_rev("origin/main"),
              "counts": list(COUNTS), "max_parallel": args.max_parallel,
              "summary": {str(n): {
                  "successful_trials": sum(r["ok"] for r in rows if r["workers"] == n),
                  "wall_s_median": statistics.median(r["wall_s"] for r in rows if r["workers"] == n),
                  "transfer_bytes_median": statistics.median(
                      r["transfer_bytes"] for r in rows if r["workers"] == n and
                      isinstance(r["transfer_bytes"], (int, float))) if any(
                      isinstance(r["transfer_bytes"], (int, float)) for r in rows if r["workers"] == n) else None,
                  "transfer_ms_median": statistics.median(
                      r["transfer_ms"] for r in rows if r["workers"] == n and
                      isinstance(r["transfer_ms"], (int, float))) if any(
                      isinstance(r["transfer_ms"], (int, float)) for r in rows if r["workers"] == n) else None,
                  "check_ms_median": statistics.median(
                      r["check_ms"] for r in rows if r["workers"] == n and
                      isinstance(r["check_ms"], (int, float))) if any(
                      isinstance(r["check_ms"], (int, float)) for r in rows if r["workers"] == n) else None,
              } for n in COUNTS}, "results": rows}
    (args.run_dir / f"{series}.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if all(x["ok"] for x in rows) else 1


if __name__ == "__main__":
    raise SystemExit(main())
