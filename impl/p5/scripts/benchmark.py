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
TASK = ROOT / "impl/p5/tasks/list_reverse_map_lengths.toml"
COUNTS = (1, 2, 4, 8)
METRIC_SCOPE = {
    "transfer_bytes, transfer_ms": "Controller-recorded sync and successful publish calls; excludes CLI worker demand fetches and failed publish attempts.",
    "check_ms": "Controller-recorded validator calls plus stock export buildMs and attestationBuildMs; failed publish attempts may be absent.",
    "validator_rpc_ms": "check_ms minus stock export buildMs and attestationBuildMs; controller-recorded validator calls only.",
    "working_copy_transfer_bytes, working_copy_transfer_ms": "Sum of all workspace cache/p3/transfer.jsonl rows except validate-target, including worker demand fetches and failed attempts; excludes validator downloads, P5 journal IO and protocol overhead; operation costs may overlap in wall time.",
    "wall_s": "External monotonic time for the complete run command, including export.",
}


def workspace_transfer(state: Path) -> dict:
    """Read every worker cache log, including demand fetches outside controller calls."""
    by_kind: dict[str, dict[str, int | float]] = {}
    files = sorted(state.rglob("cache/p3/transfer.jsonl"))
    invalid = 0
    for path in files:
        for line in path.read_text().splitlines():
            try:
                row = json.loads(line)
            except json.JSONDecodeError:
                invalid += 1
                continue
            if not isinstance(row, dict):
                invalid += 1
                continue
            kind, size, ms = row.get("kind"), row.get("bytes"), row.get("ms")
            if (not isinstance(kind, str) or not kind or isinstance(size, bool) or
                not isinstance(size, (int, float)) or size < 0 or isinstance(ms, bool) or
                not isinstance(ms, (int, float)) or ms < 0):
                invalid += 1
                continue
            item = by_kind.setdefault(kind, {"rows": 0, "bytes": 0, "ms": 0.0})
            item["rows"] += 1
            item["bytes"] += size
            item["ms"] += ms
    transfer = [value for kind, value in by_kind.items() if kind != "validate-target"]
    return {"bytes": sum(x["bytes"] for x in transfer),
            "ms": round(sum(x["ms"] for x in transfer), 6),
            "rows": sum(x["rows"] for x in transfer), "files": len(files),
            "invalid_rows": invalid, "by_kind": by_kind}


def median_numeric(rows: list[dict], workers: int, key: str) -> float | None:
    values = [row[key] for row in rows if row["workers"] == workers and
              isinstance(row.get(key), (int, float))]
    return statistics.median(values) if values else None


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
    transfer = workspace_transfer(state)
    check_ms, export_build_ms = metrics.get("check_ms"), export.get("buildMs")
    attestation_build_ms = export.get("attestationBuildMs", 0)
    validator_rpc_ms = (max(0, check_ms - export_build_ms - attestation_build_ms)
                        if isinstance(check_ms, (int, float)) and
                        isinstance(export_build_ms, (int, float)) and
                        isinstance(attestation_build_ms, (int, float)) else None)
    done = sum(v.get("status") == "done" for v in targets.values() if isinstance(v, dict))
    row = {"trial": name, "workers": workers, "parallelism": parallelism, "repeat": rep, "kind": args.worker,
           "provenance": "ordinary-agent-cli" if args.worker in ("codex", "claude") else "command-worker",
           "deployment": name, "returncode": rc, "ok": rc == 0 and transfer["invalid_rows"] == 0 and
           run.get("phase") == "complete"
           and done == len(targets) and bool(targets) and bool(export.get("ok")),
           "targets_done": done, "targets_total": len(targets), "wall_s": elapsed,
           "controller_wall_s": metrics.get("wall_s"), "worker_wall_s": metrics.get("worker_wall_s"),
           "transfer_bytes": metrics.get("transfer_bytes"), "transfer_ms": metrics.get("transfer_ms"),
           "check_ms": check_ms, "validator_rpc_ms": validator_rpc_ms,
           "working_copy_transfer_bytes": transfer["bytes"],
           "working_copy_transfer_ms": transfer["ms"],
           "working_copy_transfer_rows": transfer["rows"],
           "working_copy_transfer_files": transfer["files"],
           "working_copy_transfer_invalid_rows": transfer["invalid_rows"],
           "working_copy_transfer_by_kind": transfer["by_kind"],
           "export_build_ms": export_build_ms, "attestation_build_ms": attestation_build_ms,
           "groups": export.get("groups"),
           "state": str(state), "log": str(directory / "controller.log"),
           "metric_scope": METRIC_SCOPE}
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
              "transfer_bytes", "transfer_ms", "check_ms", "validator_rpc_ms",
              "working_copy_transfer_bytes", "working_copy_transfer_ms", "working_copy_transfer_rows",
              "working_copy_transfer_files", "working_copy_transfer_invalid_rows",
              "export_build_ms", "attestation_build_ms", "groups", "state", "log"]
    with (args.run_dir / f"{series}.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)
    result = {"series": series, "worker": args.worker, "repeats": args.repeats,
              "git": git_rev("HEAD"), "origin_main": git_rev("origin/main"),
              "counts": list(COUNTS), "max_parallel": args.max_parallel,
              "metric_scope": METRIC_SCOPE,
              "summary": {str(n): {
                  "successful_trials": sum(r["ok"] for r in rows if r["workers"] == n),
                  "wall_s_median": median_numeric(rows, n, "wall_s"),
                  "transfer_bytes_median": median_numeric(rows, n, "transfer_bytes"),
                  "transfer_ms_median": median_numeric(rows, n, "transfer_ms"),
                  "check_ms_median": median_numeric(rows, n, "check_ms"),
                  "validator_rpc_ms_median": median_numeric(rows, n, "validator_rpc_ms"),
                  "working_copy_transfer_bytes_median": median_numeric(rows, n, "working_copy_transfer_bytes"),
                  "working_copy_transfer_ms_median": median_numeric(rows, n, "working_copy_transfer_ms"),
              } for n in COUNTS}, "results": rows}
    (args.run_dir / f"{series}.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if all(x["ok"] for x in rows) else 1


if __name__ == "__main__":
    raise SystemExit(main())
