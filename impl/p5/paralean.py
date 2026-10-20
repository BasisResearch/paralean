#!/usr/bin/env python3
"""P5 autonomous controller: run, recover, inspect, or export a frozen Lean task."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import replace
from pathlib import Path

from p5lib.controller import Controller
from p5lib.task import from_saved, load


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="paralean", description=__doc__)
    subs = parser.add_subparsers(dest="command", required=True)
    for command in ("run", "recover", "status", "export"):
        p = subs.add_parser(command)
        p.add_argument("task", help="frozen TASK.toml or stored task ID for recovery")
        p.add_argument("--state", type=Path, help="local cache/output; recovery reads the store")
        p.add_argument("--workers", type=int, help="logical worker count used when the task was stored")
        p.add_argument("--worker", choices=("codex", "claude", "command"),
                       help="worker CLI used when the task was stored")
        if command in ("run", "recover"):
            p.add_argument("--parallelism", type=int, help="maximum simultaneous worker processes")
            p.add_argument("--no-export", action="store_true")
        if command == "export":
            p.add_argument("--out", type=Path, required=True)
    a = parser.parse_args(argv)
    try:
        task_path = Path(a.task)
        backend = None
        if task_path.is_file():
            task = load(task_path)
            if getattr(a, "worker", None):
                task = replace(task, worker_kind=a.worker)
                if task.worker_kind == "command" and not task.worker_command:
                    raise ValueError("--worker command requires [worker].command in the task")
            state = a.state or Path(".runs/p5") / task.id
            worker_count = a.workers
        elif a.command != "run":
            from p5lib.backend import Backend
            state = a.state or Path(".runs/p5") / a.task
            backend = Backend.recover_task(a.task, state)
            task = from_saved(backend.task)
            worker_count = len(backend.agents)
            if a.workers is not None and a.workers != worker_count:
                raise ValueError("--workers differs from the stored task")
            if a.worker is not None and a.worker != task.worker_kind:
                raise ValueError("--worker differs from the stored task")
        else:
            raise ValueError(f"task file does not exist: {a.task}")
        ctl = Controller(task, state, backend=backend, workers=worker_count,
                         parallelism=getattr(a, "parallelism", None))
        if a.command == "run":
            result = ctl.run(export=not a.no_export)
        elif a.command == "recover":
            result = ctl.run(recover=True, export=not a.no_export)
        elif a.command == "status":
            result = ctl.status()
        else:
            result = ctl.export(a.out)
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0 if result.get("phase") in ("complete", "targets_validated", "running") else 1
    except (OSError, ValueError, RuntimeError) as exc:
        print(f"paralean: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
