"""Launch ordinary coding CLIs against one fixed, private Lean target."""

from __future__ import annotations

import json
import os
import shlex
import signal
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path

from .task import Target, Task


@dataclass
class WorkerResult:
    target: str
    agent: str
    attempt: int
    returncode: int
    wall_s: float
    timed_out: bool
    log: str

    def as_dict(self) -> dict:
        return vars(self).copy()


def prompt(task: Task, target: Target, agent: str, directory: Path, feedback: str = "") -> str:
    deps = ", ".join(target.deps) or "none"
    return (f"You are an ordinary Lean coding agent working on Paralean task {task.id}.\n"
            f"Your fixed target is {target.name}. Its exact declaration header is:\n"
            f"theorem {target.name} : {target.statement} := by\n"
            f"Edit only {target.file} relative to this working directory. Prove this target without sorry, new axioms, "
            "or changing its statement. Use completed teammates' helpers through "
            "remote% declarations already synchronized into this working copy. "
            f"Required predecessor targets: {deps}.\n"
            "Leave unrelated declarations and generated Paralean markers intact. "
            "Do not inspect or print credentials, key files, or environment secrets. "
            "Check with the installed Paralean Lean command: "
            f"$PARALEAN_BIN ws-check --dir {shlex.quote(str(directory))} {shlex.quote(target.file)}. "
            "The controller independently validates and publishes the result.\n"
            f"{target.instructions}\n"
            + (f"Previous attempt: {feedback}. Repair this before finishing.\n" if feedback else ""))


def run(task: Task, target: Target, agent: str, attempt: int, directory: Path,
        feedback: str = "", stop_event=None) -> WorkerResult:
    directory.mkdir(parents=True, exist_ok=True)
    logdir = directory / "p5-logs"
    logdir.mkdir(exist_ok=True)
    tag = f"{target.name.replace('.', '_')}-{attempt}"
    prompt_path = logdir / f"{tag}.prompt.txt"
    prompt_path.write_text(prompt(task, target, agent, directory, feedback))
    values = {"workspace": str(directory), "work": str(directory / "work"),
              "file": target.file, "target": target.name, "statement": target.statement,
              "prompt": str(prompt_path), "agent": agent, "attempt": str(attempt)}
    if task.worker_kind == "codex":
        cmd = ["codex", "exec", "--sandbox", "workspace-write", "--add-dir", str(directory),
               "--skip-git-repo-check", "-c", 'approval_policy="never"',
               "-c", "sandbox_workspace_write.network_access=true",
               "-C", str(directory / "work"), "-"]
        stdin = prompt_path.read_text()
    elif task.worker_kind == "claude":
        cmd = ["claude", "-p", "--permission-mode", "auto", "--output-format", "json",
               prompt_path.read_text()]
        stdin = None
    else:
        try:
            cmd = [part.format_map(values) for part in task.worker_command]
        except (KeyError, ValueError) as exc:
            raise ValueError(f"invalid worker command template: {exc}") from exc
        stdin = None
    env = os.environ.copy()
    # The controller's full key file may hold authority and validator seeds. Every
    # coding agent receives only its own workspace signing seed.
    for secret in ("PARALEAN_KEYS", "PARALEAN_P5_RECOVERY_SECRET",
                   "PARALEAN_GARAGE_ADMIN_TOKEN", "PARALEAN_GARAGE_RPC_SECRET"):
        env.pop(secret, None)
    env["PARALEAN_KEYS"] = str(directory / "keys.json")
    env["PARALEAN_TRUST"] = str(directory.parent / "trust.json")
    env["PARALEAN_STORE"] = str(directory / "cache")
    env["PARALEAN_AGENT"] = agent
    env["PARALEAN_VISIBILITY"] = "1"
    env["PARALEAN_VIS_EXCLUDE"] = target.file
    env["PARALEAN_REMOTE_LOG"] = str(directory / "remote.log")
    env.update({"PARALEAN_P5_TASK": task.id, "PARALEAN_P5_AGENT": agent,
                "PARALEAN_P5_TARGET": target.name, "PARALEAN_P5_STATEMENT": target.statement,
                "PARALEAN_P5_FILE": target.file, "PARALEAN_P5_WORKSPACE": str(directory),
                "PARALEAN_P5_PROMPT": str(prompt_path),
                "PARALEAN_P5_DEPS": json.dumps(target.deps),
                "PARALEAN_P5_PARENT_PID": str(os.getpid())})
    log_path = logdir / f"{tag}.log"
    started = time.monotonic()
    timed_out = False
    with log_path.open("wb") as log:
        try:
            guard = Path(__file__).with_name("worker_guard.py")
            proc = subprocess.Popen([sys.executable, str(guard), *cmd], cwd=directory / "work", stdin=subprocess.PIPE if stdin else subprocess.DEVNULL,
                                    stdout=log, stderr=subprocess.STDOUT, env=env, start_new_session=True)
        except OSError as exc:
            log.write(f"worker launch failed: {exc}\n".encode())
            return WorkerResult(target.name, agent, attempt, 127, round(time.monotonic()-started, 3), False, str(log_path))
        if stdin is not None:
            proc.stdin.write(stdin.encode())
            proc.stdin.close()
        while True:
            try:
                returncode = proc.wait(timeout=0.5)
                break
            except subprocess.TimeoutExpired:
                if (stop_event is not None and stop_event.is_set()) or time.monotonic() - started >= task.timeout_s:
                    timed_out = True
                    os.killpg(proc.pid, signal.SIGTERM)
                    try:
                        proc.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        os.killpg(proc.pid, signal.SIGKILL)
                        proc.wait()
                    returncode = 124
                    break
    return WorkerResult(target.name, agent, attempt, returncode, round(time.monotonic()-started, 3), timed_out, str(log_path))
