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

from .childenv import STORE_CREDENTIALS, filter_env
from .task import Target, Task

# Authentication a coding CLI may take from the environment instead of its own
# login files. Everything else credential-shaped is withheld from workers.
WORKER_CLI_CREDENTIALS = {
    "claude": ("ANTHROPIC_API_KEY", "ANTHROPIC_AUTH_TOKEN", "CLAUDE_CODE_OAUTH_TOKEN"),
    "codex": ("OPENAI_API_KEY", "CODEX_API_KEY"),
    "command": (),
}


def worker_env(kind: str, parent: dict | None = None) -> dict:
    """The parent environment without any credential the worker does not need."""
    source = os.environ if parent is None else parent
    # Operators may name extra variables their own worker command needs.
    extra = [name.strip() for name in source.get("PARALEAN_P5_WORKER_ENV_PASSTHROUGH", "").split(",")
             if name.strip() and not name.strip().upper().startswith("PARALEAN_")]
    return filter_env(source, allow=(*STORE_CREDENTIALS, *WORKER_CLI_CREDENTIALS.get(kind, ()), *extra))


def _open_log_dir(directory: Path) -> int:
    """Open directory/p5-logs, refusing a symlink anywhere below `directory`."""
    fd = os.open(directory, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        try:
            os.mkdir("p5-logs", 0o700, dir_fd=fd)
        except FileExistsError:
            pass
        return os.open("p5-logs", os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
    finally:
        os.close(fd)


def _replace_file(directory_fd: int, name: str) -> int:
    """Create `name` afresh: a planted symlink or hard link is unlinked, never followed."""
    try:
        os.unlink(name, dir_fd=directory_fd)
    except FileNotFoundError:
        pass
    return os.open(name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600,
                   dir_fd=directory_fd)


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
    tag = f"{target.name.replace('.', '_')}-{attempt}"
    if "/" in tag or tag.startswith("."):
        raise ValueError(f"unsafe target log name: {tag}")
    prompt_path = logdir / f"{tag}.prompt.txt"
    prompt_text = prompt(task, target, agent, directory, feedback)
    # The worker owns this folder; never follow a link it planted there.
    logdir_fd = _open_log_dir(directory)
    try:
        with os.fdopen(_replace_file(logdir_fd, prompt_path.name), "w") as handle:
            handle.write(prompt_text)
        log_fd = _replace_file(logdir_fd, f"{tag}.log")
    finally:
        os.close(logdir_fd)
    values = {"workspace": str(directory), "work": str(directory / "work"),
              "file": target.file, "target": target.name, "statement": target.statement,
              "prompt": str(prompt_path), "agent": agent, "attempt": str(attempt)}
    if task.worker_kind == "codex":
        cmd = ["codex", "exec", "--sandbox", "workspace-write", "--add-dir", str(directory),
               "--skip-git-repo-check", "-c", 'approval_policy="never"',
               "-c", "sandbox_workspace_write.network_access=true",
               "-C", str(directory / "work"), "-"]
        stdin = prompt_text
    elif task.worker_kind == "claude":
        cmd = ["claude", "-p", "--permission-mode", "auto", "--output-format", "json",
               prompt_text]
        stdin = None
    else:
        try:
            cmd = [part.format_map(values) for part in task.worker_command]
        except (KeyError, ValueError) as exc:
            os.close(log_fd)
            raise ValueError(f"invalid worker command template: {exc}") from exc
        stdin = None
    # The controller's full key file may hold authority and validator seeds, and
    # its environment may hold peer, Garage or recovery credentials. Every coding
    # agent receives only its own workspace signing seed and store access.
    env = worker_env(task.worker_kind)
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

    def stop_owned_group(proc: subprocess.Popen) -> None:
        # The guard and coding CLI have their own session. On a parent-side
        # exception, reap that session so neither process survives unnoticed.
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        guard_exited = False
        try:
            proc.wait(timeout=5)
            guard_exited = True
        except subprocess.TimeoutExpired:
            pass
        # The guard may exit after forwarding TERM. Its wait() can finish
        # while a CLI descendant still ignores TERM in the same group.
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        if not guard_exited:
            proc.wait()

    with os.fdopen(log_fd, "wb") as log:
        try:
            guard = Path(__file__).with_name("worker_guard.py")
            proc = subprocess.Popen([sys.executable, str(guard), *cmd], cwd=directory / "work", stdin=subprocess.PIPE if stdin else subprocess.DEVNULL,
                                    stdout=log, stderr=subprocess.STDOUT, env=env, start_new_session=True)
        except OSError as exc:
            log.write(f"worker launch failed: {exc}\n".encode())
            return WorkerResult(target.name, agent, attempt, 127, round(time.monotonic()-started, 3), False, str(log_path))
        try:
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
                        stop_owned_group(proc)
                        returncode = 124
                        break
        except BaseException:
            stop_owned_group(proc)
            raise
    return WorkerResult(target.name, agent, attempt, returncode, round(time.monotonic()-started, 3), timed_out, str(log_path))
