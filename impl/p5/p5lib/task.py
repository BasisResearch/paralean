"""Frozen, private task metadata. No task graph enters the declaration library."""

from __future__ import annotations

import hashlib
import json
import re
import tomllib
from dataclasses import dataclass, field
from pathlib import Path


_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")


@dataclass(frozen=True)
class Target:
    name: str
    statement: str
    file: str
    deps: tuple[str, ...] = ()
    owner: str | None = None
    instructions: str = ""

    def as_dict(self) -> dict:
        return {"name": self.name, "statement": self.statement, "file": self.file,
                "deps": list(self.deps), "owner": self.owner, "instructions": self.instructions}


@dataclass(frozen=True)
class Task:
    id: str
    name: str
    targets: tuple[Target, ...]
    workers: int = 2
    max_attempts: int = 3
    worker_kind: str = "codex"
    worker_command: tuple[str, ...] = ()
    timeout_s: int = 1800
    files: tuple[str, ...] = ()
    sources: dict[str, str] = field(default_factory=dict)
    source: Path | None = field(default=None, compare=False)

    def as_dict(self) -> dict:
        return {"id": self.id, "name": self.name,
                "targets": [x.as_dict() for x in self.targets], "workers": self.workers,
                "max_attempts": self.max_attempts, "worker_kind": self.worker_kind,
                "worker_command": list(self.worker_command), "timeout_s": self.timeout_s,
                "files": list(self.files), "sources": self.sources}

    @property
    def fingerprint(self) -> str:
        return hashlib.sha256(json.dumps(self.as_dict(), sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def _positive(v: object, label: str) -> int:
    if isinstance(v, bool) or not isinstance(v, int) or v < 1:
        raise ValueError(f"{label} must be a positive integer")
    return v


def _relative_file(v: object, label: str) -> str:
    if not isinstance(v, str) or not v or Path(v).is_absolute() or ".." in Path(v).parts or v.startswith("-"):
        raise ValueError(f"{label} must be a safe relative path")
    return v


def from_dict(raw: dict, source: Path | None = None) -> Task:
    t = raw.get("task", {})
    c = raw.get("controller", {})
    w = raw.get("worker", {})
    if not isinstance(t, dict) or not isinstance(c, dict) or not isinstance(w, dict):
        raise ValueError("task, controller and worker must be tables")
    task_id = t.get("id")
    if not isinstance(task_id, str) or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]{0,79}", task_id):
        raise ValueError("task.id must be a simple, nonempty identifier")
    raw_targets = raw.get("targets")
    if not isinstance(raw_targets, list) or not raw_targets:
        raise ValueError("at least one [[targets]] entry is required")
    targets = []
    for x in raw_targets:
        if not isinstance(x, dict):
            raise ValueError("each target must be a table")
        name, statement = x.get("name"), x.get("statement")
        if not isinstance(name, str) or not _NAME.fullmatch(name):
            raise ValueError(f"invalid target name: {name!r}")
        if not isinstance(statement, str) or not statement.strip():
            raise ValueError(f"{name}: a frozen statement is required")
        deps = x.get("deps", [])
        if not isinstance(deps, list) or any(not isinstance(d, str) for d in deps):
            raise ValueError(f"{name}: deps must be names")
        owner = x.get("owner")
        if owner is not None and (not isinstance(owner, str) or not re.fullmatch(r"[A-Za-z0-9_-]+", owner)):
            raise ValueError(f"{name}: invalid owner")
        targets.append(Target(name, statement, _relative_file(x.get("file"), f"{name}.file"),
                              tuple(deps), owner, str(x.get("instructions", ""))))
    names = {x.name for x in targets}
    if len(names) != len(targets):
        raise ValueError("target names must be unique")
    for x in targets:
        if x.name in x.deps or len(set(x.deps)) != len(x.deps) or not set(x.deps) <= names:
            raise ValueError(f"{x.name}: invalid or unknown dependency")
    visiting, done = set(), set()
    by_name = {x.name: x for x in targets}

    def visit(name: str) -> None:
        if name in visiting:
            raise ValueError(f"dependency cycle through {name}")
        if name not in done:
            visiting.add(name)
            for dep in by_name[name].deps:
                visit(dep)
            visiting.remove(name)
            done.add(name)

    for name in names:
        visit(name)
    command = w.get("command", [])
    if isinstance(command, str):
        raise ValueError("worker.command must be an array; shell commands are not accepted")
    if not isinstance(command, list) or any(not isinstance(z, str) or not z for z in command):
        raise ValueError("worker.command must be an array of nonempty strings")
    kind = w.get("kind", "codex")
    if kind not in ("codex", "claude", "command") or (kind == "command" and not command):
        raise ValueError("worker.kind must be codex, claude, or command with worker.command")
    files = t.get("files", sorted({x.file for x in targets}))
    if not isinstance(files, list):
        raise ValueError("task.files must be a list")
    sources = raw.get("sources", {})
    if not isinstance(sources, dict) or any(not isinstance(k, str) or not isinstance(v, str) for k, v in sources.items()):
        raise ValueError("sources must be a table mapping paths to Lean text")
    sources = {_relative_file(k, "sources path"): v for k, v in sources.items()}
    if not set(sources) <= set(files):
        raise ValueError("sources must name task.files entries")
    return Task(task_id, str(t.get("name", task_id)), tuple(targets),
                _positive(c.get("workers", 2), "controller.workers"),
                _positive(c.get("max_attempts", 3), "controller.max_attempts"), kind,
                tuple(command), _positive(w.get("timeout_s", 1800), "worker.timeout_s"),
                tuple(_relative_file(f, "task.files entry") for f in files), sources, source)


def load(path: Path) -> Task:
    path = path.resolve()
    with path.open("rb") as handle:
        return from_dict(tomllib.load(handle), path)


def from_saved(data: dict) -> Task:
    """Rebuild the immutable scheduler input from the task journal after desktop loss."""
    return Task(str(data["id"]), str(data.get("name", data["id"])),
                tuple(Target(str(t["name"]), str(t["statement"]), str(t["file"]),
                             tuple(t.get("deps", ())), t.get("owner"), str(t.get("instructions", "")))
                      for t in data["targets"]),
                int(data["workers"]), int(data["max_attempts"]),
                str(data["worker_kind"]), tuple(data.get("worker_command", ())),
                int(data["timeout_s"]), tuple(data.get("files", ())),
                dict(data.get("sources", {})))
