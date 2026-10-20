#!/usr/bin/env python3
"""P4 workspace tools: guided collision deletion and append-only Git projections.

Use the P3 environment plus PARALEAN_INSTANCE. Projection writes Git objects/refs
only: the working files, HEAD and the user's index are never checked out or staged.
"""
import argparse
import fcntl
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


TRAILER = "Co-Authored-By: GPT-6 Astra (Codex) <noreply@openai.com>"


def run(args, *, env=None, data=None):
    p = subprocess.run([str(a) for a in args], input=data, capture_output=True,
                       env=env, check=False)
    if p.returncode:
        raise RuntimeError(p.stderr.decode(errors="replace") or p.stdout.decode(errors="replace"))
    return p.stdout


def command_json(args, env):
    return json.loads(run(args, env=env).decode().strip().splitlines()[-1])


def environment(directory):
    env = dict(os.environ)
    env["PARALEAN_STORE"] = str(directory / "cache")
    if (directory / "keys.json").exists():
        env["PARALEAN_KEYS"] = str(directory / "keys.json")
    return env


def safe_path(value):
    p = Path(value)
    if p.is_absolute() or not p.parts or any(x in ("..", ".git") for x in p.parts):
        raise ValueError(f"unsafe projection path: {value}")
    return p


def name_components(value):
    """Parse printed Lean name components, including escaped collision names."""
    parts, current, quoted = [], "", False
    for char in value:
        if char == "«" and not quoted:
            quoted = True
        elif char == "»" and quoted:
            quoted = False
        elif char == "." and not quoted:
            if not current:
                raise ValueError("empty name component")
            parts.append(current)
            current = ""
        else:
            current += char
    if quoted or not current:
        raise ValueError("malformed Lean name")
    return parts + [current]


def records(cache):
    result = []
    for path in (cache / "p3/records").glob("*.json"):
        if path.name.startswith(("m-", "t-")):
            r = json.loads(path.read_text())
            safe_path(r["file"])
            r["_path"] = str(path)
            result.append(r)
    return sorted(result, key=lambda r: (r["lamport"], r["author"], r["id"]))


def render(cache, selected, env):
    """Render via Lean's canonical RGA, using an isolated view of known records."""
    with tempfile.TemporaryDirectory(prefix="paralean-projection-") as tmp:
        root = Path(tmp)
        view = root / "cache"
        (view / "p3/records").mkdir(parents=True)
        for entry in cache.iterdir():
            if entry.name != "p3":
                (view / entry.name).symlink_to(entry.resolve(), target_is_directory=entry.is_dir())
        for entry in (cache / "p3").iterdir():
            if entry.name not in ("records", "fetched"):
                (view / "p3" / entry.name).symlink_to(entry.resolve(), target_is_directory=entry.is_dir())
        for r in selected:
            src = Path(r["_path"])
            (view / "p3/records" / src.name).symlink_to(src.resolve())
        files = sorted({r["file"] for r in selected})
        if not files:
            return {}
        output = root / "rendered"
        e = dict(env, PARALEAN_STORE=str(view))
        run([e["PARALEAN_BIN"], "ws-hash", "--source", "1", "--write", output, *files], env=e)
        return {f: (output / safe_path(f)).read_bytes() for f in files}


class Projection:
    ref = "refs/heads/paralean/projection"

    def __init__(self, directory):
        self.directory = Path(directory).resolve()
        self.work = self.directory / "work"
        self.env = environment(self.directory)
        self.gitdir = Path(self.git("rev-parse", "--absolute-git-dir").decode().strip())
        trust = json.loads(Path(self.env["PARALEAN_TRUST"]).read_text())
        self.authors = {ident: name for name, ident in trust.get("agents", [])}

    def git(self, *args, data=None, env=None):
        return run(["git", "-C", self.work, *args], data=data, env=env)

    def head(self, ref):
        p = subprocess.run(["git", "-C", str(self.work), "rev-parse", "--verify", ref],
                           capture_output=True)
        return p.stdout.decode().strip() if p.returncode == 0 else None

    def state(self, head):
        if head is None:
            return []
        return json.loads(self.git("show", f"{head}:.paralean/projection.json"))["records"]

    def tree(self, files, ids):
        files = dict(files)
        files[".paralean/projection.json"] = (json.dumps({"records": sorted(ids)}, sort_keys=True) + "\n").encode()
        # Controller-provided build metadata is copied without including drafts.
        for name in ("lean-toolchain", "lakefile.toml"):
            p = self.work / name
            if p.exists():
                files[name] = p.read_bytes()
        with tempfile.TemporaryDirectory(prefix="paralean-index-") as tmp:
            env = dict(os.environ, GIT_INDEX_FILE=str(Path(tmp) / "index"))
            self.git("read-tree", "--empty", env=env)
            for name, content in sorted(files.items()):
                safe_path(name)
                blob = self.git("hash-object", "-w", "--stdin", data=content).decode().strip()
                self.git("update-index", "--add", "--cacheinfo", "100644", blob, name, env=env)
            return self.git("write-tree", env=env).decode().strip()

    def commit(self, tree, parents, message, author, lamport):
        env = dict(os.environ, GIT_AUTHOR_NAME=author,
                   GIT_AUTHOR_EMAIL=f"{author}@paralean.invalid",
                   GIT_COMMITTER_NAME="Paralean projection",
                   GIT_COMMITTER_EMAIL="projection@paralean.invalid",
                   GIT_AUTHOR_DATE=f"@{lamport} +0000",
                   GIT_COMMITTER_DATE=f"@{lamport} +0000")
        args = ["commit-tree", tree]
        for parent in dict.fromkeys(p for p in parents if p):
            args += ["-p", parent]
        return self.git(*args, data=(message + "\n\n" + TRAILER + "\n").encode(),
                        env=env).decode().strip()

    def project(self):
        head = self.head(self.ref)
        applied = self.state(head)
        all_records = records(self.directory / "cache")
        by_id = {r["id"]: r for r in all_records}
        if any(i not in by_id for i in applied):
            raise ValueError("cache lost previously projected records; pull before projecting")
        selected = [by_id[i] for i in applied]
        added = 0
        for r in all_records:
            if r["id"] in applied:
                continue
            selected.append(r)
            applied.append(r["id"])
            files = render(self.directory / "cache", selected, self.env)
            tree = self.tree(files, applied)
            if not re.fullmatch(r"[a-zA-Z0-9_-]+", r["author"]):
                raise ValueError("invalid author identifier")
            agent_ref = "refs/heads/paralean/agents/" + r["author"]
            agent_head = self.head(agent_ref)
            action = "delete" if "target" in r else "insert"
            msg = (f"{action} {r.get('group', r.get('target'))} in {r['file']}\n\n"
                   f"Paralean-Group: {r.get('group', r.get('target'))}\n"
                   f"Paralean-Lamport: {r['lamport']}\nParalean-Record: {r['id']}\n"
                   f"Paralean-Receipt: {r.get('receipt', '')}")
            event = self.commit(tree, [agent_head, head], msg,
                                self.authors.get(r["author"], r["author"]), r["lamport"])
            # Update both refs atomically; a crash cannot strand a visible event.
            transaction = (f"start\nupdate {agent_ref} {event} {agent_head or '0' * 40}\n"
                           f"update {self.ref} {event} {head or '0' * 40}\nprepare\ncommit\n")
            self.git("update-ref", "--stdin", data=transaction.encode())
            head = event
            added += 1
        return {"commit": head, "added": added, "records": len(applied), "branch": self.ref}

    def snapshot(self, workspace, catalog):
        """Recover a certified snapshot; its tag fixes that snapshot's rendered tree."""
        with tempfile.TemporaryDirectory(prefix="paralean-snapshot-") as tmp:
            cache = Path(tmp) / "cache"
            result = command_json([self.env["PARALEAN_PLR"], "snapshot-get", "--cache", cache,
                                   "--ws", workspace, "--catalog", catalog], self.env)
            sid = result["snapshot"]
            if not re.fullmatch("[0-9a-f]{64}", sid):
                raise ValueError("invalid snapshot ID")
            rs = records(cache)
            tree = self.tree(render(cache, rs, self.env), [r["id"] for r in rs])
            tag = "refs/tags/paralean/snapshot/" + sid
            old = self.head(tag)
            if old:
                if self.git("rev-parse", f"{old}^{{tree}}").decode().strip() != tree:
                    raise ValueError("immutable snapshot tag already names a different tree")
                return {"snapshot": sid, "tag": tag, "commit": old, "created": False}
            commit = self.commit(tree, [self.head(self.ref)],
                                 f"snapshot {sid}\n\nParalean-Catalog: {catalog}",
                                 "snapshot", max((r["lamport"] for r in rs), default=0))
            self.git("update-ref", tag, commit, "0" * 40)
            return {"snapshot": sid, "tag": tag, "commit": commit, "created": True}


def resolve(directory, file, name):
    """Choose the tombstone path in §11.5; backend enforces author authorization."""
    env = environment(directory)
    agent = (directory / "agent").read_text().strip()
    cache = directory / "cache"
    def pull():
        result = command_json([env["PARALEAN_PLR"], "pull", "--cache", cache], env)
        if result.get("stale"):
            raise RuntimeError("store returned a stale registry view; retry before resolving")
    pull()
    target = command_json([env["PARALEAN_BIN"], "ws-delete", "--dir", directory,
                           "--file", file, "--name-json", json.dumps(name_components(name))], env)
    deleted = command_json([env["PARALEAN_PLR"], "tombstone", "--cache", cache,
                            "--ws", agent, "--file", file, "--target", target["target"],
                            "--lamport", str(target["lamport"])], env)
    pull()
    synced = command_json([env["PARALEAN_BIN"], "ws-sync", "--dir", directory], env)
    heads = command_json([env["PARALEAN_BIN"], "ws-live"], env)
    live = set(heads["groups"])
    revisions = sorted({revision for record in records(cache)
                        if record.get("group") in live and record["file"] == file
                        for revision in record.get("revisions", [])})
    return {"resolution": "tombstone", "target": target["target"], **deleted,
            "sync": synced, "checkpointFiles": [file], "revisions": revisions,
            "checkpointArgs": ["checkpoint", "--cache", str(cache), "--ws", agent,
                               "--revisions", ",".join(revisions)],
            "next": "These candidate checkpointArgs select only this file's live heads. Revise affected drafts, check/export the selection, then submit through the controller's authority context. Recompute heads after any further publication; use ws-live to plan a broader snapshot."}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="command", required=True)
    for name in ("project", "snapshot", "resolve"):
        s = sub.add_parser(name)
        s.add_argument("directory", type=Path)
        if name == "snapshot":
            s.add_argument("--workspace", required=True)
            s.add_argument("--catalog", required=True)
        if name == "resolve":
            s.add_argument("file")
            s.add_argument("name", help="exact rendered losing name from the collision diagnostic")
    a = p.parse_args()
    directory = a.directory.resolve()
    # Serialize mutations of this workspace, including clocks and projection refs.
    with (directory / ".p4-tools.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if a.command == "resolve":
            result = resolve(directory, a.file, a.name)
        else:
            projection = Projection(directory)
            result = projection.project() if a.command == "project" else projection.snapshot(a.workspace, a.catalog)
    print(json.dumps(result))


if __name__ == "__main__":
    main()
