"""Controller boundary for private editor capture and explicit publication.

The router owns buffers and serializes accepted edits with ``mutation_lock``.
This module never publishes from a document notification. A publication request
must name a frozen target, its owner and dispatch epoch explicitly.
"""

from __future__ import annotations

import asyncio
import errno
import hashlib
import json
import os
from pathlib import Path
import secrets
import stat
import subprocess
import sys
import urllib.parse


# P2 ``objects::MAX_FILE_PATH``.
MAX_FILE_PATH = 1024
# W2-09 decoder budget, also the router's LSP frame limit.
MAX_WORKER_FILE = 64 * 1024 * 1024
# W2 anti-entropy metadata limit; a registry marker is far smaller.
MAX_MARKER_JSON = 1024 * 1024


class BridgeError(ValueError):
    pass


def _hash(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def check_file_path(path: str) -> str:
    """The P2 ``objects::check_file_path`` / Lean ``Safety.checkRelPath`` rule."""
    if not isinstance(path, str) or not path:
        raise BridgeError("empty source file path")
    if len(path.encode("utf-8", "surrogatepass")) > MAX_FILE_PATH:
        raise BridgeError("source file path too long")
    if path.startswith("/"):
        raise BridgeError("absolute source file path")
    if any(c == "\\" or ord(c) < 0x20 or c == "\x7f" for c in path):
        raise BridgeError("backslash or control character in source file path")
    if not path.endswith(".lean"):
        raise BridgeError("source file path does not name a .lean file")
    parts = path.split("/")
    if any(part in ("", ".", "..") or (part.isascii() and part.lower() == ".git") for part in parts):
        raise BridgeError("empty, dot or .git component in source file path")
    if parts[-1] == ".lean":
        raise BridgeError("empty source file name")
    return path


def _open_beneath(root: Path, relative: str) -> tuple[int, str]:
    """Open the parent of ``root/relative`` without following a symlink below ``root``."""
    parts = relative.split("/")
    if any(part in ("", ".", "..") for part in parts):
        raise OSError(errno.EINVAL, "unsafe relative path", relative)
    fd = os.open(root, os.O_RDONLY | os.O_DIRECTORY)
    try:
        for part in parts[:-1]:
            next_fd = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
            os.close(fd)
            fd = next_fd
        return fd, parts[-1]
    except BaseException:
        os.close(fd)
        raise


def _read_beneath(root: Path, relative: str, limit: int) -> bytes:
    """Read a bounded regular file the worker controls (compare backend ``_read_source``).

    O_NONBLOCK keeps a planted FIFO from blocking the controller, and the bound
    keeps a sparse or /proc file from exhausting its memory.
    """
    directory_fd, name = _open_beneath(root, relative)
    try:
        fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_NOCTTY,
                     dir_fd=directory_fd)
    finally:
        os.close(directory_fd)
    with os.fdopen(fd, "rb") as handle:
        info = os.fstat(handle.fileno())
        if not stat.S_ISREG(info.st_mode) or info.st_size > limit:
            raise OSError(errno.EINVAL, "not a bounded regular file", relative)
        data = handle.read(limit + 1)
    if len(data) > limit:
        raise OSError(errno.EFBIG, "file exceeds its size limit", relative)
    return data


def _replace_beneath(root: Path, relative: str, data: bytes) -> None:
    """Replace one worker source by rename, so a planted symlink or hard link
    is replaced rather than written through."""
    directory_fd, name = _open_beneath(root, relative)
    try:
        try:
            old = os.stat(name, dir_fd=directory_fd, follow_symlinks=False)
            mode = stat.S_IMODE(old.st_mode) if stat.S_ISREG(old.st_mode) else 0o600
        except FileNotFoundError:
            mode = 0o600
        temporary = f".{name}.{secrets.token_hex(8)}.paralean.tmp"
        fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600,
                     dir_fd=directory_fd)
        try:
            with os.fdopen(fd, "wb") as handle:
                handle.write(data)
                os.fchmod(handle.fileno(), mode)
            os.replace(temporary, name, src_dir_fd=directory_fd, dst_dir_fd=directory_fd)
        except BaseException:
            try:
                os.unlink(temporary, dir_fd=directory_fd)
            except FileNotFoundError:
                pass
            raise
    finally:
        os.close(directory_fd)


def authoritative_policy_probe(ws) -> str:
    """Read the current store, including live receipt revocations, for a copy.

    Pull obtains the current certified registry. ``check-receipt`` goes to the
    store for every group the editor might load; a revocation therefore changes
    this identity even when no local trust or record file changes.
    """
    plr = ws.env_overrides.get("PARALEAN_PLR") or os.environ.get("PARALEAN_PLR", "plr")
    bridge = os.environ.get("PARALEAN_P5_BRIDGE", str(Path(__file__).resolve().parents[1] /
        "p5" / "store-bridge" / "target" / "release" / "paralean-p5-store"))
    cache = Path(ws.env_overrides["PARALEAN_STORE"])
    env = {**os.environ, **ws.env_overrides}

    def command(binary: str, *args: str) -> dict:
        result = subprocess.run([binary, *args], env=env, cwd=ws.root,
                                text=True, capture_output=True, timeout=45)
        if result.returncode:
            raise BridgeError(f"authoritative policy query failed: {args[0]}")
        try:
            return json.loads(result.stdout.strip().splitlines()[-1])
        except (IndexError, json.JSONDecodeError) as exc:
            raise BridgeError("authoritative policy query returned malformed JSON") from exc

    live_policy = command(bridge, "policy-state")
    validators = live_policy.get("validators")
    if not isinstance(validators, list) or not validators or any(
            not isinstance(row.get("key"), str) or not isinstance(row.get("revoked"), bool)
            for row in validators if isinstance(row, dict)) or any(not isinstance(row, dict) for row in validators):
        raise BridgeError("store policy query returned malformed validators")
    agents = live_policy.get("agents")
    if not isinstance(agents, list) or any(
            not isinstance(row, dict) or not isinstance(row.get("workspace"), str)
            or not isinstance(row.get("registered"), bool) or not isinstance(row.get("revoked"), bool)
            for row in agents):
        raise BridgeError("store policy query returned malformed agent keys")
    # W3 agent-key registry. A revoked or unregistered author key leaves the
    # workspace readable but unable to publish; it is part of the hashed policy,
    # so the change also expires sessions and captures.
    own = [row for row in agents if row["workspace"] == ws.name]
    ws.authoring_refusal = (None if len(own) == 1 and own[0]["registered"] and not own[0]["revoked"]
        else "workspace agent key is revoked or unregistered")
    pulled = command(plr, "pull", "--cache", str(cache))
    if pulled.get("stale") or not isinstance(pulled.get("available"), int):
        raise BridgeError("store registry pull was stale or incomplete")
    groups = set()
    for path in (cache / "p3" / "records").glob("m-*.json"):
        # The worker controls its cache: a FIFO or huge file here must not hang
        # the probe while poll_policy holds mutation_lock for every workspace.
        try:
            marker = json.loads(_read_beneath(cache, "p3/records/" + path.name, MAX_MARKER_JSON))
        except (OSError, ValueError, RecursionError) as exc:
            raise BridgeError("local registry marker is unreadable or malformed") from exc
        group = marker.get("group") if isinstance(marker, dict) else None
        if not isinstance(group, str) or len(group) != 64:
            raise BridgeError("local registry marker is malformed")
        groups.add(group)
    receipts = []
    for group in sorted(groups):
        answer = command(plr, "check-receipt", group)
        if not isinstance(answer.get("admits"), bool):
            raise BridgeError("store receipt query returned malformed verdict")
        receipts.append((group, answer.get("admits"), answer.get("receipt"), answer.get("reason")))
    material = {"available": pulled["available"], "receipts": receipts,
                "live_policy": live_policy}
    return hashlib.sha256(json.dumps(material, sort_keys=True).encode()).hexdigest()


class ControllerBridge:
    # One capture reply line. asyncio's 64 KiB default rejects large legitimate
    # captures and leaves the rest of an over-limit line in the pipe.
    capture_reply_limit = MAX_WORKER_FILE

    def __init__(self, proxy, backend=None, *, capture_binary=None, policy_probe=None,
                 remote_sync=None):
        self.proxy = proxy
        self.backend = backend
        self.capture_binary = capture_binary or os.environ.get("PARALEAN_BIN", "paralean")
        # The probe must read current authoritative store state. No local file
        # digest is accepted as evidence of an unrevoked receipt.
        self.policy_probe = policy_probe
        self.remote_sync = remote_sync
        self.mutation_lock = proxy.mutation_lock
        self.captures: dict[tuple[str, str], dict] = {}
        self.workers: dict[tuple[str, str], asyncio.subprocess.Process] = {}
        self.worker_identities: dict[tuple[str, str], tuple[str, int]] = {}
        self.policy_ids: dict[str, str] = {}
        self.policy_ready: set[str] = set()
        # An event means the latest probe has reached a decision. It is also
        # set for an unavailable policy so router requests fail promptly.
        self.policy_events = {name: asyncio.Event() for name in proxy.workspaces}

    def _key(self, ws, uri: str) -> tuple[str, str]:
        return ws.name, uri

    def _source(self, ws, uri: str) -> tuple[str, dict]:
        state = ws.open_documents.get(uri)
        if state is None:
            raise BridgeError("document is not open")
        parsed = urllib.parse.urlparse(uri)
        if parsed.scheme != "file":
            raise BridgeError("document URI is not a canonical file URI")
        source = Path(urllib.parse.unquote(parsed.path)).resolve()
        work = ws.root / "work" if (ws.root / "work").is_dir() else ws.root
        work = work.resolve()
        if source == work or work not in source.parents or source.suffix != ".lean":
            raise BridgeError("document is outside the workspace Lean source root")
        return check_file_path(source.relative_to(work).as_posix()), state

    def _stamp(self, ws, uri: str) -> dict:
        file, state = self._source(ws, uri)
        return {"workspace": ws.name, "uri": uri, "file": file,
                "version": state["version"], "environment": ws.environment,
                "generation": ws.generation, "source_sha256": _hash(state["text"])}

    def observe(self, ws, uri: str, method: str) -> None:
        """Called only after the router accepts an open/change/close notification."""
        if method in ("textDocument/didOpen", "textDocument/didChange", "textDocument/didClose"):
            self.captures.pop(self._key(ws, uri), None)
            if method == "textDocument/didClose":
                worker = self.workers.pop(self._key(ws, uri), None)
                if worker and worker.returncode is None:
                    worker.kill()

    def _assert_current(self, ws, uri: str, expected: dict) -> None:
        if self._stamp(ws, uri) != expected:
            raise BridgeError("capture expired after a document or environment change")
        if ws.environment_digest() != ws.environment:
            raise BridgeError("workspace environment changed since capture")
        if self.policy_probe is not None and ws.name not in self.policy_ready:
            raise BridgeError("authoritative store policy is unavailable")

    def _assert_store_policy(self, ws) -> None:
        if self.policy_probe is not None:
            current = self._probe_policy(ws)
            if not current or current != self.policy_ids.get(ws.name):
                raise BridgeError("authoritative store policy changed since capture")
            if ws.environment_digest() != ws.environment:
                raise BridgeError("workspace environment changed since capture")

    def _assert_authoring(self, ws) -> None:
        refusal = getattr(ws, "authoring_refusal", None)
        if refusal:
            raise BridgeError(refusal)

    def _probe_policy(self, ws) -> str:
        if self.backend is not None:
            self.backend.refresh_public_trust(ws.name, ws.root)
        return self.policy_probe(ws)

    async def assert_policy_fresh(self, workspaces) -> None:
        """Recheck authoritative policy while the router holds mutation_lock."""
        if self.policy_probe is None:
            raise BridgeError("authoritative policy probe is not configured")
        for ws in workspaces:
            if ws.name not in self.policy_ready:
                raise BridgeError("authoritative store policy is unavailable")
            await asyncio.to_thread(self._assert_store_policy, ws)

    async def _stop_worker(self, key: tuple[str, str]) -> None:
        worker = self.workers.pop(key, None)
        self.worker_identities.pop(key, None)
        if worker and worker.returncode is None:
            worker.kill()
            await worker.wait()

    async def _capture_locked(self, ws, uri: str, version: int) -> dict:
        stamp = self._stamp(ws, uri)
        if stamp["version"] != version:
            raise BridgeError("capture requested for a stale document version")
        if self.policy_probe is not None and ws.name not in self.policy_ready:
            raise BridgeError("authoritative store policy is unavailable")
        if ws.environment_digest() != ws.environment:
            raise BridgeError("workspace environment changed before capture")
        key = self._key(ws, uri)
        identity = (stamp["environment"], stamp["generation"])
        if key in self.workers and self.worker_identities.get(key) != identity:
            await self._stop_worker(key)
        worker = self.workers.get(key)
        if worker is None or worker.returncode is not None:
            # The document's own published elements are in its text (ws.py's rule): a
            # buffer revising one redeclares its name.
            worker = await asyncio.create_subprocess_exec(
                self.capture_binary, "ws-capture-server", "--dir", str(ws.root),
                cwd=ws.root, env={**os.environ, **ws.env_overrides, "PARALEAN_VIS_EXCLUDE": stamp["file"]},
                stdin=asyncio.subprocess.PIPE, stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.DEVNULL, start_new_session=True,
                limit=self.capture_reply_limit)
            self.workers[key] = worker
            self.worker_identities[key] = identity
        request = {"file": stamp["file"], "text": ws.open_documents[uri]["text"],
                   "version": version, "environment": stamp["environment"],
                   "generation": stamp["generation"]}
        assert worker.stdin and worker.stdout
        worker.stdin.write((json.dumps(request, separators=(",", ":")) + "\n").encode())
        await worker.stdin.drain()
        try:
            line = await asyncio.wait_for(worker.stdout.readline(), 60)
        except asyncio.TimeoutError as exc:
            await self._stop_worker(key)
            raise BridgeError("capture worker timed out") from exc
        except ValueError as exc:
            # asyncio discards an over-limit partial line; the stream is unframed.
            await self._stop_worker(key)
            raise BridgeError("capture worker reply exceeds its size limit") from exc
        if not line:
            await self._stop_worker(key)
            raise BridgeError("capture worker exited")
        try:
            result = json.loads(line)
            if not isinstance(result, dict):
                raise ValueError("capture reply is not an object")
        except (ValueError, RecursionError) as exc:
            await self._stop_worker(key)
            raise BridgeError("capture worker returned malformed JSON") from exc
        self._assert_current(ws, uri, stamp)
        capture = self._checked_capture(result, stamp)
        record = {**stamp, "packages": capture["packages"],
                  "groups": capture.get("groups"),
                  "registry": result.get("registry"),
                  "reusedCommands": result.get("reusedCommands"),
                  "newCommands": result.get("newCommands")}
        self.captures[key] = record
        return record

    @staticmethod
    def _checked_capture(result: dict, stamp: dict) -> dict:
        """The capture in a worker reply for exactly this stamp, without rejections."""
        if result.get("error"):
            raise BridgeError(str(result["error"]))
        if any(result.get(k) != stamp[k] for k in ("file", "version", "environment", "generation")):
            raise BridgeError("capture worker returned a mismatched stamp")
        capture = result.get("capture")
        if (not isinstance(capture, dict) or not isinstance(capture.get("packages"), list)
                or any(not isinstance(package, dict) for package in capture["packages"])):
            raise BridgeError("capture worker returned malformed packages")
        if capture.get("rejected") or capture.get("rejectedPids"):
            reasons = capture.get("rejected") if isinstance(capture.get("rejected"), list) else []
            raise BridgeError("capture contains rejected declarations: " + "; ".join(map(str, reasons))[:300])
        return capture

    async def capture(self, ws, uri: str, version: int) -> dict:
        if self.policy_probe is not None:
            await self.poll_policy()
        async with self.mutation_lock:
            return await self._capture_locked(ws, uri, version)

    async def publish(self, ws, uri: str, version: int, target: str, owner: str,
                      epoch: int, *, policy: str | None = None) -> dict:
        """Publish one current captured target through receipt-checked P2/P3."""
        if policy != "frozen-target" or not target or not owner or not isinstance(epoch, int) or epoch < 0:
            raise BridgeError("explicit frozen-target publication policy, target, owner and epoch required")
        if self.backend is None:
            raise BridgeError("controller backend is not configured")
        if self.policy_probe is not None:
            await self.poll_policy()
        async with self.mutation_lock:
            stamp = self._stamp(ws, uri)
            if stamp["version"] != version:
                raise BridgeError("publication requested for a stale document version")
            saved = self.captures.get(self._key(ws, uri))
            if saved is None or any(saved.get(k) != v for k, v in stamp.items()):
                raise BridgeError("current buffer has no successful private capture")
            self._assert_current(ws, uri, stamp)
            self._assert_authoring(ws)
            spec = next((t for t in self.backend.task.get("targets", []) if t.get("name") == target), None)
            if (spec is None or spec.get("file") != stamp["file"] or owner != ws.name
                    or owner not in self.backend.agents):
                raise BridgeError("target, source file or owner is outside the frozen task")
            names = {".".join(map(str, name)) if isinstance(name, list) else str(name)
                     for package in saved["packages"] for name in package.get("names", [])}
            if target not in names:
                raise BridgeError("private capture does not contain the requested target")
            observation = await asyncio.to_thread(self.backend.observe_target, target, owner)
            if not observation.get("assigned_to_agent") or observation.get("epoch") != epoch:
                raise BridgeError("target owner or dispatch epoch changed")
            self._assert_current(ws, uri, stamp)
            # The worker controls work/: never write or read through its links.
            relative = "work/" + check_file_path(stamp["file"])
            _replace_beneath(ws.root, relative, ws.open_documents[uri]["text"].encode())

            def precommit_guard() -> None:
                self._assert_current(ws, uri, stamp)
                self._assert_store_policy(ws)
                self._assert_authoring(ws)
                try:
                    current = _read_beneath(ws.root, relative, MAX_WORKER_FILE)
                except OSError:
                    current = None
                if current is None or hashlib.sha256(current).hexdigest() != stamp["source_sha256"]:
                    raise BridgeError("working source changed after receipt validation")

            result = await asyncio.to_thread(
                self.backend.publish, owner, ws.root, stamp["file"], [target], epoch,
                precommit_guard=precommit_guard)
            # Backend.publish returns only after its receipt-checked P2 commit and
            # target verification. Its own pull may change the workspace digest;
            # a post-commit stale stamp must not be reported as a failed commit.
            checked = result.get("validated", {})
            if not checked.get("group"):
                raise BridgeError("backend returned no verified published target")
            stale_after_commit = self._stamp(ws, uri) != stamp or ws.environment_digest() != ws.environment
            self.captures.pop(self._key(ws, uri), None)
            return {"target": target, "group": checked["group"], "validated": checked,
                    "publication": result, "stamp": stamp, "committed": True,
                    "environment_changed_after_commit": stale_after_commit}

    def rename_inventory(self) -> dict:
        documents = []
        missing = []
        for ws in self.proxy.workspaces.values():
            work = ws.root / "work" if (ws.root / "work").is_dir() else ws.root
            open_by_path = {}
            for opened in ws.open_documents:
                parsed = urllib.parse.urlparse(opened)
                if parsed.scheme == "file":
                    open_by_path[Path(urllib.parse.unquote(parsed.path)).resolve()] = opened
            paths = {path.resolve() for path in work.rglob("*.lean")}
            paths |= {path for path in open_by_path if path.suffix == ".lean"}
            for path in sorted(paths):
                if work.resolve() not in path.resolve().parents:
                    missing.append({"workspace": ws.name, "uri": path.as_uri(), "reason": "source escapes work root"})
                    continue
                uri = open_by_path.get(path.resolve(), path.resolve().as_uri())
                if path.exists() and not path.is_file():
                    missing.append({"workspace": ws.name, "uri": uri, "reason": "source is not a regular file"})
                    continue
                try:
                    stamp = self._stamp(ws, uri)
                except BridgeError:
                    missing.append({"workspace": ws.name, "uri": uri, "reason": "not open"})
                    continue
                saved = self.captures.get(self._key(ws, uri))
                if saved is None or any(saved.get(k) != v for k, v in stamp.items()):
                    missing.append({"workspace": ws.name, "uri": uri, "reason": "capture missing or stale"})
                elif not isinstance(saved.get("groups"), list):
                    missing.append({"workspace": ws.name, "uri": uri,
                                    "reason": "complete group inventory unavailable"})
                else:
                    documents.append(saved.copy())
        return {"complete": not missing, "documents": documents, "missing": missing}

    async def _capture_planned(self, ws, uri: str, text: str, staging: str | None = None) -> dict:
        """Capture a planned, uncommitted buffer in a one-shot private worker.

        With ``staging``, P1 resolves the staged batch member shared under that ID
        (``PARALEAN_BATCH``), so a dependent can be captured against a renamed
        declaration that is not yet published. Nothing here is published or committed.
        """
        stamp = self._stamp(ws, uri)
        env = {**os.environ, **ws.env_overrides, "PARALEAN_VIS_EXCLUDE": stamp["file"]}
        if staging is not None:
            env["PARALEAN_BATCH"] = staging
        worker = await asyncio.create_subprocess_exec(
            self.capture_binary, "ws-capture-server", "--dir", str(ws.root),
            cwd=ws.root, env=env, stdin=asyncio.subprocess.PIPE, stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.DEVNULL, start_new_session=True, limit=self.capture_reply_limit)
        try:
            request = {"file": stamp["file"], "text": text, "version": stamp["version"],
                       "environment": stamp["environment"], "generation": stamp["generation"]}
            assert worker.stdin and worker.stdout
            worker.stdin.write((json.dumps(request, separators=(",", ":")) + "\n").encode())
            await worker.stdin.drain()
            try:
                line = await asyncio.wait_for(worker.stdout.readline(), 120)
                result = json.loads(line)
                if type(result) is not dict:
                    raise ValueError("capture reply is not an object")
            except asyncio.TimeoutError as exc:
                raise BridgeError("planned capture timed out") from exc
            except (ValueError, RecursionError) as exc:
                raise BridgeError("planned capture returned no well-formed reply") from exc
        finally:
            if worker.returncode is None:
                worker.kill()
            await worker.wait()
        capture = self._checked_capture(result, stamp)
        if not isinstance(capture.get("groups"), list) or any(
                not isinstance(g, dict) or not isinstance(g.get("pid"), str) or not isinstance(g.get("names"), list)
                for g in capture["groups"]):
            raise BridgeError("planned capture has no complete group inventory")
        return capture

    @staticmethod
    def _declarations(capture: dict) -> dict[int, dict]:
        """The declaration starting at each line of a captured buffer.

        P1 lists first the file's published groups that the text no longer contains, at
        their original lines, then the text's own declarations in order. Where two share
        a line, the later is the text's; the earlier must be such a published group. A
        rename edit stays within a line, so a line names a declaration before and after.
        """
        by_line: dict[int, dict] = {}
        for record in capture["groups"]:
            line = record.get("line")
            if type(line) is not int:
                raise BridgeError("captured declaration has no line")
            if line in by_line and by_line[line].get("alreadyPublished") is not True:
                raise BridgeError("two captured declarations start on one line")
            by_line[line] = record
        return by_line

    def _rename_members(self, before: dict, after: dict, agent: str, file: str) -> list[dict]:
        """Batch members for one document: each published declaration the rename
        changed is published again from the planned capture (a revision under a kept
        name), and a declaration whose names all changed also has its old position
        deleted. Unchanged declarations and private drafts contribute nothing."""
        old, new = self._declarations(before), self._declarations(after)
        if any(line not in old and record.get("alreadyPublished") is not True for line, record in new.items()):
            raise BridgeError("planned buffer declares a different set of declarations")
        packages = {package.get("group"): package for package in after["packages"]}
        members = []
        for line, previous in sorted(old.items()):
            current = new.get(line)
            if current is None:
                raise BridgeError("planned buffer declares a different set of declarations")
            if previous["pid"] == current["pid"] or previous.get("alreadyPublished") is not True:
                continue
            package = packages.get(current.get("group"))
            if package is None or current.get("alreadyPublished"):
                raise BridgeError("a changed published declaration has no new package")
            kept = set(map(str, previous["names"])) & set(map(str, current["names"]))
            if kept and kept != set(map(str, previous["names"])):
                raise BridgeError("a rename of one member of a published declaration group is not atomic here")
            names = [str(name) for name in current["names"]]
            members.append({"kind": "publish", "agent": agent, "file": file, "group": package["group"],
                            "capsule": package["capsule"], "deps": list(package.get("deps", [])),
                            "names": names, "replaces": [previous["group"]]})
            if not kept:
                members.append({"kind": "tombstone", "agent": agent, "target": previous["group"]})
        return members

    async def publish_rename(self, affected: dict, planned: dict, group: str) -> dict | None:
        """Publish what a planned rename changes in published declarations, atomically.

        The router calls this holding ``mutation_lock``, after every worker planned and
        every stamp, inventory and policy check passed, and before any buffer changes.
        Each affected buffer's planned text is captured privately: first the document
        declaring ``group``, then the others against its renamed declaration, staged
        but unpublished. The renamed declaration, the deletion of its old position and
        every revised dependent (with its target binding, owner and epoch) are then
        validated and published as one batch, or not at all. Returns None when no
        affected declaration is published: the rename then changes buffers only.
        """
        if not any(record.get("alreadyPublished") is True for doc in affected.values() for record in doc["groups"]):
            return None
        if self.backend is None:
            raise BridgeError("controller backend is not configured")
        if set(planned) != set(affected):
            raise BridgeError("planned rename does not cover every affected document")
        workspaces = {name: self.proxy.workspaces[name] for name, _ in affected}
        stamps = {}
        for (name, uri), doc in affected.items():
            ws = workspaces[name]
            stamp = self._stamp(ws, uri)
            if any(doc.get(k) != v for k, v in stamp.items()):
                raise BridgeError("an affected capture is stale")
            self._assert_current(ws, uri, stamp)
            self._assert_authoring(ws)
            stamps[(name, uri)] = stamp
        origin = next((key for key, doc in affected.items()
                       if any(record["group"] == group for record in doc["groups"])), None)
        if origin is None:
            raise BridgeError("no affected document declares the renamed group")
        captures = {origin: await self._capture_planned(workspaces[origin[0]], origin[1], planned[origin])}
        others = sorted(key for key in affected if key != origin)
        if others:
            line = next(record["line"] for record in affected[origin]["groups"] if record["group"] == group)
            renamed = self._declarations(captures[origin]).get(line, {})
            package = next((p for p in captures[origin]["packages"] if p.get("group") == renamed.get("group")), None)
            if package is None:
                raise BridgeError("the renamed declaration has no new package")
            users = sorted({name for name, _ in others})
            staging = await asyncio.to_thread(self.backend.stage_for_capture, origin[0], package, users)
            try:
                for name, uri in others:
                    captures[(name, uri)] = await self._capture_planned(
                        workspaces[name], uri, planned[(name, uri)], staging=staging)
            finally:
                await asyncio.to_thread(self.backend.unstage, staging, users)
        members = []
        for key in [origin] + others:
            members += self._rename_members(affected[key], captures[key], key[0], stamps[key]["file"])
        if not any(member["kind"] == "publish" for member in members):
            raise BridgeError("the rename changes no published declaration")
        # Frozen target names a revised member declares: the store rechecks owner,
        # epoch and head in the batch transaction; refuse early on what is visible now.
        frozen = {spec.get("name") for spec in self.backend.task.get("targets", [])}
        for member in members:
            proven = [name for name in member.get("names", []) if name in frozen]
            if len(proven) > 1:
                raise BridgeError("a batch member proves more than one target")
            if proven:
                observation = await asyncio.to_thread(self.backend.observe_target, proven[0], member["agent"])
                if observation.get("assigned_to_agent") is not True or not isinstance(observation.get("epoch"), int):
                    raise BridgeError(f"target {proven[0]} is not assigned to {member['agent']}")
                member["target"], member["epoch"] = proven[0], observation["epoch"]

        def precommit_guard() -> None:
            for (name, uri), stamp in stamps.items():
                self._assert_current(workspaces[name], uri, stamp)
            for each in workspaces.values():
                self._assert_store_policy(each)
                self._assert_authoring(each)

        floor = await asyncio.to_thread(self.backend.lamport_floor, sorted(workspaces))
        return await asyncio.to_thread(self.backend.publish_batch, members, lamport_floor=floor,
                                       precommit_guard=precommit_guard)

    async def poll_policy(self) -> bool:
        """Probe current store policy and push a new environment to Lean workers."""
        if self.policy_probe is None:
            return False
        changed = False
        async with self.mutation_lock:
            for ws in self.proxy.workspaces.values():
                # The probe pulls registry data into the local cache. Fence new
                # requests while it runs, including when no policy change is
                # ultimately observed.
                self.policy_ready.discard(ws.name)
                self.policy_events[ws.name].clear()
                try:
                    policy_id = await asyncio.to_thread(self._probe_policy, ws)
                    if not isinstance(policy_id, str) or not policy_id:
                        raise BridgeError("policy probe returned no authoritative identity")
                except Exception:
                    policy_id = "unavailable"
                previous = self.policy_ids.get(ws.name)
                if previous == policy_id and ws.environment_digest() == ws.environment:
                    if policy_id != "unavailable":
                        self.policy_ready.add(ws.name)
                    self.policy_events[ws.name].set()
                    continue
                # Stop the old generation and expire sessions before remote
                # provisioning. A replacement may only start after the owned
                # root has been completely synchronized.
                await ws.fence_policy()
                self.proxy.drop_sessions(ws)
                self.captures = {key: value for key, value in self.captures.items() if key[0] != ws.name}
                for key in [key for key in self.workers if key[0] == ws.name]:
                    await self._stop_worker(key)
                if policy_id != "unavailable" and self.remote_sync is not None:
                    try:
                        await asyncio.to_thread(self.remote_sync, ws)
                    except Exception:
                        policy_id = "unavailable"
                self.policy_ids[ws.name] = policy_id
                ws.environment_label = f"controller-policy:{policy_id}"
                ws.refresh_environment()
                if policy_id != "unavailable":
                    self.policy_ready.add(ws.name)
                    if self.proxy.initialize is not None:
                        try:
                            await ws.start()
                            await asyncio.wait_for(ws.ready.wait(), 30)
                        except Exception:
                            self.policy_ready.discard(ws.name)
                            self.policy_ids[ws.name] = "unavailable"
                            ws.environment_label = "controller-policy:unavailable"
                            ws.refresh_environment()
                            await ws.fence_policy()
                            self.proxy.drop_sessions(ws)
                if self.proxy.client_writer is not None:
                    await self.proxy.send({"jsonrpc": "2.0", "method": "paralean/environmentChanged",
                                           "params": {"workspace": ws.name,
                                                      "environment": ws.environment,
                                                      "generation": ws.generation,
                                                      "policyReady": ws.name in self.policy_ready}})
                self.policy_events[ws.name].set()
                changed = True
        return changed

    async def close(self) -> None:
        for key in list(self.workers):
            await self._stop_worker(key)
        if self.backend is not None and hasattr(self.backend, "close"):
            self.backend.close()


def attach_p5(proxy, task_path: Path, state_dir: Path, ssh_map: dict | None = None) -> ControllerBridge:
    """Attach an existing frozen P5 task to the router's provisioned workspaces."""
    p5 = Path(__file__).resolve().parents[1] / "p5"
    if str(p5) not in sys.path:
        sys.path.insert(0, str(p5))
    from p5lib.backend import Backend
    from p5lib.task import load

    task = load(Path(task_path))
    state_dir = Path(state_dir).resolve()
    agents = [f"w{i}" for i in range(task.workers)]
    if set(proxy.workspaces) != set(agents):
        raise BridgeError("P5 editor workspaces must exactly match frozen task agents")
    for name, ws in proxy.workspaces.items():
        if ws.root != (state_dir / name).resolve():
            raise BridgeError("P5 editor workspace root differs from provisioned task root")
    backend = Backend(task.as_dict() | {"agents": agents}, state_dir,
                      env={"PARALEAN_KEYS": str(state_dir / "keys.json"),
                           "PARALEAN_TRUST": str(state_dir / "trust.json")})
    backend.setup()
    for name in agents:
        backend.provision(name, state_dir / name)
        ws = proxy.workspaces[name]
        trust = ws.root / "trust.json"
        if not trust.is_file():
            raise BridgeError("P5 worker public trust ring was not provisioned")
        pinned = {"PARALEAN_STORE": str(ws.root / "cache"),
                  "PARALEAN_WORK_ROOT": str(ws.root / "work"),
                  "PARALEAN_KEYS": str(ws.root / "keys.json"),
                  "PARALEAN_TRUST": str(trust),
                  "PARALEAN_VISIBILITY": "1"}
        ws.base_env_overrides.update(pinned)
        ws.env_overrides.update(pinned)
        ws.refresh_environment()
        if any(ws.env_overrides.get(key) != value for key, value in pinned.items()):
            raise BridgeError("P5 workspace environment overrides a pinned worker path")
        ws.bound_env = pinned.copy()
    remote_sync = None
    if ssh_map:
        from p5lib.lsp_provision import SshEndpoint, provision_ssh_copy
        if set(ssh_map) != set(agents):
            raise BridgeError("SSH endpoint map must name every task workspace")
        endpoints = {name: SshEndpoint(
            row["host"], row["user"], int(row["port"]), Path(row["identity_file"]),
            Path(row["known_hosts"]), Path(row["root"]), dict(row.get("runtime_env", {})))
            for name, row in ssh_map.items()}
        for name, endpoint in endpoints.items():
            if proxy.workspaces[name].worker_root != endpoint.root:
                raise BridgeError("router worker root differs from pinned SSH endpoint")
        def remote_sync(ws):
            provision_ssh_copy(ws.root, endpoints[ws.name])
    bridge = ControllerBridge(proxy, backend=backend,
                              policy_probe=authoritative_policy_probe,
                              remote_sync=remote_sync)
    proxy.bridge = bridge
    return bridge


async def policy_feed(bridge: ControllerBridge, interval: float = 1.0) -> None:
    while not bridge.proxy.stopping:
        try:
            await bridge.poll_policy()
        except Exception as exc:
            # A failed remote restart cannot leave a previously ready policy
            # visible. Keep polling so a restored store/SSH endpoint recovers.
            bridge.proxy.debug("controller policy feed failed", exc)
            async with bridge.mutation_lock:
                for ws in bridge.proxy.workspaces.values():
                    bridge.policy_ready.discard(ws.name)
                    bridge.policy_events[ws.name].set()
                    bridge.policy_ids[ws.name] = "unavailable"
                    bridge.captures = {key: value for key, value in bridge.captures.items()
                                       if key[0] != ws.name}
                    ws.stop_process()
                    bridge.proxy.drop_sessions(ws)
                    if bridge.proxy.client_writer is not None:
                        await bridge.proxy.send({"jsonrpc": "2.0",
                            "method": "paralean/environmentChanged",
                            "params": {"workspace": ws.name, "environment": ws.environment,
                                       "generation": ws.generation, "policyReady": False}})
        await asyncio.sleep(interval)
