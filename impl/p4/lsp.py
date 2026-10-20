#!/usr/bin/env python3
"""A small, persistent Lean LSP multiplexer for Paralean workspaces.

Each workspace owns one long-lived Lean server. The proxy owns only routing and
editor buffers; Lean remains responsible for elaboration and proof state.
"""

import argparse
import asyncio
import copy
import hashlib
import json
import os
import pathlib
import signal
import sys
import urllib.parse


def frame(message):
    data = json.dumps(message, separators=(",", ":")).encode()
    return b"Content-Length: " + str(len(data)).encode() + b"\r\n\r\n" + data


async def read_message(reader):
    length = None
    while True:
        line = await reader.readline()
        if not line:
            raise EOFError
        if line in (b"\r\n", b"\n"):
            break
        name, _, value = line.partition(b":")
        if name.lower() == b"content-length":
            length = int(value.strip())
    if length is None or length > 64 * 1024 * 1024:
        raise ValueError("invalid LSP frame")
    return json.loads(await reader.readexactly(length))


def file_uri(path):
    return pathlib.Path(path).as_uri()


class Workspace:
    def __init__(self, proxy, name, root, environment, env_overrides, env_file=None,
                 worker_command=None, worker_root=None):
        self.proxy = proxy
        self.name = name
        self.root = pathlib.Path(root).resolve()
        self.worker_root = pathlib.Path(worker_root) if worker_root else self.root
        self.worker_command = worker_command or proxy.lean_command
        self.environment_label = environment
        self.base_env_overrides = env_overrides
        self.env_file = env_file
        self.env_overrides = self.load_env_overrides()
        self.environment = self.environment_digest()
        self.active_environment = self.environment
        self.public_mode = "file"
        self.generation = 0
        self.process = None
        self.reader_task = None
        self.start_lock = asyncio.Lock()
        self.write_lock = asyncio.Lock()
        self.change_lock = asyncio.Lock()
        self.ready = asyncio.Event()
        self.pending = {}
        self.next_id = 0
        self.open_documents = {}
        self.restart_task = None
        self.file_workers_seen = set()

    def load_env_overrides(self):
        overrides = self.base_env_overrides.copy()
        if self.env_file:
            config = json.loads(pathlib.Path(self.env_file).read_text())
            if not isinstance(config, dict) or any(not isinstance(k, str) or not isinstance(v, str) for k, v in config.items()):
                raise ValueError("workspace environment JSON must be a string-to-string object")
            overrides.update(config)
        return overrides

    def environment_digest(self):
        digest = hashlib.sha256()
        digest.update(self.environment_label.encode())
        if self.env_file:
            digest.update(pathlib.Path(self.env_file).read_bytes())
        for key in sorted(self.env_overrides):
            digest.update(key.encode() + b"=" + self.env_overrides[key].encode())
        store = pathlib.Path(self.env_overrides["PARALEAN_STORE"])
        inputs = [store / name for name in ("records", "revisions", "p3/records", "p3/revisions")]
        inputs += [pathlib.Path(self.env_overrides[name]) for name in
                   ("PARALEAN_TRUST", "PARALEAN_KEYS", "PARALEAN_REVOCATIONS") if self.env_overrides.get(name)]
        for root_path in inputs:
            digest.update(str(root_path).encode())
            if not root_path.exists():
                digest.update(b":missing")
                continue
            files = sorted(p for p in root_path.iterdir() if p.is_file() and not p.name.endswith(".tmp")) if root_path.is_dir() else [root_path]
            for path in files:
                try:
                    digest.update(str(path).encode())
                    digest.update(hashlib.sha256(path.read_bytes()).digest())
                except OSError:
                    digest.update(str(path).encode() + b":unreadable")
        return digest.hexdigest()

    def refresh_environment(self):
        try:
            self.env_overrides = self.load_env_overrides()
            current = self.environment_digest()
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            self.proxy.debug("invalid workspace environment", self.name, exc)
            self.environment = "invalid-configuration"
            self.stop_process()
            self.proxy.drop_sessions(self)
            raise ValueError(f"Invalid environment for workspace {self.name}") from exc
        if current != self.environment:
            self.environment = current
            return True
        return False

    def stop_process(self):
        if self.process and self.process.returncode is None:
            try:
                os.killpg(self.process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass

    async def replace_worker(self):
        """Fence old responses and complete a controlled restart before returning."""
        self.proxy.debug("replace begin", self.name, self.generation)
        async with self.start_lock:
            old = self.process
            self.generation += 1
            self.ready.clear()
            for item in self.pending.values():
                future = item[5]
                if not future.done():
                    future.set_result(None)
            self.pending.clear()
            self.proxy.drop_sessions(self)
            if old and old.returncode is None:
                self.stop_process()
                # asyncio subprocess wait may wait for an inherited pipe held by
                # a launcher child. The generation fence already makes its output
                # inert, so do not hold the replacement behind that pipe.
                asyncio.create_task(old.wait())
            self.proxy.debug("old stopped", self.name, old.returncode if old else None)
            self.process = None
        await self.start()
        self.proxy.debug("replacement initialized request sent", self.name, self.generation)
        await asyncio.wait_for(self.ready.wait(), 30)
        self.proxy.debug("replace ready", self.name, self.generation)

    async def start(self):
        async with self.start_lock:
            if self.process and self.process.returncode is None:
                return
            self.refresh_environment()
            self.ready.clear()
            self.generation += 1
            self.active_environment = self.environment
            self.file_workers_seen.clear()
            self.process = await asyncio.create_subprocess_exec(
                *self.worker_command, cwd=self.root,
                env=dict(os.environ, **self.env_overrides),
                stdin=asyncio.subprocess.PIPE, stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE if os.environ.get("PARALEAN_LSP_DEBUG") else asyncio.subprocess.DEVNULL,
                start_new_session=True,
            )
            if self.process.stderr is not None:
                asyncio.create_task(self.forward_stderr(self.process.stderr))
            generation = self.generation
            self.reader_task = asyncio.create_task(self.read_loop(generation, self.process))
            init = copy.deepcopy(self.proxy.initialize)
            init["id"] = -1
            init.setdefault("params", {})["rootUri"] = file_uri(self.worker_root)
            init["params"]["rootPath"] = str(self.worker_root)
            init["params"]["workspaceFolders"] = [{"uri": file_uri(self.worker_root), "name": self.name}]
            await self.write(init)

    async def forward_stderr(self, stderr):
        while line := await stderr.readline():
            self.proxy.debug(self.name, "lean stderr:", line.decode(errors="replace").rstrip())

    async def write(self, message):
        async with self.write_lock:
            if not self.process or self.process.returncode is not None:
                raise ConnectionError("Lean server unavailable")
            self.process.stdin.write(frame(message))
            await self.process.stdin.drain()

    async def request(self, message, client_id, document=None, aggregate=None, expected_version=None):
        async with self.change_lock:
            await self.start()
            await asyncio.wait_for(self.ready.wait(), 15)
            if client_id in self.proxy.cancelled:
                raise ValueError("request cancelled before worker dispatch")
            version = self.open_documents.get(document, {}).get("version") if document else None
            if document and version != expected_version:
                raise ValueError("document changed before request dispatch")
            self.next_id += 1
            worker_id = self.next_id
            future = asyncio.get_running_loop().create_future()
            self.pending[worker_id] = (client_id, document, version, self.generation, self.environment, future, aggregate, message.get("method"))
            wire = copy.deepcopy(message)
            wire["id"] = worker_id
            try:
                await self.write(wire)
            except (ConnectionError, BrokenPipeError):
                self.pending.pop(worker_id, None)
                if not future.done():
                    future.set_result(None)
            return worker_id, future

    async def notify(self, message):
        await self.start()
        await asyncio.wait_for(self.ready.wait(), 15)
        await self.write(message)

    async def read_loop(self, generation, process):
        try:
            while True:
                message = await read_message(process.stdout)
                if generation != self.generation or self.active_environment != self.environment:
                    return
                if message.get("id") == -1 and "method" not in message:
                    self.proxy.debug("worker initialize reply", self.name, generation)
                    await self.write({"jsonrpc": "2.0", "method": "initialized", "params": {}})
                    for uri, state in list(self.open_documents.items()):
                        await self.write({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {"uri": self.proxy.to_worker_uri(self, uri), "languageId": "lean4", "version": state["version"], "text": state["text"]}}})
                        state["sent_generation"] = generation
                        state["sent_version"] = state["version"]
                    self.ready.set()
                    continue
                if "id" in message and "method" not in message:
                    await self.proxy.worker_response(self, message)
                else:
                    await self.proxy.worker_message(self, message)
        except (EOFError, asyncio.IncompleteReadError, ConnectionError, BrokenPipeError):
            pass
        except (ValueError, json.JSONDecodeError):
            self.proxy.debug("malformed worker frame", self.name, generation)
            if process.returncode is None:
                self.stop_process()
        finally:
            if generation == self.generation:
                await process.wait()
                self.proxy.debug("worker exited", self.name, generation, process.returncode)
                self.ready.clear()
                for item in self.pending.values():
                    future = item[5]
                    if not future.done():
                        future.set_result(None)
                self.pending.clear()
                self.proxy.drop_sessions(self)
                if not self.proxy.stopping:
                    self.restart_task = asyncio.create_task(self.restart())

    async def restart(self):
        for delay in (0.1, 0.25, 0.5, 1, 2, 5):
            await asyncio.sleep(delay)
            try:
                await self.start()
                await asyncio.wait_for(self.ready.wait(), 15)
                return
            except (OSError, ValueError, ConnectionError, asyncio.TimeoutError):
                self.stop_process()


class Proxy:
    def __init__(self, workspaces, lean_command):
        self.lean_command = lean_command
        self.workspaces = workspaces
        self.initialize = None
        self.client_write_lock = asyncio.Lock()
        self.client_writer = None
        self.requests = {}
        self.sessions = {}
        self.next_session = 0
        self.cancelled = set()
        self.stopping = False
        self.environment_epoch = 0

    def debug(self, *items):
        if os.environ.get("PARALEAN_LSP_DEBUG"):
            print("paralean-lsp:", *items, file=sys.stderr, flush=True)

    async def send(self, message):
        async with self.client_write_lock:
            self.client_writer.write(frame(message))
            await self.client_writer.drain()

    def resolve(self, uri):
        parsed = urllib.parse.urlparse(uri)
        if parsed.scheme == "paralean":
            name = parsed.netloc
            ws = self.workspaces.get(name)
            if ws is None:
                return None, uri
            relative = pathlib.PurePosixPath(urllib.parse.unquote(parsed.path).lstrip("/"))
            if ".." in relative.parts:
                return None, uri
            path = (ws.root / relative).resolve()
            if path != ws.root and ws.root not in path.parents:
                return None, uri
            return ws, file_uri(path)
        if parsed.scheme != "file":
            return None, uri
        path = pathlib.Path(urllib.parse.unquote(parsed.path)).resolve()
        matches = [ws for ws in self.workspaces.values() if path == ws.root or ws.root in path.parents]
        if not matches:
            return None, uri
        return max(matches, key=lambda ws: len(ws.root.parts)), file_uri(path)

    def to_worker_uri(self, ws, uri):
        parsed = urllib.parse.urlparse(uri)
        if parsed.scheme != "file":
            return uri
        path = pathlib.Path(urllib.parse.unquote(parsed.path)).resolve()
        if path == ws.root or ws.root in path.parents:
            return file_uri(ws.worker_root / path.relative_to(ws.root))
        return uri

    def from_worker_uri(self, ws, uri):
        parsed = urllib.parse.urlparse(uri)
        if parsed.scheme != "file":
            return uri
        path = pathlib.Path(urllib.parse.unquote(parsed.path))
        if ws.worker_root == ws.root and path != ws.worker_root and ws.worker_root not in path.parents:
            path = path.resolve()
        if path == ws.worker_root or ws.worker_root in path.parents:
            return file_uri(ws.root / path.relative_to(ws.worker_root))
        return uri

    def map_worker_out(self, value, ws):
        if isinstance(value, list):
            return [self.map_worker_out(item, ws) for item in value]
        if isinstance(value, dict):
            result = {}
            for key, item in value.items():
                if key == "changes" and isinstance(item, dict):
                    result[key] = {self.from_worker_uri(ws, uri): self.map_worker_out(edits, ws) for uri, edits in item.items()}
                elif key in ("uri", "oldUri", "newUri", "targetUri") and isinstance(item, str):
                    result[key] = self.from_worker_uri(ws, item)
                else:
                    result[key] = self.map_worker_out(item, ws)
            return result
        return value

    def map_in(self, value, default=None):
        """Translate public virtual URIs before a worker sees a request."""
        if isinstance(value, list):
            return [self.map_in(v, default) for v in value]
        if isinstance(value, dict):
            result = {}
            for key, item in value.items():
                if key in ("uri", "oldUri", "newUri", "targetUri") and isinstance(item, str):
                    owner, actual = self.resolve(item)
                    result[key] = self.to_worker_uri(owner, actual) if owner else actual
                else:
                    result[key] = self.map_in(item, default)
            return result
        return value

    def map_out(self, value, ws):
        if isinstance(value, list):
            return [self.map_out(v, ws) for v in value]
        if isinstance(value, dict):
            result = {}
            for key, item in value.items():
                if key == "changes" and isinstance(item, dict):
                    result[key] = {self.public_uri(uri): self.map_out(edits, ws) for uri, edits in item.items()}
                    continue
                if key in ("uri", "oldUri", "newUri", "targetUri") and isinstance(item, str):
                    result[key] = self.public_uri(item)
                else:
                    result[key] = self.map_out(item, ws)
            return result
        return value

    def public_uri(self, uri):
        owner, actual = self.resolve(uri)
        if owner is None:
            return uri
        state = owner.open_documents.get(actual)
        if state:
            return state["public_uri"]
        if owner.public_mode == "paralean":
            path = pathlib.Path(urllib.parse.unquote(urllib.parse.urlparse(actual).path))
            return "paralean://" + owner.name + "/" + urllib.parse.quote(str(path.relative_to(owner.root)))
        return uri

    def stamp_completions(self, result, ws, document, version, generation, environment):
        owner = {"workspace": ws.name, "document": document, "version": version,
                 "generation": generation, "environment": environment}
        def stamp(item):
            if not isinstance(item, dict):
                return item
            item = copy.deepcopy(item)
            item["data"] = {"__paralean_completion": owner, "leanData": item.get("data")}
            return item
        if isinstance(result, list):
            return [stamp(item) for item in result]
        if isinstance(result, dict) and isinstance(result.get("items"), list):
            result = copy.deepcopy(result)
            result["items"] = [stamp(item) for item in result["items"]]
        return result

    def registry_symbols(self, ws, query):
        """Rebuild the public symbol cache from the copy's publication records."""
        store = pathlib.Path(ws.env_overrides["PARALEAN_STORE"])
        records = store / "p3/records"
        if not records.is_dir():
            return []
        def read_json(path):
            try:
                return json.loads(path.read_text())
            except (OSError, ValueError):
                return None
        entries = [read_json(path) for path in records.glob("*.json")]
        markers = [entry for entry in entries if isinstance(entry, dict) and entry.get("kind") == "marker"]
        tombs = [entry for entry in entries if isinstance(entry, dict) and entry.get("kind") == "tombstone"]
        revisions = {}
        revision_dir = store / "p3/revisions"
        if revision_dir.is_dir():
            for path in revision_dir.glob("*.json"):
                revision = read_json(path)
                if isinstance(revision, dict):
                    revisions[revision.get("id", path.stem)] = revision
        def ancestors(rid, seen=None):
            seen = set() if seen is None else seen
            if rid in seen or rid not in revisions:
                return set()
            seen.add(rid)
            found = set()
            for parent in revisions[rid].get("parents", []):
                previous = revisions.get(parent)
                if previous:
                    found.add(previous.get("group"))
                    found.update(ancestors(parent, seen))
            return found
        superseded = set()
        for marker in markers:
            for rid in marker.get("revisions", []):
                superseded.update(ancestors(rid))
        live = [marker for marker in markers if marker.get("group") not in superseded and
                not any(t.get("target") == marker.get("group") and t.get("author") == marker.get("author") and t.get("file") == marker.get("file") for t in tombs)]
        def name(value):
            return ".".join(str(component) for component in value) if isinstance(value, list) else str(value)
        entries = []
        for marker in live:
            pid = marker.get("pid")
            capsule = read_json(store / "meta" / f"{pid}.json") if pid else None
            if not isinstance(capsule, dict):
                capsule = read_json(store / "p3/capsules" / f"{marker.get('capsule')}.json")
            if not isinstance(capsule, dict):
                continue
            for original in capsule.get("publicNames", []):
                key = next(((row[1], row[2]) for row in marker.get("lineageKeys", []) if name(row[0]) == name(original)),
                           (marker.get("lamport", 0), marker.get("author", "")))
                entries.append((marker, capsule, original, key))
        winners = {}
        for marker, capsule, original, key in entries:
            spelling = name(original)
            rank = (key, (marker.get("lamport", 0), marker.get("author", "")))
            if spelling not in winners or rank < winners[spelling][0]:
                winners[spelling] = (rank, marker.get("group"))
        symbols = []
        for marker, capsule, original, key in entries:
            spelling = name(original)
            if winners[spelling][1] != marker.get("group"):
                parts = spelling.rsplit(".", 1)
                suffix = "✝pl" + marker.get("group", "")[:8]
                spelling = (parts[0] + "." if len(parts) == 2 else "") + parts[-1] + suffix
            if query.lower() not in spelling.lower():
                continue
            work_root = pathlib.Path(ws.env_overrides["PARALEAN_WORK_ROOT"]).resolve()
            source = (work_root / marker.get("file", capsule.get("capsule", {}).get("file", ""))).resolve()
            if source != work_root and work_root not in source.parents:
                continue
            source_uri = self.public_uri(file_uri(source))
            line = max(0, int(capsule.get("capsule", {}).get("startLine", 1)) - 1)
            symbols.append({"name": spelling, "kind": 12,
                            "location": {"uri": source_uri, "range": {"start": {"line": line, "character": 0},
                                                                          "end": {"line": line, "character": 0}}},
                            "containerName": ws.name})
        return symbols

    def document(self, params):
        doc = params.get("textDocument", {})
        uri = doc.get("uri", params.get("uri"))
        if uri is None and isinstance(params.get("location"), dict):
            uri = params["location"].get("uri")
        return self.resolve(uri) if uri else (None, None)

    def drop_sessions(self, ws):
        self.sessions = {k: v for k, v in self.sessions.items() if v[0] is not ws}

    async def worker_response(self, ws, message):
        if ws.refresh_environment():
            await ws.replace_worker()
            return
        message = self.map_worker_out(message, ws)
        item = ws.pending.pop(message["id"], None)
        if item is None:
            return
        client_id, document, version, generation, environment, future, aggregate, method = item
        fresh = generation == ws.generation and environment == ws.environment
        if document is not None:
            state = ws.open_documents.get(document)
            fresh &= state is not None and state["version"] == version
        if not fresh:
            self.debug("stale response", ws.name, message["id"], "method", method,
                       "doc", document, "wanted", version, generation, environment,
                       "actual", ws.open_documents.get(document) if document else None,
                       ws.generation, ws.environment)
            if not future.done():
                future.set_result(None)
            return
        output = self.map_out(message, ws)
        if method in ("textDocument/completion", "completionItem/resolve") and "result" in output:
            if method == "textDocument/completion":
                output["result"] = self.stamp_completions(output["result"], ws, document, version, generation, environment)
            elif isinstance(output["result"], dict):
                output["result"] = self.stamp_completions([output["result"]], ws, document, version, generation, environment)[0]
        if method == "$/lean/rpc/connect" and "result" in output:
            session = output["result"]
            if isinstance(session, dict):
                session = session.get("sessionId")
            if session is not None:
                self.next_session += 1
                self.sessions[str(self.next_session)] = (ws, generation, environment, document, session)
                output["result"]["sessionId"] = self.next_session
        if not future.done():
            future.set_result(output)

    async def worker_message(self, ws, message):
        if ws.refresh_environment():
            await ws.replace_worker()
            return
        message = self.map_worker_out(message, ws)
        method = message.get("method", "")
        if method == "$/paralean/fileWorkerStarted":
            uri = message.get("params", {}).get("uri")
            if uri in ws.file_workers_seen:
                # A native Lean file-worker restart (for example changed imports)
                # invalidates its opaque references even if the watchdog survived.
                # Recreate the owning watchdog so every old response is fenced by
                # the same generation rule used for a transport failure.
                await ws.replace_worker()
            elif uri:
                ws.file_workers_seen.add(uri)
            return
        if method == "$/lean/fileProgress":
            params = message.get("params", {})
            doc = params.get("textDocument", {})
            state = ws.open_documents.get(doc.get("uri"))
            if state is None or doc.get("version") != state["version"]:
                return
            if any(p.get("kind") == 2 for p in params.get("processing", [])):
                self.sessions = {key: value for key, value in self.sessions.items()
                                 if not (value[0] is ws and value[3] == doc.get("uri"))}
        if method == "textDocument/publishDiagnostics":
            params = message.get("params", {})
            uri = params.get("uri")
            state = ws.open_documents.get(uri)
            # Exact version is required. Lean normally includes it; unversioned
            # diagnostics cannot be tied to the current editor buffer.
            if state is None or params.get("version") != state["version"]:
                return
        if method == "$/lean/rpc/publish" and "params" in message:
            session = message["params"].get("sessionId")
            if session is not None:
                published_uri = message["params"].get("uri")
                candidates = [(public, record) for public, record in self.sessions.items()
                              if record[0] is ws and record[1:3] == (ws.generation, ws.environment)
                              and record[4] == session and (published_uri is None or record[3] == published_uri)]
                if len(candidates) != 1:
                    return
                message["params"]["sessionId"] = int(candidates[0][0])
        if "id" in message and method:
            # Server-initiated requests are not safely multiplexable without an ID
            # namespace. Answer common capability probes locally.
            await ws.write({"jsonrpc": "2.0", "id": message["id"], "result": None})
            return
        await self.send(self.map_out(message, ws))

    async def dispatch(self, message):
        method = message.get("method")
        params = message.get("params", {})
        client_id = message.get("id")
        if method == "initialize":
            self.initialize = message
            for ws in self.workspaces.values():
                asyncio.create_task(ws.start())
            await self.send({"jsonrpc": "2.0", "id": client_id, "result": {"capabilities": {"textDocumentSync": 2, "hoverProvider": True, "completionProvider": {"triggerCharacters": ["."], "resolveProvider": True}, "renameProvider": True, "definitionProvider": True, "referencesProvider": True, "documentSymbolProvider": True, "workspaceSymbolProvider": True, "executeCommandProvider": {"commands": ["paralean/killWorker", "paralean/setEnvironment"]}}, "serverInfo": {"name": "Paralean LSP"}}})
            return
        if method == "shutdown":
            await self.send({"jsonrpc": "2.0", "id": client_id, "result": None})
            return
        if method == "exit":
            self.stopping = True
            for ws in self.workspaces.values():
                ws.stop_process()
            return
        if method == "initialized":
            return
        if method == "workspace/executeCommand" and params.get("command") == "paralean/killWorker":
            name = (params.get("arguments") or [None])[0]
            ws = self.workspaces.get(name)
            if ws and ws.process and ws.process.returncode is None:
                ws.stop_process()
            await self.send({"jsonrpc": "2.0", "id": client_id, "result": ws is not None})
            return
        if method == "workspace/executeCommand" and params.get("command") == "paralean/setEnvironment":
            args = params.get("arguments") or []
            ws = self.workspaces.get(args[0]) if args else None
            if ws and len(args) > 1:
                ws.environment_label = str(args[1])
                ws.refresh_environment()
                await ws.replace_worker()
            await self.send({"jsonrpc": "2.0", "id": client_id, "result": ws is not None})
            return
        if method == "paralean/source":
            ws, uri = self.resolve(params.get("uri", ""))
            if ws is None:
                await self.error(client_id, -32602, "No workspace owns the source URI")
                return
            if ws.refresh_environment():
                await ws.replace_worker()
            state = ws.open_documents.get(uri)
            try:
                source = state["text"] if state else pathlib.Path(urllib.parse.unquote(urllib.parse.urlparse(uri).path)).read_text()
            except (OSError, UnicodeError):
                await self.error(client_id, -32602, "Source unavailable")
                return
            await self.send({"jsonrpc": "2.0", "id": client_id, "result": {"uri": params["uri"], "workspace": ws.name, "environment": ws.environment, "generation": ws.generation, "version": state["version"] if state else None, "text": source}})
            return
        if method == "$/cancelRequest":
            target = params.get("id")
            self.cancelled.add(target)
            for ws, worker_id in self.requests.pop(target, []):
                item = ws.pending.pop(worker_id, None)
                if item and not item[5].done():
                    item[5].set_result(None)
                try:
                    if ws.process and ws.process.returncode is None:
                        await ws.write({"jsonrpc": "2.0", "method": "$/cancelRequest", "params": {"id": worker_id}})
                except (ConnectionError, BrokenPipeError):
                    pass
            return
        if method in ("textDocument/didOpen", "textDocument/didChange", "textDocument/didClose", "textDocument/didSave"):
            ws, uri = self.document(params)
            if ws is None:
                return
            if ws.refresh_environment():
                await ws.replace_worker()
            wire = copy.deepcopy(message)
            wire["params"] = self.map_in(params, ws)
            doc = wire["params"]["textDocument"]
            if method == "textDocument/didOpen":
                ws.open_documents[uri] = {"version": doc["version"], "text": doc["text"], "public_uri": params["textDocument"]["uri"]}
                if params["textDocument"]["uri"].startswith("paralean:"):
                    ws.public_mode = "paralean"
            elif method == "textDocument/didChange":
                state = ws.open_documents.get(uri)
                if state is None or doc["version"] <= state["version"]:
                    return
                text = state["text"]
                for change in wire["params"]["contentChanges"]:
                    if "range" not in change:
                        text = change["text"]
                    else:
                        text = apply_change(text, change)
                state.update(version=doc["version"], text=text)
            elif method == "textDocument/didClose":
                closed = ws.open_documents.pop(uri, None)
                ws.file_workers_seen.discard(uri)
                if closed:
                    await self.send({"jsonrpc": "2.0", "method": "textDocument/publishDiagnostics", "params": {"uri": closed["public_uri"], "diagnostics": []}})
            asyncio.create_task(self.deliver_change(ws, wire, uri, method))
            return
        if method in ("workspace/symbol", "paralean/search"):
            if client_id is None:
                return
            asyncio.create_task(self.aggregate_symbols(message))
            return
        ws, uri = self.document(params)
        if method == "completionItem/resolve":
            data = params.get("data") if isinstance(params, dict) else None
            owner = data.get("__paralean_completion") if isinstance(data, dict) else None
            if not isinstance(owner, dict):
                await self.error(client_id, -32602, "Completion item lacks Paralean owner")
                return
            ws = self.workspaces.get(owner.get("workspace"))
            uri = owner.get("document")
            if ws is None or uri not in ws.open_documents or ws.open_documents[uri]["version"] != owner.get("version") or ws.environment != owner.get("environment") or ws.generation != owner.get("generation"):
                await self.error(client_id, -32800, "Completion item expired")
                return
        if method == "$/lean/rpc/connect" and "uri" not in params:
            await self.error(client_id, -32602, "RPC connect requires uri")
            return
        if method.startswith("$/lean/rpc/") and "sessionId" in params:
            session = self.sessions.get(str(params["sessionId"]))
            if session is None or session[1:3] != (session[0].generation, session[0].environment):
                if client_id is not None:
                    await self.error(client_id, -32002, "RPC session expired")
                return
            if ws is not None and ws is not session[0]:
                if client_id is not None:
                    await self.error(client_id, -32602, "RPC session belongs to another workspace")
                return
            if uri is not None and uri != session[3]:
                if client_id is not None:
                    await self.error(client_id, -32602, "RPC session belongs to another document")
                return
            ws = session[0]
        if ws is None:
            await self.error(client_id, -32602, "No workspace owns the request URI") if client_id is not None else None
            return
        if ws.refresh_environment():
            await ws.replace_worker()
        if method == "completionItem/resolve" and (owner.get("generation") != ws.generation or owner.get("environment") != ws.environment):
            await self.error(client_id, -32800, "Completion item expired")
            return
        if method.startswith("$/lean/rpc/") and "sessionId" in params and session[1:3] != (ws.generation, ws.environment):
            if client_id is not None:
                await self.error(client_id, -32002, "RPC session expired")
            return
        wire = copy.deepcopy(message)
        wire["params"] = self.map_in(params, ws)
        if method == "completionItem/resolve":
            original = wire["params"]["data"]["leanData"]
            if original is None:
                wire["params"].pop("data", None)
            else:
                wire["params"]["data"] = original
        if method.startswith("$/lean/rpc/") and "sessionId" in params:
            wire["params"]["sessionId"] = session[4]
        if client_id is None:
            try:
                await ws.notify(wire)
            except (ConnectionError, BrokenPipeError):
                pass
            return
        document = uri if uri in ws.open_documents else None
        expected_version = ws.open_documents[document]["version"] if document else None
        asyncio.create_task(self.route_request(ws, wire, client_id, document, expected_version))

    async def route_request(self, ws, message, client_id, document, expected_version):
        if client_id in self.cancelled:
            await self.error(client_id, -32800, "Request cancelled")
            self.cancelled.discard(client_id)
            return
        try:
            worker_id, future = await ws.request(message, client_id, document, expected_version=expected_version)
        except ValueError:
            await self.error(client_id, -32800, "Document changed before request dispatch")
            return
        except (OSError, ConnectionError, BrokenPipeError, asyncio.TimeoutError):
            await self.error(client_id, -32001, "Workspace worker unavailable")
            return
        self.requests.setdefault(client_id, []).append((ws, worker_id))
        result = await future
        self.requests[client_id] = [x for x in self.requests.get(client_id, []) if x != (ws, worker_id)]
        if client_id in self.cancelled:
            self.cancelled.discard(client_id)
            await self.error(client_id, -32800, "Request cancelled")
        elif result is None:
            await self.error(client_id, -32800, "Request cancelled or worker generation changed")
        else:
            result["id"] = client_id
            await self.send(result)

    async def aggregate_symbols(self, message):
        client_id = message["id"]
        if client_id in self.cancelled:
            self.cancelled.discard(client_id)
            await self.error(client_id, -32800, "Request cancelled")
            return
        for ws in self.workspaces.values():
            if ws.refresh_environment():
                try:
                    await ws.replace_worker()
                except (OSError, ConnectionError, asyncio.TimeoutError):
                    await self.error(client_id, -32001, "Workspace index worker unavailable")
                    return
        snapshot = {ws.name: (ws.environment, ws.generation,
                              {uri: state["version"] for uri, state in ws.open_documents.items()})
                    for ws in self.workspaces.values()}
        jobs = []
        for ws in self.workspaces.values():
            try:
                search = copy.deepcopy(message)
                search["method"] = "workspace/symbol"
                worker_id, future = await ws.request(search, client_id)
                self.requests.setdefault(client_id, []).append((ws, worker_id))
                jobs.append((ws, worker_id, future))
            except (OSError, ConnectionError, BrokenPipeError, asyncio.TimeoutError, ValueError):
                pass
        combined = []
        for ws, worker_id, future in jobs:
            response = await future
            if response and isinstance(response.get("result"), list):
                combined.extend(response["result"])
            self.requests[client_id] = [x for x in self.requests.get(client_id, []) if x != (ws, worker_id)]
        for ws in self.workspaces.values():
            combined.extend(self.registry_symbols(ws, message.get("params", {}).get("query", "")))
        combined = list({(item.get("name"), item.get("location", {}).get("uri"),
                          item.get("location", {}).get("range", {}).get("start", {}).get("line")): item
                         for item in combined if isinstance(item, dict)}.values())
        fresh = all(snapshot[ws.name] == (ws.environment, ws.generation,
                        {uri: state["version"] for uri, state in ws.open_documents.items()})
                    for ws in self.workspaces.values())
        if client_id in self.cancelled:
            self.cancelled.discard(client_id)
            await self.error(client_id, -32800, "Request cancelled")
        elif not fresh:
            await self.error(client_id, -32800, "Workspace index changed during search")
        else:
            await self.send({"jsonrpc": "2.0", "id": client_id, "result": combined})

    async def deliver_change(self, ws, wire, uri, method):
        try:
            async with ws.change_lock:
                await ws.start()
                await asyncio.wait_for(ws.ready.wait(), 15)
                state = ws.open_documents.get(uri)
                if method in ("textDocument/didOpen", "textDocument/didChange"):
                    if not state or state.get("sent_generation") == ws.generation and state.get("sent_version") == state["version"]:
                        return
                    if state.get("sent_generation") == ws.generation:
                        wire = {"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {"textDocument": {"uri": self.to_worker_uri(ws, uri), "version": state["version"]}, "contentChanges": [{"text": state["text"]}]}}
                    else:
                        wire = {"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {"uri": self.to_worker_uri(ws, uri), "languageId": "lean4", "version": state["version"], "text": state["text"]}}}
                elif method == "textDocument/didClose" and state:
                    return
                await ws.write(wire)
                if state:
                    state["sent_generation"] = ws.generation
                    state["sent_version"] = state["version"]
        except (OSError, ConnectionError, BrokenPipeError, asyncio.TimeoutError):
            self.debug("change queued for worker replay", ws.name, method, uri)

    async def error(self, client_id, code, reason):
        await self.send({"jsonrpc": "2.0", "id": client_id, "error": {"code": code, "message": reason}})


def apply_change(text, change):
    """Apply LSP UTF-16 ranges to the replay buffer."""
    lines = text.splitlines(keepends=True)
    def offset(position):
        line = position["line"]
        prefix = sum(len(part) for part in lines[:line])
        content = lines[line] if line < len(lines) else ""
        if position["character"] == 0:
            return prefix
        used = 0
        for index, char in enumerate(content):
            used += 2 if ord(char) > 0xFFFF else 1
            if used >= position["character"]:
                return prefix + index + (used == position["character"])
        return prefix + len(content)
    region = change["range"]
    return text[:offset(region["start"])] + change["text"] + text[offset(region["end"]):]


async def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workspace", action="append", required=True, help="NAME=ROOT")
    parser.add_argument("--environment", action="append", default=[], help="NAME=IMMUTABLE_ENVIRONMENT_ID")
    parser.add_argument("--workspace-env", action="append", default=[], help="NAME=JSON_FILE of per-worker environment variables")
    parser.add_argument("--worker-command", action="append", default=[], help="NAME=JSON_ARGV for this workspace's worker transport")
    parser.add_argument("--worker-root", action="append", default=[], help="NAME=ABS_PATH visible to that workspace's worker")
    parser.add_argument("--lean-cmd", nargs="+", default=["lake", "env", "lean", "--server"])
    args = parser.parse_args()
    environments = dict(item.split("=", 1) for item in args.environment)
    workspace_env_files = dict(item.split("=", 1) for item in args.workspace_env)
    worker_roots = dict(item.split("=", 1) for item in args.worker_root)
    try:
        worker_commands = {name: json.loads(value) for name, value in
                           (item.split("=", 1) for item in args.worker_command)}
    except (ValueError, json.JSONDecodeError) as exc:
        parser.error(f"invalid worker command JSON: {exc}")
    if any(not isinstance(argv, list) or not argv or any(not isinstance(arg, str) for arg in argv)
           for argv in worker_commands.values()):
        parser.error("worker command must be a nonempty JSON string array")
    if any(not pathlib.Path(path).is_absolute() for path in worker_roots.values()):
        parser.error("worker root must be absolute")
    proxy = Proxy({}, args.lean_cmd)
    for item in args.workspace:
        name, root = item.split("=", 1)
        if not pathlib.Path(root).is_dir() or name in proxy.workspaces:
            parser.error("workspace roots must exist and names must be unique")
        workspace_root = pathlib.Path(root).resolve()
        work_root = workspace_root / "work" if (workspace_root / "work").is_dir() else workspace_root
        cache_root = work_root.parent / "cache" if work_root.name == "work" and (work_root.parent / "cache").is_dir() else workspace_root / "cache"
        overrides = {"PARALEAN_STORE": str(cache_root),
                     "PARALEAN_WORK_ROOT": str(work_root),
                     "PARALEAN_VISIBILITY": "1"}
        for key, filename in (("PARALEAN_TRUST", "trust.json"), ("PARALEAN_KEYS", "keys.json")):
            candidate = (work_root.parent if cache_root == work_root.parent / "cache" else workspace_root) / filename
            if candidate.is_file():
                overrides[key] = str(candidate)
        for key in ("PARALEAN_TRUST", "PARALEAN_KEYS", "PARALEAN_PLR"):
            if key not in overrides and key in os.environ:
                overrides[key] = os.environ[key]
        try:
            proxy.workspaces[name] = Workspace(proxy, name, root, environments.get(name, "local"), overrides,
                                               workspace_env_files.get(name), worker_commands.get(name), worker_roots.get(name))
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            parser.error(str(exc))
    stores = [pathlib.Path(ws.env_overrides["PARALEAN_STORE"]).resolve() for ws in proxy.workspaces.values()]
    if len(stores) != len(set(stores)):
        parser.error("each workspace must use a distinct PARALEAN_STORE")
    loop = asyncio.get_running_loop()
    reader = asyncio.StreamReader()
    protocol = asyncio.StreamReaderProtocol(reader)
    await loop.connect_read_pipe(lambda: protocol, sys.stdin.buffer)
    transport, output_protocol = await loop.connect_write_pipe(asyncio.streams.FlowControlMixin, sys.stdout.buffer)
    proxy.client_writer = asyncio.StreamWriter(transport, output_protocol, reader, loop)
    try:
        while not proxy.stopping:
            message = await read_message(reader)
            try:
                await proxy.dispatch(message)
            except (OSError, ValueError, asyncio.TimeoutError) as exc:
                if "id" in message:
                    await proxy.error(message["id"], -32001, str(exc))
                else:
                    proxy.debug("notification refused", message.get("method"), exc)
    except EOFError:
        pass
    finally:
        proxy.stopping = True
        for ws in proxy.workspaces.values():
            ws.stop_process()


if __name__ == "__main__":
    asyncio.run(main())
