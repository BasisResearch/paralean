"""Controller boundary for private editor capture and explicit publication.

The router owns buffers and serializes accepted edits with ``mutation_lock``.
This module never publishes from a document notification. A publication request
must name a frozen target, its owner and dispatch epoch explicitly.
"""

from __future__ import annotations

import asyncio
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import urllib.parse


class BridgeError(ValueError):
    pass


def _hash(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


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
        marker = json.loads(path.read_text())
        group = marker.get("group")
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
        return source.relative_to(work).as_posix(), state

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
            worker = await asyncio.create_subprocess_exec(
                self.capture_binary, "ws-capture-server", "--dir", str(ws.root),
                cwd=ws.root, env={**os.environ, **ws.env_overrides},
                stdin=asyncio.subprocess.PIPE, stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.DEVNULL, start_new_session=True)
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
        if not line:
            await self._stop_worker(key)
            raise BridgeError("capture worker exited")
        result = json.loads(line)
        self._assert_current(ws, uri, stamp)
        if result.get("error"):
            raise BridgeError(str(result["error"]))
        if any(result.get(k) != stamp[k] for k in ("file", "version", "environment", "generation")):
            raise BridgeError("capture worker returned a mismatched stamp")
        capture = result.get("capture")
        if not isinstance(capture, dict) or not isinstance(capture.get("packages"), list):
            raise BridgeError("capture worker returned malformed packages")
        if capture.get("rejected") or capture.get("rejectedPids"):
            raise BridgeError("capture contains rejected declarations")
        record = {**stamp, "packages": capture["packages"],
                  "groups": capture.get("groups"),
                  "registry": result.get("registry"),
                  "reusedCommands": result.get("reusedCommands"),
                  "newCommands": result.get("newCommands")}
        self.captures[key] = record
        return record

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
            source = (ws.root / "work" / stamp["file"]).resolve()
            source.write_text(ws.open_documents[uri]["text"])

            def precommit_guard() -> None:
                self._assert_current(ws, uri, stamp)
                self._assert_store_policy(ws)
                self._assert_authoring(ws)
                if not source.is_file() or hashlib.sha256(source.read_bytes()).hexdigest() != stamp["source_sha256"]:
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
