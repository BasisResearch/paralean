"""P5 adapter over P3 transparent workspaces and the P5 task journal.

The task journal contains the frozen task, controller progress, recoverable source
and encrypted local signing material. P3/P2 remain the authority for published
Lean declarations. Every public method is synchronous for the controller.
"""
from __future__ import annotations

import base64
import hashlib
import hmac
import json
import os
from pathlib import Path
import socket
import signal
import stat
import time
import atexit
import subprocess
import tempfile
from typing import Any

from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.kdf.hkdf import HKDF

ROOT = Path(__file__).resolve().parents[1]


class BackendError(RuntimeError):
    pass


def _canonical(obj: Any) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def _hex_id(value: object) -> str:
    if not isinstance(value, str) or len(value) != 64 or any(c not in "0123456789abcdef" for c in value):
        raise BackendError("malformed object ID in workspace cache")
    return value


def _source_parts(relative: str) -> tuple[str, ...]:
    if not isinstance(relative, str):
        raise BackendError(f"unsafe source path: {relative}")
    p = Path(relative)
    if (p.is_absolute() or
            not relative or any(part in ("", ".", "..") for part in relative.split("/")) or
            "\\" in relative or "\0" in relative):
        raise BackendError(f"unsafe source path: {relative}")
    return p.parts


def _source_fd(work: Path, relative: str, *, create_dirs: bool = False) -> tuple[int, str]:
    """Walk a worker-controlled source path without following symlinks."""
    parts = _source_parts(relative)
    fd = os.open(work, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        for part in parts[:-1]:
            if create_dirs:
                try:
                    os.mkdir(part, dir_fd=fd)
                except FileExistsError:
                    pass
            next_fd = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                              dir_fd=fd)
            os.close(fd)
            fd = next_fd
        return fd, parts[-1]
    except BaseException:
        os.close(fd)
        raise


def _read_source(work: Path, relative: str) -> str | None:
    try:
        directory_fd, name = _source_fd(work, relative)
    except FileNotFoundError:
        return None
    try:
        try:
            fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,
                         dir_fd=directory_fd)
        except FileNotFoundError:
            return None
        with os.fdopen(fd, "rb") as handle:
            if not stat.S_ISREG(os.fstat(handle.fileno()).st_mode):
                raise BackendError(f"source is not a regular file: {relative}")
            return handle.read().decode()
    finally:
        os.close(directory_fd)


def _write_source_if_missing(work: Path, relative: str, text: str) -> None:
    directory_fd, name = _source_fd(work, relative, create_dirs=True)
    try:
        try:
            fd = os.open(name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                         0o600, dir_fd=directory_fd)
        except FileExistsError:
            # A symlink or device at this name must not be accepted as source.
            _read_source(work, relative)
            return
        with os.fdopen(fd, "w") as handle:
            handle.write(text)
    finally:
        os.close(directory_fd)


class Backend:
    _JOURNAL_DOMAIN = b"paralean/p5/journal-hmac/v1\0"
    _CONTROLLER_ONLY_ENV = ("PARALEAN_P5_RECOVERY_SECRET", "PARALEAN_GARAGE_ADMIN_TOKEN",
                            "PARALEAN_GARAGE_RPC_SECRET")

    @classmethod
    def _runtime_env(cls, env: dict) -> dict:
        return {key: value for key, value in env.items() if key not in cls._CONTROLLER_ONLY_ENV}

    @classmethod
    def _journal_key(cls, task_id: str, env: dict) -> bytes:
        secret = env.get("PARALEAN_P5_RECOVERY_SECRET")
        deployment = env.get("PARALEAN_DEPLOYMENT")
        if not secret or not deployment:
            raise BackendError("deployment recovery secret is required for task journal authentication")
        return HKDF(algorithm=hashes.SHA256(), length=32,
                    salt=(deployment + "\0" + task_id).encode(),
                    info=cls._JOURNAL_DOMAIN).derive(secret.encode())

    @classmethod
    def _sign_journal(cls, payload: dict, task_id: str, env: dict) -> dict:
        unsigned = {k: v for k, v in payload.items() if k != "journal_hmac"}
        if unsigned.get("task") != task_id:
            raise BackendError("task journal names another task")
        mac = hmac.new(cls._journal_key(task_id, env),
                       cls._JOURNAL_DOMAIN + _canonical(unsigned), hashlib.sha256).hexdigest()
        return {**unsigned, "journal_hmac": "v1:" + mac}

    @classmethod
    def _verify_journal(cls, payload: object, task_id: str, env: dict,
                        sequence: int) -> dict:
        if not isinstance(payload, dict) or payload.get("task") != task_id:
            raise BackendError("task journal is malformed or names another task")
        claimed = payload.get("journal_hmac")
        if not isinstance(claimed, str) or not claimed.startswith("v1:"):
            raise BackendError("task journal has no supported authentication tag")
        expected = cls._sign_journal(payload, task_id, env)["journal_hmac"]
        if not hmac.compare_digest(claimed, expected):
            raise BackendError("task journal authentication failed")
        if payload.get("journal_sequence") != sequence:
            raise BackendError("task journal sequence does not match the durable head")
        return payload

    def __init__(self, task: dict, state_dir: Path, env: dict | None = None):
        self.task = task
        self.task_id = str(task["id"])
        self.state_dir = Path(state_dir).resolve()
        self.env = dict(os.environ)
        if env:
            self.env.update({k: str(v) for k, v in env.items()})
        self.bridge = self.env.get("PARALEAN_P5_BRIDGE", str(ROOT / "store-bridge" / "target" / "release" / "paralean-p5-store"))
        self.ws = self.env.get("PARALEAN_P5_WS", str(ROOT.parent / "p3-remote" / "scripts" / "ws.py"))
        self.plr = self.env.get("PARALEAN_PLR", str(ROOT.parent / "p2" / "target" / "release" / "plr"))
        self.lean = self.env.get("PARALEAN_BIN", "paralean")
        self.agents = list(task.get("agents", [f"w{i}" for i in range(int(task.get("workers", 0)))]))
        self.contract_hash = hashlib.sha256(_canonical(task)).hexdigest()
        self.sequence = 0
        self.payload: dict | None = None
        self.paths: dict[str, Path] = {}
        self.validator_process = None
        self.env.setdefault("PARALEAN_KEYS", str(self.state_dir / "keys.json"))
        self.env.setdefault("PARALEAN_TRUST", str(self.state_dir / "trust.json"))
        self._require_environment()

    @staticmethod
    def list_tasks(env: dict | None = None) -> list[dict]:
        """Enumerate durable task heads without a local task file or remembered ID."""
        source_env = {**os.environ, **(env or {})}
        bridge = source_env.get("PARALEAN_P5_BRIDGE", str(ROOT / "store-bridge" / "target" / "release" / "paralean-p5-store"))
        child_env = Backend._runtime_env(source_env)
        proc = subprocess.run([bridge, "list"], env=child_env, capture_output=True, text=True)
        if proc.returncode:
            raise BackendError("task catalogue enumeration failed")
        value = json.loads(proc.stdout)
        tasks = value.get("tasks")
        if not isinstance(tasks, list):
            raise BackendError("task catalogue response is malformed")
        return tasks

    @classmethod
    def recover_task(cls, task_id: str, state_dir: Path, env: dict | None = None) -> "Backend":
        """Recover a deleted task file and desktop from FDB/Garage by task ID."""
        source_env = {**os.environ, **(env or {})}
        bridge = source_env.get("PARALEAN_P5_BRIDGE", str(ROOT / "store-bridge" / "target" / "release" / "paralean-p5-store"))
        state_dir = Path(state_dir).resolve()
        state_dir.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(dir=state_dir, delete=False) as tmp:
            path = Path(tmp.name)
        try:
            bridge_env = cls._runtime_env(source_env)
            proc = subprocess.run([bridge, "get", "--task", task_id, "--out", str(path)],
                                  env=bridge_env, capture_output=True, text=True)
            if proc.returncode:
                raise BackendError("task recovery from store failed")
            result = json.loads(proc.stdout)
            if not result.get("found"):
                raise BackendError(f"no durable task: {task_id}")
            payload = cls._verify_journal(json.loads(path.read_text()), task_id, source_env,
                                          int(result["sequence"]))
            task = payload["spec"]
            backend = cls(task, state_dir, env)
            backend.sequence = int(result["sequence"])
            backend.payload = payload
            if backend.contract_hash != payload.get("contract_hash"):
                raise BackendError("recovered task contract hash mismatch")
            backend._restore_keys(payload)
            return backend
        finally:
            path.unlink(missing_ok=True)

    def _require_environment(self) -> None:
        required = ("PARALEAN_DEPLOYMENT", "PARALEAN_FDB_CLUSTER", "PARALEAN_S3_ENDPOINT",
                    "PARALEAN_S3_ACCESS_KEY", "PARALEAN_S3_SECRET_KEY", "PARALEAN_VALIDATOR")
        missing = [name for name in required if not self.env.get(name)]
        if missing:
            raise BackendError("missing deployment configuration: " + ", ".join(missing))

    def _run(self, argv: list[str], *, env: dict | None = None, cwd: Path | None = None) -> Any:
        child_env = self._runtime_env(self.env)
        for key, value in (env or {}).items():
            if value is None:
                child_env.pop(key, None)
            else:
                child_env[key] = value
        proc = subprocess.run(argv, cwd=cwd, env=child_env,
                              text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if proc.returncode:
            self.state_dir.mkdir(parents=True, exist_ok=True)
            detail = proc.stderr[-4000:]
            for key in ("PARALEAN_S3_SECRET_KEY", "PARALEAN_S3_ACCESS_KEY",
                        *self._CONTROLLER_ONLY_ENV):
                if self.env.get(key):
                    detail = detail.replace(self.env[key], "[redacted]")
            log = self.state_dir / "backend.log"
            with log.open("a") as handle:
                handle.write(f"{Path(argv[0]).name} {argv[1] if len(argv)>1 else ''} exit={proc.returncode}\n{detail}\n")
            log.chmod(0o600)
            raise BackendError(f"{Path(argv[0]).name} {argv[1] if len(argv)>1 else ''} failed (exit {proc.returncode}); see {log}")
        lines = proc.stdout.strip().splitlines()
        if not lines:
            return {}
        try:
            return json.loads(lines[-1])
        except json.JSONDecodeError:
            return {"text": proc.stdout}

    def _bridge(self, *args: str, env: dict | None = None) -> dict:
        return self._run([self.bridge, *args], env=env)

    def _encryption_key(self, *, legacy: bool = False) -> bytes:
        if legacy:
            secret = self.env["PARALEAN_S3_SECRET_KEY"]
        else:
            secret = self.env.get("PARALEAN_P5_RECOVERY_SECRET")
            if not secret:
                raise BackendError("PARALEAN_P5_RECOVERY_SECRET is required for durable signing keys")
        salt = (self.env["PARALEAN_DEPLOYMENT"] + "/p5/" + self.task_id).encode()
        return hashlib.pbkdf2_hmac("sha256", secret.encode(), salt, 100_000, 32)

    def _seal(self, data: bytes) -> str:
        key = self._encryption_key()
        nonce = os.urandom(12)
        ciphertext = nonce + AESGCM(key).encrypt(nonce, data, self.contract_hash.encode())
        return "v2:" + base64.b64encode(ciphertext).decode()

    def _open(self, value: str) -> bytes:
        legacy = not value.startswith("v2:")
        encoded = value if legacy else value[3:]
        b = base64.b64decode(encoded, validate=True)
        return AESGCM(self._encryption_key(legacy=legacy)).decrypt(
            b[:12], b[12:], self.contract_hash.encode())

    def _key_paths(self) -> list[Path]:
        out = []
        for name in ("PARALEAN_KEYS", "PARALEAN_TRUST"):
            if self.env.get(name):
                out.append(Path(self.env[name]))
        keys = self.env.get("PARALEAN_KEYS")
        if keys:
            out.extend(Path(keys).parent / f"keys-{agent}.json" for agent in self.agents)
        return out

    def _read_snapshot(self) -> dict | None:
        self.state_dir.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(dir=self.state_dir, delete=False) as tmp:
            out = Path(tmp.name)
        try:
            result = self._bridge("get", "--task", self.task_id, "--out", str(out))
            if not result.get("found"):
                return None
            data = self._verify_journal(json.loads(out.read_text()), self.task_id, self.env,
                                        int(result["sequence"]))
            if data.get("task") != self.task_id or data.get("contract_hash") != self.contract_hash:
                raise BackendError("stored task differs from the supplied frozen task")
            self.sequence = int(result["sequence"])
            self.payload = data
            return data
        finally:
            out.unlink(missing_ok=True)

    def _commit(self, data: dict) -> str:
        self.state_dir.mkdir(parents=True, exist_ok=True)
        if data.get("keys") and any(not encrypted.startswith("v2:") for encrypted in data["keys"].values()):
            data = dict(data)
            data["keys"] = {name: self._seal(self._open(encrypted))
                            for name, encrypted in data["keys"].items()}
            data["format"] = 2
        data = self._sign_journal({**data, "journal_sequence": self.sequence + 1},
                                  self.task_id, self.env)
        with tempfile.NamedTemporaryFile(mode="wb", dir=self.state_dir, delete=False) as tmp:
            path = Path(tmp.name)
            tmp.write(_canonical(data))
        try:
            result = self._bridge("put", "--task", self.task_id, "--file", str(path),
                                  "--expected", str(self.sequence))
        finally:
            path.unlink(missing_ok=True)
        self.sequence = int(result["sequence"])
        self.payload = data
        return result["blob"]

    def _freeze_contracts(self) -> dict[str, str]:
        targets = [{"name": t["name"], "statement": t["statement"]}
                   for t in self.task.get("targets", [])]
        if not targets:
            return {}
        lean_exe = self.env.get("PARALEAN_P5_LEAN")
        if not lean_exe:
            fork = self.env.get("PARALEAN_FORK_PREFIX")
            lean_exe = str(Path(fork) / "bin" / "lean") if fork else "lean"
        library = self.env.get("PARALEAN_LIB")
        if not library:
            raise BackendError("PARALEAN_LIB is required to freeze P1 statement hashes")
        path_env = library + (os.pathsep + self.env["LEAN_PATH"] if self.env.get("LEAN_PATH") else "")
        with tempfile.NamedTemporaryFile(mode="w", dir=self.state_dir, delete=False) as tmp:
            path = Path(tmp.name)
            json.dump({"targets": targets}, tmp)
        try:
            hashes = self._run([lean_exe, "--run", str(ROOT / "Contract.lean"), "--input", str(path)],
                               env={"LEAN_PATH": path_env})
        finally:
            path.unlink(missing_ok=True)
        if set(hashes) != {t["name"] for t in targets}:
            raise BackendError("contract extractor omitted or added a target")
        if any(not isinstance(v, str) or len(v) != 64 or
               any(c not in "0123456789abcdef" for c in v) for v in hashes.values()):
            raise BackendError("contract extractor returned an invalid P1 statement hash")
        return hashes

    def setup(self) -> None:
        if self._read_snapshot() is not None:
            assert self.payload is not None
            self._restore_keys(self.payload)
            return
        keys = self.env.get("PARALEAN_KEYS")
        trust = self.env.get("PARALEAN_TRUST")
        if not keys or not trust:
            raise BackendError("PARALEAN_KEYS and PARALEAN_TRUST paths are required")
        key_path = Path(keys)
        if not key_path.exists():
            key_path.parent.mkdir(parents=True, exist_ok=True)
            rogue = key_path.with_name("rogue-keys.json")
            self._run([self.plr, "keys-init", str(key_path), str(trust), str(rogue),
                       "--agents", ",".join(self.agents)])
        hashes = self._freeze_contracts()
        self._commit({"format": 2, "task": self.task_id, "contract_hash": self.contract_hash,
                      "contract_hashes": hashes, "spec": self.task, "state": {}, "sources": {}, "keys": self._capture_keys()})

    def _start_validator(self) -> None:
        if self.validator_process is not None and self.validator_process.poll() is None:
            return
        host, port_text = self.env["PARALEAN_VALIDATOR"].rsplit(":", 1)
        port = int(port_text)
        with socket.socket() as probe:
            probe.settimeout(0.2)
            if probe.connect_ex((host, port)) == 0:
                raise BackendError("validator address is occupied by another process")
        p3 = self.env.get("PARALEAN_P3_BIN", str(ROOT.parent / "p2" / "target" / "release" / "paralean-p3"))
        workdir = self.state_dir / "validator-work"
        workdir.mkdir(parents=True, exist_ok=True)
        log = open(self.state_dir / "validator.log", "ab", buffering=0)
        try:
            guard = Path(__file__).with_name("worker_guard.py")
            self.validator_process = subprocess.Popen(
                ["python3", str(guard), p3, "validator", "--listen", self.env["PARALEAN_VALIDATOR"], "--key", "v0",
                 "--max-running", "1", "--max-queued", "8", "--workdir", str(workdir)],
                env={**self._runtime_env(self.env),
                     "PARALEAN_P5_PARENT_PID": str(os.getpid())},
                stdin=subprocess.DEVNULL, stdout=log, stderr=log, start_new_session=True)
        finally:
            log.close()
        for _ in range(50):
            if self.validator_process.poll() is not None:
                raise BackendError("validator exited during startup")
            with socket.socket() as probe:
                probe.settimeout(0.1)
                if probe.connect_ex((host, port)) == 0:
                    atexit.register(self.close)
                    return
            time.sleep(0.1)
        self.close()
        raise BackendError("validator did not become ready")

    def close(self) -> None:
        process = self.validator_process
        self.validator_process = None
        if process is not None and process.poll() is None:
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait(timeout=5)

    def _capture_keys(self) -> dict[str, str]:
        keys = {}
        for path in self._key_paths():
            if path.exists():
                keys[path.name] = self._seal(path.read_bytes())
        return keys

    def _restore_keys(self, payload: dict) -> None:
        own = self.env.get("PARALEAN_KEYS")
        if not own:
            return
        dest = Path(own).parent
        dest.mkdir(parents=True, exist_ok=True)
        for name, encrypted in payload.get("keys", {}).items():
            if Path(name).name != name:
                raise BackendError("unsafe key filename in task store")
            path = dest / name
            plaintext = self._open(encrypted)
            with tempfile.NamedTemporaryFile(mode="wb", dir=dest, delete=False) as tmp:
                staged = Path(tmp.name)
                tmp.write(plaintext)
                tmp.flush()
                os.fsync(tmp.fileno())
            try:
                try:
                    # link installs the complete file only if the name is unused.
                    os.link(staged, path)
                except FileExistsError:
                    # A stale desktop must not silently replace a recovered signer.
                    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
                    with os.fdopen(fd, "rb") as handle:
                        if not stat.S_ISREG(os.fstat(handle.fileno()).st_mode) or handle.read() != plaintext:
                            raise BackendError(f"local key differs from authenticated task store: {name}")
            finally:
                staged.unlink(missing_ok=True)

    def _sources(self) -> dict:
        result = {}
        for agent, path in self.paths.items():
            files = {}
            for rel in self.task.get("files", []):
                source = _read_source(path / "work", rel)
                if source is not None:
                    files[rel] = source
            result[agent] = files
        return result

    def provision(self, agent: str, directory: Path) -> None:
        if agent not in self.agents:
            raise BackendError(f"unregistered agent: {agent}")
        directory = Path(directory).resolve()
        self.paths[agent] = directory
        if self.payload is None:
            self.setup()
        assert self.payload is not None
        self._restore_keys(self.payload)
        if not (directory / "agent").exists():
            directory.mkdir(parents=True, exist_ok=True)
            self._run(["python3", self.ws, "init", str(directory), agent])
        saved = self.payload.get("sources", {}).get(agent, {})
        for rel in self.task.get("files", []):
            text = saved.get(rel, self.task.get("sources", {}).get(rel, ""))
            _write_source_if_missing(directory / "work", rel, text)

    def _ws(self, action: str, agent: str, directory: Path, *args: str) -> dict:
        env = {"PARALEAN_AGENT": agent}
        proc = subprocess.run(["python3", self.ws, action, str(directory), *args],
                              env={**self._runtime_env(self.env),
                                   **env}, text=True, capture_output=True)
        if proc.returncode:
            raise BackendError(f"ws.py {action} failed for {agent} (exit {proc.returncode})")
        result = {}
        for line in proc.stdout.splitlines():
            step, _, body = line.partition(" ")
            if body:
                try:
                    result.setdefault(step, []).append(json.loads(body))
                except json.JSONDecodeError:
                    pass
        return result

    def sync(self, agent: str, directory: Path) -> dict:
        self.paths[agent] = Path(directory).resolve()
        result = self._ws("sync", agent, directory)
        pull = result.get("pull", [{}])[-1]
        result["metrics"] = {"transfer_bytes": int(pull.get("bytes") or 0),
                             "transfer_ms": float(pull.get("ms") or 0), "check_ms": 0}
        return result

    def assign_target(self, name: str, agent: str) -> int:
        if name not in {t["name"] for t in self.task.get("targets", [])}:
            raise BackendError(f"target outside frozen task: {name}")
        if agent not in self.agents:
            raise BackendError(f"unregistered agent: {agent}")
        request = hashlib.sha256(os.urandom(32)).hexdigest()[:32]
        result = self._bridge("assign-target", "--name", name, "--ws", agent,
                              "--request", request)
        return int(result["epoch"])

    def observe_target(self, name: str, agent: str) -> dict:
        """Read the durable owner, epoch and head before dispatch or recovery."""
        if name not in {t["name"] for t in self.task.get("targets", [])}:
            raise BackendError(f"target outside frozen task: {name}")
        if agent not in self.agents:
            raise BackendError(f"unregistered agent: {agent}")
        result = self._bridge("observe-target", "--name", name, "--ws", agent)
        if (result.get("name") != name or not isinstance(result.get("epoch"), int) or
                not isinstance(result.get("owner"), str) or
                not isinstance(result.get("assigned_to_agent"), bool) or
                (result.get("head") is not None and not isinstance(result.get("head"), str))):
            raise BackendError("malformed durable target observation")
        return result

    def fence_unfinished(self, name: str, agent: str, expected_epoch: int,
                         expected_head: str | None, request: str) -> dict:
        """Fence a still-unpublished dispatch, or report that its head changed."""
        if name not in {t["name"] for t in self.task.get("targets", [])}:
            raise BackendError(f"target outside frozen task: {name}")
        if agent not in self.agents:
            raise BackendError(f"unregistered agent: {agent}")
        if not isinstance(expected_epoch, int) or expected_epoch < 0:
            raise BackendError("invalid expected target epoch")
        if not request or len(request.encode()) > 128:
            raise BackendError("invalid stable fence request ID")
        if expected_head is not None and (len(expected_head) != 64 or
                any(c not in "0123456789abcdef" for c in expected_head)):
            raise BackendError("invalid expected target head")
        result = self._bridge("fence-unfinished", "--name", name, "--ws", agent,
                              "--expected-epoch", str(expected_epoch),
                              "--expected-head", expected_head or "none", "--request", request)
        if (result.get("outcome") not in ("fenced", "changed") or result.get("name") != name or
                not isinstance(result.get("owner"), str) or not isinstance(result.get("epoch"), int) or
                (result.get("head") is not None and not isinstance(result.get("head"), str))):
            raise BackendError("malformed guarded target-fence result")
        return result

    @staticmethod
    def _transfer_rows(directory: Path) -> list[dict]:
        path = directory / "cache" / "p3" / "transfer.jsonl"
        if not path.exists():
            return []
        rows = []
        for line in path.read_text().splitlines():
            try:
                rows.append(json.loads(line))
            except json.JSONDecodeError:
                pass
        return rows

    def _dependency_closure(self, cache: Path, roots: list[str]) -> set[str]:
        capsules = cache / "p3" / "capsules"
        by_gid = {}
        by_capsule = {}
        if capsules.exists():
            for file in capsules.glob("*.json"):
                _hex_id(file.stem)
                meta = json.loads(_read_source(capsules, file.name))
                if meta.get("gid"):
                    by_gid[_hex_id(meta["gid"])] = meta
                    by_capsule[file.stem] = meta["gid"]
        closure: set[str] = set()
        todo = [by_capsule.get(root, root) for root in roots]
        while todo:
            gid = todo.pop()
            if gid in closure:
                continue
            closure.add(gid)
            meta = by_gid.get(gid)
            if meta:
                todo.extend(meta.get("deps", []))
        return closure

    def _required_dependency_gids(self, names: list[str]) -> dict[str, str]:
        if not names:
            return {}
        verified = self.validate(names)
        if not verified["ok"]:
            raise BackendError("required predecessor target is not currently verified")
        groups = {name: verified["targets"][name]["group"] for name in names}
        found = {}
        for directory in self.paths.values():
            records = directory / "cache" / "p3" / "records"
            for record in records.glob("m-*.json"):
                marker = json.loads(_read_source(records, record.name))
                for name, group in groups.items():
                    if marker.get("group") == group:
                        capsule_root = directory / "cache" / "p3" / "capsules"
                        capsule_text = _read_source(capsule_root, _hex_id(marker.get("capsule")) + ".json")
                        if capsule_text is not None:
                            found[name] = _hex_id(json.loads(capsule_text)["gid"])
        if set(found) != set(names):
            raise BackendError("published predecessor capsule is missing from the synced cache")
        return found

    def publish(self, agent: str, directory: Path, file: str, targets: list[str] = (), epoch: int | None = None) -> dict:
        if file not in self.task.get("files", []):
            raise BackendError(f"file outside frozen task: {file}")
        directory = Path(directory).resolve()
        self.paths[agent] = directory
        before_transfer = len(self._transfer_rows(directory))
        if not targets:
            result = self._ws("publish", agent, directory, file)
            rows = self._transfer_rows(directory)[before_transfer:]
            return {"groups": result.get("published", [[]])[-1], "steps": result,
                    "metrics": {"transfer_bytes": sum(int(r.get("bytes", 0)) for r in rows),
                                "transfer_ms": sum(float(r.get("ms") or 0) for r in rows if r.get("kind") != "validate-target"),
                                "check_ms": sum(float(v.get("ms") or 0) for v in result.get("validate", []))}}
        if len(targets) != 1:
            raise BackendError("target publication accepts one fixed target at a time")
        self._start_validator()
        name = targets[0]
        if epoch is None:
            raise BackendError("target dispatch epoch is required")
        spec = next((t for t in self.task.get("targets", []) if t["name"] == name), None)
        if spec is None:
            raise BackendError(f"target outside frozen task: {name}")
        hashes = (self.payload or {}).get("contract_hashes", {})
        frozen = hashes.get(name)
        required_gids = self._required_dependency_gids(list(spec.get("deps", [])))
        if not frozen:
            raise BackendError(f"trusted frozen statement hash unavailable for {name}")
        cache = directory / "cache"
        own_env = {"PARALEAN_KEYS": str(directory / "keys.json"),
                   "PARALEAN_STORE": str(cache), "PARALEAN_VISIBILITY": "1",
                   "PARALEAN_VIS_EXCLUDE": file, "PARALEAN_AGENT": agent}
        self._run([self.plr, "pull", "--cache", str(cache)], env=own_env)
        cap = self._run([self.lean, "ws-capture", "--dir", str(directory), file], env=own_env)
        published = []
        check_ms = 0.0
        current_source = _read_source(directory / "work", file)
        if current_source is None:
            raise BackendError(f"target source is missing: {file}")
        for item in reversed(cap.get("packages", [])):
            pkg = f'{item["group"]}:{item["capsule"]}'
            names = {".".join(map(str, n)) if isinstance(n, list) else str(n)
                     for n in item.get("names", [])}
            if name not in names:
                # Non-target helpers use the ordinary P3 path in a separate call.
                continue
            capsule_text = json.loads(_read_source(cache / "p3" / "capsules",
                                                   _hex_id(item["capsule"]) + ".json"))["capsule"]["text"]
            if not capsule_text or capsule_text not in current_source:
                # ws-capture may report earlier rejected drafts; only publish the
                # declaration whose command is still present in this working file.
                continue
            closure = self._dependency_closure(cache, item.get("deps", []))
            missing = [dependency for dependency, gid in required_gids.items() if gid not in closure]
            if missing:
                raise BackendError(f"target {name} proof does not depend on required helpers: {missing}")
            self._run([self.plr, "stage", "--cache", str(cache), "--pkg", pkg], env=own_env)
            v = self._bridge("validate-target", "--cache", str(cache), "--ws", agent,
                             "--validator", self.env["PARALEAN_VALIDATOR"], "--pkg", pkg,
                             "--deps", ",".join(item.get("deps", [])), "--name", name,
                             "--statement-hash", frozen, "--epoch", str(epoch))
            check_ms += float(v.get("ms") or 0)
            if not v.get("accepted"):
                reason = str(v.get("reason") or "no reason returned")[:500]
                raise BackendError(f"trusted validator rejected target {name}: {reason}")
            receipt = directory / "p5-target-receipt.json"
            receipt.write_text(json.dumps(v))
            plan = directory / "p5-target-plan.json"
            planned = self._run([self.lean, "ws-plan", "--dir", str(directory), "--file", file,
                                 "--receipts", str(receipt), "--out", str(plan)], env=own_env)
            if planned.get("planned", 0) == 0:
                raise BackendError(f"no publication plan for target {name}")
            plan_entries = json.loads(plan.read_text())
            selected = [entry for entry in plan_entries if entry.get("group") == item["group"]]
            if len(selected) != 1:
                raise BackendError(f"target {name} has no unique publication plan")
            plan.write_text(json.dumps(selected))
            pub = self._bridge("publish-target", "--cache", str(cache), "--ws", agent,
                               "--plan", str(plan), "--name", name, "--epoch", str(epoch))
            self._run([self.plr, "pull", "--cache", str(cache), "--only", item["group"]], env=own_env)
            published.append(item["group"])
        if not published:
            raise BackendError(f"target {name} was not captured")
        self.sync(agent, directory)
        check = self.validate([name])
        if not check["ok"]:
            raise BackendError(f"published target {name} failed contract verification")
        rows = self._transfer_rows(directory)[before_transfer:]
        return {"groups": published, "target": name, "validated": check["targets"][name],
                "metrics": {"transfer_bytes": sum(int(r.get("bytes", 0)) for r in rows),
                            "transfer_ms": sum(float(r.get("ms") or 0) for r in rows if r.get("kind") != "validate-target"),
                            "check_ms": check_ms}}

    def _ensure_paths(self) -> None:
        if self.paths:
            return
        if self.payload is None:
            self.load_state()
        for agent in self.agents:
            directory = self.state_dir / agent
            self.provision(agent, directory)
            self.sync(agent, directory)

    def _target_candidates(self) -> dict[str, set[str]]:
        self._ensure_paths()
        found: dict[str, set[str]] = {}
        required = {t["name"] for t in self.task.get("targets", [])}
        for path in self.paths.values():
            rec = path / "cache" / "p3" / "records"
            caps = path / "cache" / "p3" / "capsules"
            if not rec.exists():
                continue
            for f in rec.glob("m-*.json"):
                m = json.loads(_read_source(rec, f.name))
                capsule_text = _read_source(caps, _hex_id(m.get("capsule")) + ".json")
                if capsule_text is None:
                    continue
                meta = json.loads(capsule_text)
                for raw in meta.get("publicNames", []):
                    n = ".".join(map(str, raw)) if isinstance(raw, list) else str(raw)
                    if n in required:
                        found.setdefault(n, set()).add(m["group"])
        return found

    def save_state(self, state: dict) -> str:
        if self.payload is None:
            self.setup()
        assert self.payload is not None
        data = dict(self.payload)
        data["state"] = state
        data["sources"] = {**data.get("sources", {}), **self._sources()}
        if not data.get("keys"):
            data["keys"] = self._capture_keys()
        return self._commit(data)

    def load_state(self) -> dict | None:
        data = self._read_snapshot()
        if data is None:
            return None
        self._restore_keys(data)
        return data.get("state") or None

    def validate(self, targets: list[str]) -> dict:
        candidates = self._target_candidates()
        hashes = (self.payload or {}).get("contract_hashes", {})
        out = {}
        for name in targets:
            frozen = hashes.get(name)
            groups = candidates.get(name, set())
            valid = []
            for group in sorted(groups):
                if not frozen:
                    break
                try:
                    detail = self._bridge("verify-target", "--group", group, "--name", name,
                                          "--statement-hash", frozen)
                    if detail.get("ok") is True:
                        valid.append(detail)
                except BackendError:
                    pass
            if len(valid) == 1:
                out[name] = {"ok": True, "group": valid[0]["group"], "reason": "", **valid[0]}
            else:
                reason = "missing frozen contract" if not frozen else ("unpublished" if not groups else "no unique current verified head")
                out[name] = {"ok": False, "group": None, "reason": reason}
        return {"ok": all(v["ok"] for v in out.values()), "targets": out}

    @staticmethod
    def _attest_stock_build(out: Path, stock_lake: str, mathlib: str | None) -> dict:
        """Keep the real, clean stock build log named by the P2 build receipt."""
        stock_env = {k: v for k, v in os.environ.items()
                     if not k.startswith("PARALEAN_") and k != "LEAN_PATH"}
        stock_env["LEAN_NUM_THREADS"] = "1"
        log_path = out / "build.log"
        started = time.monotonic()
        with log_path.open("wb") as handle:
            proc = subprocess.run([stock_lake, "build"], cwd=out, env=stock_env,
                                  stdout=handle, stderr=subprocess.STDOUT)
        build_ms = round((time.monotonic() - started) * 1000, 3)
        if proc.returncode:
            raise BackendError(f"stock attestation build failed (exit {proc.returncode}); see {log_path}")
        lean_exe = str(Path(stock_lake).with_name("lean"))
        version = subprocess.run([lean_exe, "--githash"], env=stock_env,
                                 text=True, capture_output=True)
        lean_commit = version.stdout.strip()
        if version.returncode or len(lean_commit) != 40 or any(c not in "0123456789abcdef" for c in lean_commit):
            raise BackendError("stock Lean did not report a valid git commit")
        mathlib_commit = ""
        if mathlib:
            revision = subprocess.run(["git", "-C", mathlib, "rev-parse", "HEAD"],
                                      env=stock_env, text=True, capture_output=True)
            if revision.returncode:
                raise BackendError("Mathlib import has no pinned git commit")
            mathlib_commit = revision.stdout.strip()
            if len(mathlib_commit) != 40 or any(c not in "0123456789abcdef" for c in mathlib_commit):
                raise BackendError("Mathlib import has an invalid git commit")
        return {"attestationBuildMs": build_ms,
                "buildLogHash": hashlib.sha256(log_path.read_bytes()).hexdigest(),
                "leanCommit": lean_commit, "mathlibCommit": mathlib_commit}

    def export(self, out: Path) -> dict:
        self._ensure_paths()
        if not self.paths:
            raise BackendError("no workspace available for export")
        required = [t["name"] for t in self.task.get("targets", [])]
        if not self.validate(required)["ok"]:
            raise BackendError("required frozen target contracts are not all verified")
        agent, directory = next(iter(self.paths.items()))
        self.sync(agent, directory)
        stock_lake = self.env.get("PARALEAN_STOCK_LAKE")
        if not stock_lake or not Path(stock_lake).exists():
            raise BackendError("PARALEAN_STOCK_LAKE must name an installed stock Lean lake")
        sources = list(self.task.get("sources", {}).values()) + [
            _read_source(directory / "work", f) or "" for f in self.task.get("files", [])]
        uses_mathlib = any("import Mathlib" in source or "import all Mathlib" in source for source in sources)
        mathlib = self.env.get("PARALEAN_MATHLIB")
        if uses_mathlib and (not mathlib or not Path(mathlib).exists()):
            raise BackendError("task imports Mathlib but PARALEAN_MATHLIB is unavailable")
        result = self._run([self.lean, "ws-export", "--dir", str(directory), "--out", str(out)],
                           env={"PARALEAN_STORE": str(directory / "cache"), "PARALEAN_VISIBILITY": "1",
                                "PARALEAN_LAKE": stock_lake,
                                "PARALEAN_MATHLIB": mathlib if uses_mathlib else None})
        if not result.get("ok"):
            detail = {k: result.get(k) for k in ("build", "diags", "modules", "groups", "identical", "effectOnly") if k in result}
            text = json.dumps(detail, ensure_ascii=False)[:4000]
            for key in ("PARALEAN_S3_SECRET_KEY", "PARALEAN_S3_ACCESS_KEY", "PARALEAN_P5_RECOVERY_SECRET"):
                if self.env.get(key):
                    text = text.replace(self.env[key], "[redacted]")
            log = self.state_dir / "backend.log"
            with log.open("a") as handle:
                handle.write("ws-export reported failure: " + text + "\n")
            log.chmod(0o600)
            raise BackendError(f"stock Lean export or replay verification failed; see {log}")
        result.update(self._attest_stock_build(out, stock_lake, mathlib if uses_mathlib else None))
        if self.conflicts():
            raise BackendError("workspace conflict diagnostics prevent final checkpoint")
        # Ask the same P1 view and closure functions used by ws-export which
        # published packages it built. Cached markers also contain superseded
        # revisions and tombstones; scanning them would attest a different
        # source graph from the stock-built project.
        lean_exe = self.env.get("PARALEAN_P5_LEAN")
        if not lean_exe:
            fork = self.env.get("PARALEAN_FORK_PREFIX")
            lean_exe = str(Path(fork) / "bin" / "lean") if fork else "lean"
        library = self.env.get("PARALEAN_LIB")
        if not library:
            raise BackendError("PARALEAN_LIB is required to select the exact export snapshot")
        path_env = library + (os.pathsep + self.env["LEAN_PATH"] if self.env.get("LEAN_PATH") else "")
        selection = self._run([lean_exe, "--run", str(ROOT / "Snapshot.lean"), "--dir", str(directory)],
                              env={"LEAN_PATH": path_env, "PARALEAN_STORE": str(directory / "cache")})
        rows = selection.get("groups")
        if not isinstance(rows, list) or len(rows) != result.get("groups"):
            raise BackendError("export snapshot selection differs from stock-built group count")
        by_file: dict[str, set[str]] = {}
        seen_groups = set()
        for marker in rows:
            if not isinstance(marker, dict) or not marker.get("current"):
                raise BackendError("export closure contains a noncurrent published group")
            group, file, rids = marker.get("group"), marker.get("file"), marker.get("revisions")
            if (not isinstance(group, str) or len(group) != 64 or
                    any(c not in "0123456789abcdef" for c in group) or group in seen_groups or
                    not isinstance(file, str) or not file or not isinstance(rids, list) or not rids or
                    any(not isinstance(rid, str) or len(rid) != 64 or
                        any(c not in "0123456789abcdef" for c in rid) for rid in rids)):
                raise BackendError("export snapshot selection is malformed or duplicated")
            _source_parts(file)
            seen_groups.add(group)
            by_file.setdefault(file, set()).update(rids)
        revisions = sorted({rid for ids in by_file.values() for rid in ids})
        verified = self.validate(required)
        if not verified["ok"]:
            raise BackendError("required target head changed during stock export")
        hashes = (self.payload or {}).get("contract_hashes", {})
        checkpoint_spec = {
            "revisions": revisions,
            "files": {file: sorted(ids) for file, ids in sorted(by_file.items())},
            "targets": [{"name": name, "group": verified["targets"][name]["group"],
                         "statement_hash": hashes[name]} for name in required],
            "build": {"exporter_bin": "paralean-p1-export",
                      "lean_commit": result["leanCommit"],
                      "mathlib_commit": result["mathlibCommit"],
                      "build_log_hash": result["buildLogHash"]}}
        with tempfile.NamedTemporaryFile(mode="w", dir=self.state_dir, delete=False) as tmp:
            spec_path = Path(tmp.name)
            json.dump(checkpoint_spec, tmp)
        try:
            args = ["checkpoint-targets", "--spec", str(spec_path), "--ws", agent]
            if self.payload and self.payload.get("catalog"):
                args += ["--predecessor", self.payload["catalog"]]
            cp = self._bridge(*args)
        finally:
            spec_path.unlink(missing_ok=True)
        if self.payload is not None:
            data = dict(self.payload)
            data["catalog"] = cp["catalog"]
            data["completion_targets"] = cp["completion_targets"]
            data["export"] = {"output": str(out), "result": result, "checkpoint": cp}
            self._commit(data)
        return {**result, "output": str(out), "checkpoint": cp,
                "metrics": {"transfer_bytes": 0, "transfer_ms": 0,
                            "check_ms": float(result.get("buildMs") or 0) +
                                        float(result.get("attestationBuildMs") or 0)}}

    def conflicts(self) -> list[dict]:
        issues = []
        for agent, directory in self.paths.items():
            log = directory / "diagnostics.log"
            if log.exists():
                for line in log.read_text().splitlines():
                    if "collision" in line.lower() or "conflict" in line.lower():
                        issues.append({"agent": agent, "diagnostic": line[:500]})
        return issues
