"""Prepare P5 working copies for P4 LSP, locally or over pinned SSH."""

from __future__ import annotations

from dataclasses import dataclass
from dataclasses import field
import hashlib
import json
from pathlib import Path
import re
import shlex
import subprocess
import tempfile


@dataclass(frozen=True)
class SshEndpoint:
    host: str
    user: str
    port: int
    identity_file: Path
    known_hosts: Path
    root: Path
    runtime_env: dict[str, str] = field(default_factory=dict)

    def __post_init__(self):
        if not self.host or not self.user or self.port < 1 or self.port > 65535:
            raise ValueError("SSH host, user and valid port are required")
        if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]*", self.host) or not re.fullmatch(
                r"[A-Za-z0-9][A-Za-z0-9._-]*", self.user):
            raise ValueError("SSH host and user contain unsafe characters")
        if not self.root.is_absolute() or str(self.root) in ("/", "/tmp"):
            raise ValueError("SSH worker root must be a dedicated absolute directory")
        if not re.fullmatch(r"/[A-Za-z0-9._/-]+", str(self.root)) or ".." in self.root.parts:
            raise ValueError("SSH worker root contains unsafe characters")
        if not self.identity_file.is_file() or not self.known_hosts.is_file():
            raise ValueError("SSH identity and pinned known_hosts files must exist")
        allowed = {"LEAN_PARALEAN", "LEAN_PATH", "PARALEAN_BIN", "PARALEAN_SYSROOT", "PATH",
                   "PARALEAN_DEPLOYMENT", "PARALEAN_FDB_CLUSTER", "PARALEAN_S3_ENDPOINT",
                   "PARALEAN_S3_BUCKET", "PARALEAN_S3_REGION", "PARALEAN_PLR",
                   "LD_LIBRARY_PATH", "AWS_ACCESS_KEY_ID", "AWS_SECRET_ACCESS_KEY",
                   "AWS_SESSION_TOKEN", "PARALEAN_S3_ACCESS_KEY", "PARALEAN_S3_SECRET_KEY"}
        if set(self.runtime_env) - allowed or any(not isinstance(v, str) or not v or "\0" in v
                                                  for v in self.runtime_env.values()):
            raise ValueError("SSH runtime environment contains unsupported settings")

    def ownership_marker(self, local: Path) -> str:
        material = f"{local.resolve()}\0{self.user}@{self.host}:{self.root}".encode()
        return "paralean-lsp-v1-" + hashlib.sha256(material).hexdigest()

    @property
    def ssh(self) -> list[str]:
        return ["ssh", "-p", str(self.port), "-i", str(self.identity_file.resolve()),
                "-o", f"UserKnownHostsFile={self.known_hosts.resolve()}",
                "-o", "StrictHostKeyChecking=yes", "-o", "BatchMode=yes",
                f"{self.user}@{self.host}"]


def provision_ssh_copy(local: Path, endpoint: SshEndpoint, *, run=subprocess.run) -> None:
    """Copy only source, cache and worker credentials into a dedicated remote root."""
    local = local.resolve()
    if not (local / "work").is_dir() or not (local / "cache").is_dir():
        raise ValueError("local P5 workspace must contain work and cache directories")
    root = str(endpoint.root)
    marker = endpoint.ownership_marker(local)
    marker_file = root + "/.paralean-lsp-owned"
    # A pre-existing directory is writable only if it carries this copy's
    # marker. This bounds rsync --delete to a root provisioned by this caller.
    script = (f"if test -e {shlex.quote(root)}; then "
              f"test -f {shlex.quote(marker_file)} && "
              f"test \"$(cat {shlex.quote(marker_file)})\" = {shlex.quote(marker)}; "
              f"else mkdir -p {shlex.quote(root)} && "
              f"printf %s {shlex.quote(marker)} > {shlex.quote(marker_file)}; fi && "
              f"mkdir -p {shlex.quote(root + '/work')} {shlex.quote(root + '/cache')}")
    run(endpoint.ssh + [script],
        check=True, capture_output=True, stdin=subprocess.DEVNULL)
    transport = shlex.join(endpoint.ssh[:-1])
    for name in ("work", "cache"):
        run(["rsync", "-a", "--delete", "-e", transport,
             str(local / name) + "/", f"{endpoint.user}@{endpoint.host}:{root}/{name}/"],
            check=True, capture_output=True, stdin=subprocess.DEVNULL)
    for name in ("keys.json", "trust.json"):
        source = local / name
        if source.is_file():
            run(["rsync", "-a", "-e", transport, str(source),
                 f"{endpoint.user}@{endpoint.host}:{root}/{name}"],
                check=True, capture_output=True, stdin=subprocess.DEVNULL)
    wrapper = Path(__file__).with_name("remote_worker.py")
    run(["rsync", "-a", "--chmod=F700", "-e", transport, str(wrapper),
         f"{endpoint.user}@{endpoint.host}:{root}/.paralean-remote-worker.py"],
        check=True, capture_output=True, stdin=subprocess.DEVNULL)
    runtime = {**endpoint.runtime_env,
               "PARALEAN_STORE": root + "/cache",
               "PARALEAN_WORK_ROOT": root + "/work",
               "PARALEAN_VISIBILITY": "1", "LEAN_PARALEAN": "1"}
    if (local / "keys.json").is_file():
        runtime["PARALEAN_KEYS"] = root + "/keys.json"
    if (local / "trust.json").is_file():
        runtime["PARALEAN_TRUST"] = root + "/trust.json"
    with tempfile.NamedTemporaryFile(mode="w", dir=local, prefix=".lsp-env-", delete=False) as handle:
        env_file = Path(handle.name)
        handle.write("\n".join("export " + key + "=" + shlex.quote(value)
                               for key, value in sorted(runtime.items())) + "\n")
    try:
        env_file.chmod(0o600)
        run(["rsync", "-a", "--chmod=F600", "-e", transport, str(env_file),
             f"{endpoint.user}@{endpoint.host}:{root}/.lsp-env"],
            check=True, capture_output=True, stdin=subprocess.DEVNULL)
    finally:
        env_file.unlink(missing_ok=True)


def lsp_workspace_args(name: str, local: Path, lean_argv: list[str],
                       endpoint: SshEndpoint | None = None) -> list[str]:
    """Arguments for P4 lsp.py after the P5 backend provisioned ``local``."""
    local = local.resolve()
    if not name or "=" in name or not local.is_dir():
        raise ValueError("workspace name and provisioned local root are required")
    if not lean_argv or any(not isinstance(part, str) or not part for part in lean_argv):
        raise ValueError("Lean server command must be an argument vector")
    args = ["--workspace", f"{name}={local}"]
    if endpoint is None:
        args += ["--worker-root", f"{name}={local}",
                 "--worker-command", f"{name}={json.dumps(lean_argv)}"]
    else:
        root = str(endpoint.root)
        command = ("cd " + shlex.quote(root) + " && . ./.lsp-env && exec python3 "
                   "./.paralean-remote-worker.py " + shlex.join(lean_argv))
        args += ["--worker-root", f"{name}={endpoint.root}",
                 "--worker-command", f"{name}={json.dumps(endpoint.ssh + [command])}"]
    return args
