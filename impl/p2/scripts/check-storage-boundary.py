#!/usr/bin/env python3
"""Check this instance's storage boundary without changing any process.

Garage's S3 API must be a Unix socket in an owner-only directory, with no legacy TCP
listener, so the delete- and overwrite-denying gateway is the only S3 ingress. Files
holding deployment secrets (garage.toml: RPC secret and admin token; fdb.cluster:
FoundationDB's only client credential) and their directories must be owner-only.
Garage's admin /metrics endpoint must require the config's bearer `metrics_token`.
"""
import http.client
import os
from pathlib import Path
import socket
import stat
import sys
import tomllib


def private(path: Path, what: str) -> None:
    st = path.stat()
    if st.st_uid != os.getuid() or stat.S_IMODE(st.st_mode) & 0o077:
        raise ValueError(f"{what} {path} must be owned by this user with no group or other access")


def metrics_status(addr: str, token: str | None) -> int:
    host, _, port = addr.rpartition(":")
    conn = http.client.HTTPConnection(host, int(port), timeout=2)
    try:
        conn.request("GET", "/metrics", headers={"Authorization": f"Bearer {token}"} if token else {})
        return conn.getresponse().status
    except (OSError, http.client.HTTPException) as exc:
        raise ValueError(f"Garage admin API {addr} is not answering; restart this instance") from exc
    finally:
        conn.close()


def private_metrics(admin: dict) -> None:
    # Without a metrics token Garage serves /metrics to every local client (W2-40).
    token = admin.get("metrics_token")
    if not isinstance(token, str) or len(token) < 32:
        raise ValueError("Garage config has no [admin] metrics_token; rerun up.sh (bootstrap.sh for the default cluster)")
    addr = admin.get("api_bind_addr")
    if not isinstance(addr, str) or addr.startswith("/") or ":" not in addr:
        raise ValueError("Garage admin API must bind a loopback TCP address")
    if metrics_status(addr, None) not in (401, 403):
        raise ValueError("Garage /metrics answers without its token; restart this instance")
    if metrics_status(addr, token) != 200:
        raise ValueError("Garage /metrics refuses this config's token; restart this instance")


def check(config: Path, old_port: int, cluster: Path | None = None) -> None:
    private(config, "Garage config")
    private(config.parent, "Garage config directory")
    if cluster is not None:
        private(cluster, "FDB cluster file")
        private(cluster.parent, "FDB cluster directory")
    settings = tomllib.loads(config.read_text())
    bind = settings["s3_api"]["api_bind_addr"]
    endpoint = Path(bind)
    if not endpoint.is_absolute():
        raise ValueError("Garage S3 must bind an absolute private Unix socket")
    parent = endpoint.parent.stat()
    if parent.st_uid != os.getuid() or stat.S_IMODE(parent.st_mode) & 0o077:
        raise ValueError("Garage socket parent must be owned by this user and mode 0700")
    if not stat.S_ISSOCK(endpoint.stat().st_mode):
        raise ValueError("Garage S3 Unix socket is not running; restart this instance")
    # A loopback TCP backend is still reachable by any local client with an S3 key.
    try:
        with socket.create_connection(("127.0.0.1", old_port), timeout=0.2):
            pass
    except (ConnectionRefusedError, TimeoutError):
        pass
    else:
        raise ValueError("direct Garage TCP port is reachable; restart this instance")
    private_metrics(settings.get("admin", {}))


if __name__ == "__main__":
    check(Path(sys.argv[1]), int(sys.argv[2]), Path(sys.argv[3]) if len(sys.argv) > 3 else None)
