#!/usr/bin/env python3
"""Check this instance's Garage S3 boundary without changing any process."""
import os
from pathlib import Path
import socket
import stat
import sys
import tomllib


def check(config: Path, old_port: int) -> None:
    bind = tomllib.loads(config.read_text())["s3_api"]["api_bind_addr"]
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
        return
    raise ValueError("direct Garage TCP port is reachable; restart this instance")


if __name__ == "__main__":
    check(Path(sys.argv[1]), int(sys.argv[2]))
