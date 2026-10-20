#!/usr/bin/env python3
"""Relay an SSH LSP stream and reap Lean file workers when the stream closes."""

from __future__ import annotations

import os
from pathlib import Path
import signal
import subprocess
import sys
import threading


def descendants(pid: int) -> list[int]:
    try:
        children = [int(item) for item in
                    Path(f"/proc/{pid}/task/{pid}/children").read_text().split()]
    except OSError:
        return []
    return children + [nested for child in children for nested in descendants(child)]


def main(argv: list[str]) -> int:
    if not argv:
        raise SystemExit("remote worker requires an argument-vector Lean command")
    process = subprocess.Popen(argv, stdin=subprocess.PIPE, start_new_session=True)
    stopped = threading.Event()

    def stop(*_):
        if stopped.is_set():
            return
        stopped.set()
        for pid in reversed(descendants(process.pid)) + [process.pid]:
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass

    def copy_input():
        try:
            while chunk := os.read(sys.stdin.fileno(), 65536):
                process.stdin.write(chunk)
                process.stdin.flush()
        except (BrokenPipeError, OSError):
            pass
        finally:
            stop()

    signal.signal(signal.SIGHUP, stop)
    signal.signal(signal.SIGTERM, stop)
    threading.Thread(target=copy_input, daemon=True).start()
    try:
        return process.wait()
    finally:
        stop()


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
