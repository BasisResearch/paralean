#!/usr/bin/env python3
"""Run Lean behind SSH and reap its detached file workers on disconnect."""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import threading


def children(pid):
    try:
        direct = [int(p) for p in Path(f"/proc/{pid}/task/{pid}/children").read_text().split()]
    except OSError:
        return []
    return direct + [descendant for child in direct for descendant in children(child)]


def main():
    config = json.loads(Path(sys.argv[1]).read_text())
    process = subprocess.Popen(config["command"], cwd=config["root"],
                               env=dict(os.environ, **config["env"]),
                               stdin=subprocess.PIPE, start_new_session=True)
    finished = threading.Event()

    def stop(*_):
        for pid in reversed(children(process.pid)) + [process.pid]:
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        finished.set()

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
    sys.exit(main())
