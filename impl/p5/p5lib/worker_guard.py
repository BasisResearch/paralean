"""Keep a CLI worker's process group tied to the P5 controller on Linux."""

from __future__ import annotations

import ctypes
import os
import signal
import subprocess
import sys


PR_SET_PDEATHSIG = 1
child = None


def terminate(_signum, _frame):
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    if child is not None:
        try:
            os.killpg(os.getpgrp(), signal.SIGTERM)
        except ProcessLookupError:
            pass
    raise SystemExit(143)


def main() -> int:
    global child
    if len(sys.argv) < 2:
        return 2
    parent = int(os.environ.get("PARALEAN_P5_PARENT_PID", str(os.getppid())))
    if os.getppid() != parent:
        return 143
    signal.signal(signal.SIGTERM, terminate)
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(PR_SET_PDEATHSIG, signal.SIGTERM, 0, 0, 0) != 0:
        raise OSError(ctypes.get_errno(), "prctl(PR_SET_PDEATHSIG)")
    if os.getppid() != parent:
        return 143
    child = subprocess.Popen(sys.argv[1:])
    return child.wait()


if __name__ == "__main__":
    raise SystemExit(main())
