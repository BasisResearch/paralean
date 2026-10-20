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
    # Unwind any interrupted Popen.wait before waiting again: that wait holds
    # an internal lock and is not safe to reenter from a signal handler.
    raise SystemExit(143)


def cleanup_group():
    if child is None:
        return
    group = os.getpgrp()
    try:
        os.killpg(group, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        child.wait(timeout=5)
    except subprocess.TimeoutExpired:
        pass
    # The CLI leader may have exited while its descendants ignore TERM. This
    # guard owns the process group and may itself be killed by the final KILL.
    try:
        os.killpg(group, signal.SIGKILL)
    except ProcessLookupError:
        pass


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
    try:
        # If the controller dies while Popen is creating the CLI, deliver its
        # death signal only after `child` records the process to clean up.
        previous_mask = signal.pthread_sigmask(signal.SIG_BLOCK, {signal.SIGTERM})
        try:
            # Popen/exec inherits the parent's blocked signal mask. This guard
            # is single-threaded, so preexec_fn can safely restore the CLI's
            # original mask without risking a forked thread holding a lock.
            def restore_child_mask():
                signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)

            child = subprocess.Popen(sys.argv[1:], preexec_fn=restore_child_mask)
        finally:
            signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)
        return child.wait()
    except SystemExit:
        cleanup_group()
        raise


if __name__ == "__main__":
    raise SystemExit(main())
