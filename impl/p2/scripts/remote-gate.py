#!/usr/bin/env python3
"""Run the unchanged P3 remote gate with a bounded validator readiness wait.

The gate's fixed 1.5-second startup delay can expire while the validator hashes
its checker on a busy shared host. Only that delay is replaced; all scenario
operations, assertions, results and exit status remain owned by gate.py.
"""
import importlib.util
import os
from pathlib import Path
import socket
from subprocess import TimeoutExpired
import sys
import time
from types import SimpleNamespace

if len(sys.argv) != 2:
    raise SystemExit("usage: remote-gate.py RUNDIR (same environment as gate.py)")

address = ("127.0.0.1", int(os.environ.get("PARALEAN_VALIDATOR_PORT", "18591")))
try:
    with socket.create_connection(address, timeout=0.2):
        raise SystemExit(f"validator port already in use: {address}")
except OSError:
    pass


def startup_wait(seconds):
    if seconds != 1.5:
        return time.sleep(seconds)
    deadline = time.monotonic() + 60
    while time.monotonic() < deadline:
        try:
            with socket.create_connection(address, timeout=0.2):
                return
        except OSError:
            time.sleep(0.1)
    raise RuntimeError(f"validator did not listen within 60 seconds: {address}")


path = Path(__file__).resolve().parents[2] / "p3-remote/scripts/gate.py"
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("paralean_remote_gate", path)
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
gate.time = SimpleNamespace(time=time.time, sleep=startup_wait)
original_popen = gate.subprocess.Popen
validators = []


def tracked_popen(command, *args, **kwargs):
    child = original_popen(command, *args, **kwargs)
    if isinstance(command, (list, tuple)) and command[1:2] == ["validator"]:
        validators.append(child)
    return child


gate.subprocess = SimpleNamespace(**vars(gate.subprocess))
gate.subprocess.Popen = tracked_popen
try:
    gate.main()
finally:
    for child in validators:
        if child.poll() is None:
            child.terminate()
        try:
            child.wait(timeout=10)
        except TimeoutExpired:
            child.kill()
            child.wait()
