#!/usr/bin/env python3
"""One-target live crash-window regression on an already running, private P5 cluster.

Run with impl/p5/scripts/env.sh sourced.
This script starts no storage service and no coding worker. It publishes a known valid
proof through P3/P2, deliberately leaves P5's journal at 'running', deletes the
entire desktop, and requires recovery to adopt the old immutable group. It also
forces a guarded-fence head mismatch and checks historical receipt rejection.
"""
from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path
from unittest.mock import patch

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("run_dir", type=Path)
    ap.add_argument("--repo", type=Path, default=Path.cwd())
    args = ap.parse_args()
    repo = args.repo.resolve()
    sys.path.insert(0, str(repo / "impl/p5"))
    from p5lib.backend import Backend
    from p5lib.controller import Controller
    from p5lib.task import from_dict, from_saved

    if not os.environ.get("PARALEAN_INSTANCE", "").startswith("p5-"):
        ap.error("source the P5 environment with a private p5-* PARALEAN_INSTANCE")
    if not os.environ.get("PARALEAN_P5_RECOVERY_SECRET"):
        ap.error("store-only recovery secret is required")
    subprocess.run(["df", "-h", "/data"], check=True)
    run_dir = args.run_dir.resolve()
    run_dir.mkdir(parents=True, exist_ok=True)
    desktop = run_dir / "desktop"
    if desktop.exists():
        ap.error("run directory must have no preexisting desktop")
    deployment = f"p5recovery-{int(time.time())}-{os.getpid()}"
    env = {**os.environ, "PARALEAN_DEPLOYMENT": deployment}
    name = "P5Recovery.target"
    raw = {"task": {"id": deployment, "name": "P5 recovery fault"},
           "controller": {"workers": 1, "max_attempts": 2},
           "worker": {"kind": "command", "command": ["python3", "-c", "raise SystemExit(99)"]},
           "targets": [{"name": name, "statement": "True", "file": "Target.lean", "deps": []}]}
    task = from_dict(raw)
    backend = Backend(task.as_dict() | {"agents": ["w0"]}, desktop, env=env)
    backend.setup()
    workspace = desktop / "w0"
    backend.provision("w0", workspace)
    backend.sync("w0", workspace)
    epoch = backend.assign_target(name, "w0")
    before = backend.observe_target(name, "w0")
    if before["epoch"] != epoch or before["head"] is not None:
        raise AssertionError("fresh target assignment has an unexpected head")
    state = Controller(task, desktop, backend, workers=1)._new_state()
    state["targets"][name].update(status="running", agent="w0", epoch=epoch,
                                  epoch_ready=False, attempts=1,
                                  dispatch_head=before["head"],
                                  fence_request="planned-fence-before-lost-call",
                                  fence_expected_epoch=epoch,
                                  fence_expected_head=before["head"])
    backend.save_state(state)  # last P5 acknowledgement before T1
    (workspace / "work/Target.lean").write_text(
        f"theorem {name} : True := by\n  trivial\n")
    publication = backend.publish("w0", workspace, "Target.lean", [name], epoch=epoch)
    group = publication["groups"][-1]
    verdict = backend.validate([name])
    if not verdict["ok"] or verdict["targets"][name]["group"] != group:
        raise AssertionError("valid P2 publication was not accepted")
    journal = backend.load_state()
    if journal["targets"][name]["status"] != "running" or journal["targets"][name]["group"]:
        raise AssertionError("test failed to leave P5 journal behind P2 publication")
    race = backend.fence_unfinished(name, "w0", epoch, before["head"], "recovery-fault-race")
    if race.get("outcome") != "changed" or race.get("epoch") != epoch or race.get("head") != verdict["targets"][name]["head"]:
        raise AssertionError("guarded fence accepted a stale observed head")
    del backend, task
    shutil.rmtree(desktop)
    if desktop.exists():
        raise AssertionError("desktop deletion failed")
    tasks = Backend.list_tasks(env)
    found = [row.get("task") for row in tasks if row.get("task") == deployment]
    if found != [deployment]:
        raise AssertionError("task ID not discoverable from store")
    recovered = Backend.recover_task(found[0], desktop, env)
    recovered_task = from_saved(recovered.task)
    with patch("p5lib.controller.run_worker", side_effect=AssertionError("new proof forbidden")):
        result = Controller(recovered_task, desktop, recovered, workers=1).run(recover=True, export=True)
        if result["targets"][name].get("fence_request"):
            raise AssertionError("adopted publication retained obsolete fence intent")
        again = Controller(recovered_task, desktop, recovered, workers=1).run(recover=True, export=True)
        if again["phase"] != "complete":
            raise AssertionError("completed recovery lost the adopted publication")
    if result["phase"] != "complete" or result["targets"][name]["group"] != group:
        raise AssertionError("store recovery did not adopt original group and complete")
    if result["targets"][name]["attempts"] != 1:
        raise AssertionError("recovery launched another proof attempt")
    new_epoch = recovered.assign_target(name, "w0")
    historical = recovered.validate([name])
    if new_epoch <= epoch or historical["ok"]:
        raise AssertionError("old epoch's historical receipt validated as current")
    # Discard a successful fence response, then repeat its request as a caller
    # would after a connection loss. The request index must prevent a second T4.
    pending = "P5Recovery.unfinished"
    assigned = recovered._bridge("assign-target", "--name", pending, "--ws", "w0",
                                 "--request", "unfinished-initial")
    fence_args = ("fence-unfinished", "--name", pending, "--ws", "w0",
                  "--expected-epoch", str(assigned["epoch"]),
                  "--expected-head", "none", "--request", "unfinished-stable-fence")
    recovered._bridge(*fence_args)
    retried = recovered._bridge(*fence_args)
    if retried["outcome"] != "fenced" or retried["epoch"] != assigned["epoch"] + 1:
        raise AssertionError("guarded fence retry advanced its epoch twice")
    evidence = {"deployment": deployment, "group": group, "original_epoch": epoch,
                "new_epoch": new_epoch, "fence_outcome": race["outcome"],
                "recovered_phase": result["phase"], "attempts": result["targets"][name]["attempts"],
                "historical_receipt_rejected": not historical["ok"],
                "stock_export_ok": bool((result.get("export") or {}).get("ok")),
                "pending_fence_cleared": not result["targets"][name].get("fence_request"),
                "completed_recovery_ok": again["phase"] == "complete",
                "fence_retry_epoch": retried["epoch"],
                "git": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()}
    (run_dir / "recovery-fault.json").write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")
    print(json.dumps(evidence, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
