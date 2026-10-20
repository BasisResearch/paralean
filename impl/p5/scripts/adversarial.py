#!/usr/bin/env python3
"""Live P5 negative checks against one private P2/P3 deployment.

The caller starts and owns the PARALEAN_INSTANCE cluster. This script creates a
fresh deployment, starts no storage service, and uses no coding-agent process.
It writes adversarial.json in RUN_DIR and returns nonzero on any failed check.
"""

from __future__ import annotations

import argparse
import copy
import json
import os
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "impl/p5"))

from p5lib.backend import Backend, BackendError
from p5lib.controller import Controller
from p5lib.task import from_dict


def rejected(action) -> tuple[bool, str]:
    try:
        action()
    except (ValueError, RuntimeError, BackendError) as exc:
        return True, str(exc)
    return False, "unexpected acceptance"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("run_dir", type=Path)
    a = ap.parse_args()
    if not os.environ.get("PARALEAN_INSTANCE"):
        ap.error("PARALEAN_INSTANCE must identify this run's private cluster")
    run_dir = a.run_dir.resolve()
    run_dir.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env["PARALEAN_DEPLOYMENT"] = f"p5negative-{int(time.time())}-{os.getpid()}"
    name = "P5Adversarial.target"
    raw = {"task": {"id": env["PARALEAN_DEPLOYMENT"], "name": "P5 live negative checks"},
           "controller": {"workers": 1, "max_attempts": 2},
           "worker": {"kind": "codex"},
           "targets": [{"name": name, "statement": "True", "file": "Target.lean", "deps": []}]}
    checks = {}
    result = {"deployment": env["PARALEAN_DEPLOYMENT"], "checks": checks}
    try:
        cycle = json.loads(json.dumps(raw))
        cycle["targets"][0]["deps"] = [name]
        ok, reason = rejected(lambda: from_dict(cycle))
        checks["invalid_task_dag"] = {"ok": ok, "reason": reason}

        task = from_dict(raw)
        state_dir = run_dir / "desktop"
        backend = Backend(task.as_dict() | {"agents": ["w0"]}, state_dir, env=env)
        backend.setup()
        workspace = state_dir / "w0"
        backend.provision("w0", workspace)
        backend.sync("w0", workspace)
        controller = Controller(task, state_dir, backend, workers=1, parallelism=1)
        backend.save_state(controller._new_state())
        ok, reason = rejected(lambda: controller.export(state_dir / "premature-export"))
        checks["missing_target_blocks_completion"] = {"ok": ok and "incomplete" in reason, "reason": reason}

        source = workspace / "work/Target.lean"
        source.write_text(f"theorem {name} : True ∧ True := by exact ⟨trivial, trivial⟩\n")
        stale_epoch = backend.assign_target(name, "w0")
        ok, reason = rejected(lambda: backend.publish("w0", workspace, "Target.lean", [name], epoch=stale_epoch))
        not_published = not backend.validate([name])["ok"]
        checks["changed_statement_rejected"] = {"ok": ok and not_published,
                                                  "reason": reason, "unpublished": not_published}

        source.write_text(f"theorem {name} : True := by trivial\n")
        fresh_epoch = backend.assign_target(name, "w0")
        ok, reason = rejected(lambda: backend.publish("w0", workspace, "Target.lean", [name], epoch=stale_epoch))
        checks["stale_dispatch_epoch_rejected"] = {"ok": ok and fresh_epoch > stale_epoch,
                                                    "reason": reason, "old": stale_epoch, "new": fresh_epoch}
        published = backend.publish("w0", workspace, "Target.lean", [name], epoch=fresh_epoch)
        verdict = backend.validate([name])
        checks["fresh_epoch_accepted"] = {"ok": verdict.get("ok") is True and bool(published.get("groups")),
                                          "validation": verdict}

        # A second desktop has read the old journal sequence. Its write must not
        # silently overwrite a newer controller snapshot.
        other = Backend(task.as_dict() | {"agents": ["w0"]}, state_dir, env=env)
        old = other.load_state()
        backend.save_state({"phase": "newer", "targets": {name: {"status": "done"}}})
        ok, reason = rejected(lambda: other.save_state(old))
        checks["stale_journal_cas_rejected"] = {"ok": ok, "reason": reason}

        # A stock build alone is not enough for a completion record: its P2
        # snapshot and build receipt must carry the fixed target binding.
        exported = backend.export(state_dir / "checkpoint-export")
        checkpoint = exported.get("checkpoint") or {}
        bindings = checkpoint.get("completion_targets") or []
        snapshot_targets = checkpoint.get("snapshot_targets") or []
        target_checks = checkpoint.get("build_receipt_target_checks") or []
        binding = next((x for x in bindings if x.get("name") == name), None)
        snapshot_target = next((x for x in snapshot_targets if x.get("name") == name), None)
        target_check = next((x for x in target_checks if x.get("group") == verdict["targets"][name]["group"]), None)
        checks["checkpoint_binds_required_target"] = {
            "ok": exported.get("ok") is True and bool(checkpoint.get("snapshot"))
                  and len(bindings) == 1 and bool(binding) and len(snapshot_targets) == 1
                  and bool(snapshot_target) and len(target_checks) == 1
                  and bool(target_check) and target_check.get("statement_matches") is True
                  and target_check.get("group") == binding.get("group")
                  and snapshot_target.get("owner") == binding.get("owner")
                  and snapshot_target.get("epoch") == binding.get("epoch")
                  and bool(snapshot_target.get("signature"))
                  and binding.get("epoch") == fresh_epoch,
            "snapshot": checkpoint.get("snapshot"), "binding": binding,
            "snapshot_target": snapshot_target, "target_check": target_check,
        }

        clean = controller._new_state()
        clean["phase"] = "complete"
        clean["targets"][name].update(status="done", agent="w0", epoch=fresh_epoch,
                                       group=verdict["targets"][name]["group"])
        clean["contract_validation"] = verdict
        clean["export"] = exported
        backend.save_state(clean)
        stored_clean = Backend(task.as_dict() | {"agents": ["w0"]}, state_dir, env=env).load_state()
        durable_bindings = (backend.payload or {}).get("completion_targets")
        checks["current_completion_accepted"] = {
            "ok": stored_clean is not None and stored_clean.get("phase") == "complete"
                  and bool(binding) and stored_clean.get("targets", {}).get(name, {}).get("group") == binding.get("group")
                  and durable_bindings == bindings,
        }

        # Leave a noncomplete durable state before fencing the old completion.
        # The failed stale write must not restore the old complete state.
        running = copy.deepcopy(clean)
        running["phase"] = "running"
        backend.save_state(running)

        request = f"adversarial-idempotent-{os.getpid()}"
        first = backend._bridge("assign-target", "--name", name, "--ws", "w0", "--request", request)
        second = backend._bridge("assign-target", "--name", name, "--ws", "w0", "--request", request)
        checks["assignment_retry_idempotent"] = {"ok": first == second, "first": first, "second": second}
        ok, reason = rejected(lambda: backend.save_state(clean))
        stored_after_reject = Backend(task.as_dict() | {"agents": ["w0"]}, state_dir, env=env).load_state()
        checks["stale_completion_epoch_rejected"] = {
            "ok": ok and int(first.get("epoch", 0)) > fresh_epoch
                  and stored_after_reject is not None and stored_after_reject.get("phase") != "complete",
            "reason": reason,
            "stored_phase": stored_after_reject.get("phase") if stored_after_reject else None,
        }
    except Exception as exc:
        result["error"] = f"{type(exc).__name__}: {exc}"
    result["ok"] = "error" not in result and all(c["ok"] for c in checks.values())
    (run_dir / "adversarial.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"ok": result["ok"], "checks": checks, "error": result.get("error")}, indent=2))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
