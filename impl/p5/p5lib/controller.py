"""Small scheduling layer over the P3/P2 backend. Task graph stays private."""

from __future__ import annotations

import json
import os
import time
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from pathlib import Path

from .task import Task
from .workers import run as run_worker


class Controller:
    def __init__(self, task: Task, state_dir: Path, backend=None, workers: int | None = None,
                 parallelism: int | None = None):
        self.task = task
        self.state_dir = state_dir.resolve()
        self.state_dir.mkdir(parents=True, exist_ok=True)
        self.worker_count = workers or task.workers
        # The shared development box also runs the store and validator processes.
        self.parallelism = min(parallelism or 4, self.worker_count)
        if self.worker_count < 1 or self.parallelism < 1:
            raise ValueError("worker count and parallelism must be positive")
        self.agents = [f"w{i}" for i in range(self.worker_count)]
        if any(t.owner and t.owner not in self.agents for t in task.targets):
            raise ValueError("target owner must be one of the configured workers")
        self.task_data = task.as_dict() | {"agents": self.agents}
        if backend is None:
            from .backend import Backend
            backend = Backend(self.task_data, self.state_dir)
        self.backend = backend
        self.state: dict | None = None

    def _new_state(self) -> dict:
        return {"task_id": self.task.id, "fingerprint": self.task.fingerprint,
                "worker_kind": self.task.worker_kind, "worker_command": list(self.task.worker_command),
                "logical_workers": self.worker_count, "parallelism": self.parallelism,
                "workspace_root": str(self.state_dir),
                "phase": "running", "targets": {
                    t.name: {"status": "pending", "attempts": 0, "agent": t.owner,
                             "group": None, "error": None, "worker": None} for t in self.task.targets},
                "events": [], "metrics": {"started_at": time.time(), "wall_s": 0,
                    "worker_wall_s": 0, "transfer_bytes": 0, "transfer_ms": 0, "check_ms": 0},
                "export": None, "contract_validation": None, "catalog": None}

    def _save(self, event: str, **details) -> None:
        assert self.state is not None
        self.state["events"].append({"at": time.time(), "event": event, **details})
        self.state["metrics"]["wall_s"] = round(time.time() - self.state["metrics"]["started_at"], 3)
        # The backend first persists the full state and workspace sources in P2's store.
        catalog = self.backend.save_state(self.state)
        self.state["catalog"] = catalog
        path = self.state_dir / "run.json"
        tmp = path.with_suffix(".json.tmp")
        tmp.write_text(json.dumps(self.state, indent=2, sort_keys=True) + "\n")
        os.replace(tmp, path)

    def _open(self, *, recover: bool) -> None:
        self.backend.setup()
        state = self.backend.load_state()
        stale = []
        if state is None:
            if recover:
                raise RuntimeError(f"no durable task record for {self.task.id}")
            self.state = self._new_state()
            self._save("task_created")
        else:
            if state.get("fingerprint") != self.task.fingerprint:
                raise RuntimeError("task contract differs from the frozen store record")
            self.state = state
            for name, entry in state["targets"].items():
                if entry["status"] == "running":
                    stale.append((name, entry["agent"]))
                    entry["status"] = "pending"
                    entry["epoch_ready"] = False
                elif entry["status"] != "done" and entry.get("fence_request"):
                    entry["status"] = "pending"
        for agent in self.agents:
            self.backend.provision(agent, self.state_dir / agent)
        for name, entry in self.state["targets"].items():
            if entry["status"] == "failed" and self._reconcile_published(name, entry):
                self._save("late_publication_recovered", target=name, group=entry["group"])
        if state is not None:
            self._save("recovered" if recover else "resumed", pending_reconciliation=[x[0] for x in stale])
        self._save("workspaces_ready", agents=self.agents)

    def _reconcile_published(self, name: str, entry: dict) -> bool:
        """Adopt a P2 publication lost before its P5 journal acknowledgement.

        verify-target rejects receipts for an old owner or epoch. If this returns
        false, _prepare_assignment compares the original dispatch head atomically
        before fencing; a concurrent publication therefore cannot be stranded.
        """
        if not entry.get("agent") or not isinstance(entry.get("epoch"), int):
            return False
        observed = self.backend.observe_target(name, entry["agent"])
        if (not observed.get("assigned_to_agent") or observed.get("epoch") != entry["epoch"]):
            return False
        # A failed pull or validator lookup is not evidence that no publication
        # committed. Propagate the error rather than fencing that proof.
        self._record_costs(self.backend.sync(entry["agent"], self.state_dir / entry["agent"]))
        verdict = self.backend.validate([name])
        self._record_costs(verdict)
        detail = verdict.get("targets", {}).get(name, {})
        if not (verdict.get("ok") and detail.get("ok") and detail.get("group")
                and detail.get("epoch") == entry["epoch"]):
            return False
        entry["group"] = detail["group"]
        entry["status"] = "done"
        entry["error"] = None
        entry["epoch_ready"] = False
        for key in ("fence_request", "fence_expected_epoch", "fence_expected_head"):
            entry.pop(key, None)
        return True

    def _prepare_assignment(self, name: str, entry: dict, agent: str) -> bool:
        """Return true when a worker may start, false when an old proof was adopted."""
        entry["agent"] = agent
        if self._reconcile_published(name, entry):
            self._save("published_target_recovered", target=name, group=entry["group"])
            return False
        if entry.get("epoch_ready"):
            current = self.backend.observe_target(name, agent)
            if current.get("epoch") != entry.get("epoch") or not current.get("assigned_to_agent"):
                raise RuntimeError("journaled assignment changed before dispatch")
            if current.get("head") != entry.get("dispatch_head"):
                raise RuntimeError("target head changed before dispatch without valid reconciliation")
            return True
        if not isinstance(entry.get("epoch"), int):
            entry["epoch"] = self.backend.assign_target(name, agent)
            current = self.backend.observe_target(name, agent)
            if current.get("epoch") != entry["epoch"] or not current.get("assigned_to_agent"):
                raise RuntimeError("initial target assignment changed before dispatch")
            entry["dispatch_head"] = current.get("head")
            entry["epoch_ready"] = True
            self._save("target_assignment_ready", target=name, epoch=entry["epoch"])
            return True
        for _ in range(8):
            if self._reconcile_published(name, entry):
                self._save("published_target_recovered", target=name, group=entry["group"])
                return False
            if not entry.get("fence_request"):
                observed = self.backend.observe_target(name, agent)
                if (observed.get("epoch") != entry["epoch"] or
                        not observed.get("assigned_to_agent")):
                    raise RuntimeError("target assignment changed outside the controller")
                if "dispatch_head" not in entry:
                    if observed.get("head") is not None:
                        raise RuntimeError("cannot fence a legacy dispatch with an unverified target head")
                    entry["dispatch_head"] = None
                if observed.get("head") != entry["dispatch_head"]:
                    raise RuntimeError("target head changed without valid reconciliation")
                entry["fence_request"] = os.urandom(16).hex()
                entry["fence_expected_epoch"] = entry["epoch"]
                entry["fence_expected_head"] = entry["dispatch_head"]
                # The request is durable before the potentially ambiguous T4 commit.
                self._save("fence_planned", target=name, epoch=entry["epoch"],
                           head=observed.get("head"))
            result = self.backend.fence_unfinished(
                name, agent, entry["fence_expected_epoch"],
                entry["fence_expected_head"], entry["fence_request"])
            if result.get("outcome") == "fenced":
                entry["epoch"] = int(result["epoch"])
                entry["dispatch_head"] = result.get("head")
                entry["epoch_ready"] = True
                for key in ("fence_request", "fence_expected_epoch", "fence_expected_head"):
                    entry.pop(key, None)
                self._save("target_fenced", target=name, epoch=entry["epoch"])
                current = self.backend.observe_target(name, agent)
                if (current.get("epoch") != entry["epoch"] or
                        not current.get("assigned_to_agent") or
                        current.get("head") != entry["dispatch_head"]):
                    entry["epoch_ready"] = False
                    self._save("fenced_assignment_changed", target=name)
                    continue
                return True
            if result.get("outcome") != "changed":
                raise RuntimeError("guarded fence returned an unknown outcome")
            for key in ("fence_request", "fence_expected_epoch", "fence_expected_head"):
                entry.pop(key, None)
            self._save("fence_observation_changed", target=name)
        raise RuntimeError("target head kept changing during reconciliation")

    def _owner(self, target) -> str:
        if target.owner:
            return target.owner
        # A stable assignment survives process loss; workspaces remain private.
        index = list(self.task.targets).index(target) % self.worker_count
        return self.agents[index]

    def _record_costs(self, result: dict) -> None:
        if not isinstance(result, dict):
            return
        details = result.get("metrics", result)
        if not isinstance(details, dict):
            details = result
        for key in ("transfer_bytes", "transfer_ms", "check_ms"):
            val = details.get(key, 0)
            if isinstance(val, (int, float)):
                self.state["metrics"][key] = self.state["metrics"].get(key, 0) + val

    def _finish_worker(self, target, agent: str, outcome) -> None:
        entry = self.state["targets"][target.name]
        self.state["metrics"]["worker_wall_s"] += outcome.wall_s
        entry["worker"] = outcome.as_dict()
        if outcome.returncode:
            entry["error"] = f"worker exited {outcome.returncode}; see {outcome.log}"
            entry["status"] = "failed" if entry["attempts"] >= self.task.max_attempts else "pending"
            entry["epoch_ready"] = False
            self._save("worker_failed", target=target.name, agent=agent,
                       attempt=outcome.attempt, returncode=outcome.returncode,
                       timed_out=outcome.timed_out)
            return
        try:
            published = self.backend.publish(agent, self.state_dir / agent, target.file,
                                             [target.name], epoch=entry["epoch"])
            self._record_costs(published)
            verdict = self.backend.validate([target.name])
            self._record_costs(verdict)
            if not verdict.get("ok"):
                raise RuntimeError(f"frozen target contract is not validated: {target.name}")
            target_verdict = verdict.get("targets", {}).get(target.name, {})
            entry["group"] = target_verdict.get("group") or published.get("group")
            entry["status"] = "done"
            entry["epoch_ready"] = False
            entry["error"] = None
            self._save("target_validated", target=target.name, agent=agent,
                       group=entry["group"], attempt=outcome.attempt)
        except Exception as exc:
            if self._reconcile_published(target.name, entry):
                self._save("publication_reply_recovered", target=target.name, agent=agent,
                           group=entry["group"], attempt=outcome.attempt)
                return
            diagnostics = self.backend.conflicts()
            detail = "; ".join(x.get("diagnostic", "") for x in diagnostics[:3])
            entry["error"] = f"{exc}; conflicts: {detail}" if detail else str(exc)
            entry["status"] = "failed" if entry["attempts"] >= self.task.max_attempts else "pending"
            entry["epoch_ready"] = False
            self._save("publication_failed", target=target.name, agent=agent,
                       attempt=outcome.attempt, reason=entry["error"])

    def run(self, *, recover: bool = False, export: bool = True) -> dict:
        self._open(recover=recover)
        if self.state["phase"] == "complete":
            required = [target.name for target in self.task.targets]

            def verify_heads() -> bool:
                verdict = self.backend.validate(required)
                self._record_costs(verdict)
                self.state["contract_validation"] = verdict
                details = verdict.get("targets", {})
                return bool(verdict.get("ok")) and all(
                    self.state["targets"].get(name, {}).get("status") == "done"
                    and self.state["targets"][name].get("group")
                    and details.get(name, {}).get("ok")
                    and details[name].get("group") == self.state["targets"][name]["group"]
                    for name in required
                )

            try:
                if not verify_heads():
                    raise RuntimeError("a completed target no longer matches its current validated head")
                if export:
                    # An existing directory is not evidence of a stock build. Rebuild it
                    # from the current store projection and check the heads again afterward.
                    out = self.state_dir / "export"
                    exported = self.backend.export(out)
                    self._record_costs(exported)
                    if not exported.get("ok"):
                        raise RuntimeError("stock export failed during recovery")
                    self.state["export"] = exported
                    if not verify_heads():
                        raise RuntimeError("a target head changed during stock export")
            except Exception as exc:
                self.state["phase"] = "failed"
                self.state["error"] = str(exc)
                self._save("completed_run_reverification_failed", reason=str(exc))
                return self.state
            self.state.pop("error", None)
            self._save("completed_run_reverified", export=export)
            return self.state
        targets = {t.name: t for t in self.task.targets}
        running = {}
        busy_agents = set()
        with ThreadPoolExecutor(max_workers=self.parallelism) as pool:
            while True:
                statuses = self.state["targets"]
                if all(e["status"] == "done" for e in statuses.values()):
                    break
                scheduled = False
                for target in self.task.targets:
                    entry = statuses[target.name]
                    agent = self._owner(target)
                    if len(running) >= self.parallelism:
                        break
                    if entry["status"] != "pending" or agent in busy_agents:
                        continue
                    if any(statuses[d]["status"] != "done" for d in target.deps):
                        continue
                    try:
                        sync = self.backend.sync(agent, self.state_dir / agent)
                        self._record_costs(sync)
                        if not self._prepare_assignment(target.name, entry, agent):
                            scheduled = True
                            continue
                    except Exception as exc:
                        if isinstance(entry.get("epoch"), int) and not entry.get("epoch_ready"):
                            # A published head may exist but be temporarily unreadable.
                            # Preserve the old dispatch and stable fence request for a
                            # later recovery instead of exhausting worker attempts.
                            entry["error"] = f"reconciliation deferred: {exc}"
                            self._save("reconciliation_deferred", target=target.name,
                                       agent=agent, reason=str(exc))
                            raise
                        entry["attempts"] += 1
                        entry["error"] = f"sync: {exc}"
                        entry["status"] = "failed" if entry["attempts"] >= self.task.max_attempts else "pending"
                        self._save("sync_failed", target=target.name, agent=agent, reason=str(exc))
                        scheduled = True
                        continue
                    entry["status"] = "running"
                    entry["epoch_ready"] = False
                    entry["agent"] = agent
                    entry["attempts"] += 1
                    self._save("target_dispatched", target=target.name, agent=agent,
                               attempt=entry["attempts"])
                    fut = pool.submit(run_worker, self.task, target, agent, entry["attempts"],
                                      self.state_dir / agent, entry.get("error") or "")
                    running[fut] = (target, agent)
                    busy_agents.add(agent)
                    scheduled = True
                if not running:
                    if not scheduled:
                        break
                    continue
                completed, _ = wait(running, return_when=FIRST_COMPLETED)
                for fut in completed:
                    target, agent = running.pop(fut)
                    busy_agents.remove(agent)
                    try:
                        result = fut.result()
                    except Exception as exc:
                        entry = statuses[target.name]
                        entry["error"] = f"worker launcher: {exc}"
                        entry["status"] = "failed" if entry["attempts"] >= self.task.max_attempts else "pending"
                        self._save("worker_launch_failed", target=target.name, reason=str(exc))
                    else:
                        self._finish_worker(target, agent, result)
        failed = [name for name, e in self.state["targets"].items() if e["status"] != "done"]
        if failed:
            self.state["phase"] = "failed"
            self._save("task_failed", incomplete=failed)
            return self.state
        required = list(targets)
        if export:
            out = self.state_dir / "export"
            exported = self.backend.export(out)
            if not exported.get("ok"):
                raise RuntimeError("stock export failed")
            self._record_costs(exported)
            self.state["export"] = exported
            self._save("stock_export_built", output=str(out))
        verdict = self.backend.validate(required)
        self._record_costs(verdict)
        self.state["contract_validation"] = verdict
        if not verdict.get("ok"):
            self.state["phase"] = "failed"
            self._save("contract_validation_failed")
            return self.state
        self.state["phase"] = "complete" if export else "targets_validated"
        self._save("task_complete" if export else "targets_validated")
        return self.state

    def status(self) -> dict:
        state = self.backend.load_state()
        if state is None:
            raise RuntimeError(f"no durable task record for {self.task.id}")
        if state.get("fingerprint") != self.task.fingerprint:
            raise RuntimeError("task contract differs from the frozen store record")
        return state

    def export(self, out: Path) -> dict:
        self.state = self.status()
        if any(e["status"] != "done" for e in self.state["targets"].values()):
            raise RuntimeError("required targets are incomplete")
        def verify_recorded_heads() -> dict:
            verdict = self.backend.validate([t.name for t in self.task.targets])
            if not verdict.get("ok") or any(
                not verdict.get("targets", {}).get(t.name, {}).get("ok") or
                verdict["targets"][t.name].get("group") != self.state["targets"][t.name].get("group")
                for t in self.task.targets
            ):
                raise RuntimeError("required target head differs from recorded validated group")
            return verdict
        verify_recorded_heads()
        exported = self.backend.export(out.resolve())
        if not exported.get("ok"):
            raise RuntimeError("stock export failed")
        verdict = verify_recorded_heads()
        self.state["export"] = exported
        self.state["contract_validation"] = verdict
        self.state["phase"] = "complete"
        self._save("stock_export_built", output=str(out.resolve()))
        return self.state
