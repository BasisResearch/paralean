#!/usr/bin/env python3
"""Remove each editor publication guard in an isolated module and require detection."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from impl.p5.tests import test_editor_bridge as tests

SOURCE = (ROOT / "impl/p4/controller_bridge.py").read_text()
PROVISION_SOURCE = (ROOT / "impl/p5/p5lib/lsp_provision.py").read_text()
BACKEND_SOURCE = (ROOT / "impl/p5/p5lib/backend.py").read_text()
ROUTER_SOURCE = (ROOT / "impl/p4/lsp.py").read_text()
CASES = [
    ("captured_stamp", "            saved = self.captures.get(self._key(ws, uri))\n            if saved is None or any(saved.get(k) != v for k, v in stamp.items()):",
     "            saved = self.captures.get(self._key(ws, uri))\n            if saved is None:",
     "test_each_stamp_mutation_refuses_publication"),
    ("target_in_capture", "if target not in names:", "if False:",
     "test_policy_and_assignment_guards"),
    ("assigned_owner", "not observation.get(\"assigned_to_agent\")", "False",
     "test_policy_and_assignment_guards"),
    ("workspace_owner", "owner != ws.name", "False",
     "test_registered_other_owner_cannot_publish_this_workspace_buffer"),
    ("explicit_policy", "if policy != \"frozen-target\" or not target",
     "if False or not target", "test_policy_and_assignment_guards"),
    ("precommit_stamp", "def precommit_guard() -> None:\n                self._assert_current(ws, uri, stamp)",
     "def precommit_guard() -> None:\n                pass", "test_mutation_after_validation_aborts_before_commit"),
    ("precommit_policy", "self._assert_store_policy(ws)", "pass",
     "test_live_policy_change_after_validation_aborts_commit"),
    ("precommit_disk", "if not source.is_file() or hashlib.sha256(source.read_bytes()).hexdigest() != stamp[\"source_sha256\"]:",
     "if False:", "test_external_source_edit_after_validation_aborts_commit"),
    ("capture_rejected", "if capture.get(\"rejected\") or capture.get(\"rejectedPids\"):",
     "if False:", "test_capture_worker_is_private_and_restarts_on_generation_change"),
    ("capture_worker_stamp", "if any(result.get(k) != stamp[k] for k in (\"file\", \"version\", \"environment\", \"generation\")):",
     "if False:", "test_capture_worker_is_private_and_restarts_on_generation_change"),
    ("policy_unavailable", "if self.policy_probe is not None and ws.name not in self.policy_ready:",
     "if False:", "test_policy_push_invalidates_capture_and_replaces_worker"),
    ("session_invalidation", "                self.proxy.drop_sessions(ws)",
     "                pass", "test_policy_push_invalidates_capture_and_replaces_worker"),
    ("probe_readiness_fence", "                self.policy_ready.discard(ws.name)\n                self.policy_events[ws.name].clear()",
     "                self.policy_events[ws.name].clear()", "test_policy_probe_fences_requests_while_pulling_registry"),
    ("probe_completion_gate", "                self.policy_events[ws.name].clear()",
     "                pass", "test_policy_probe_fences_requests_while_pulling_registry"),
    ("controller_trust_source_refresh", "            self.backend.refresh_public_trust(ws.name, ws.root)",
     "            pass", "test_controller_trust_source_rotation_pushes_local_and_remote_environment"),
    ("state_credentials_binding",
     'backend = Backend(task.as_dict() | {"agents": agents}, state_dir,\n                      env={"PARALEAN_KEYS": str(state_dir / "keys.json"),\n                           "PARALEAN_TRUST": str(state_dir / "trust.json")})',
     'backend = Backend(task.as_dict() | {"agents": agents}, state_dir)',
     "test_attach_pins_task_credentials_over_inherited_environment"),
    ("pinned_workspace_paths",
     "if any(ws.env_overrides.get(key) != value for key, value in pinned.items()):",
     "if False:", "test_attach_pins_task_credentials_over_inherited_environment"),
    ("pinned_workspace_reload_binding",
     "        ws.bound_env = pinned.copy()",
     "        ws.bound_env = {}", "test_attach_pins_task_credentials_over_inherited_environment"),
    ("sync_readiness_fence", "                if policy_id != \"unavailable\" and self.remote_sync is not None:",
     "                self.policy_ready.add(ws.name)\n                if policy_id != \"unavailable\" and self.remote_sync is not None:",
     "test_remote_sync_fences_worker_until_copy_finishes"),
    ("sync_worker_fence", "                await ws.fence_policy()",
     "                pass", "test_remote_sync_fences_worker_until_copy_finishes"),
    ("restart_failure_readiness", "                        except Exception:\n                            self.policy_ready.discard(ws.name)",
     "                        except Exception:\n                            pass",
     "test_failed_policy_restart_fails_closed_then_recovers"),
    ("policy_push_capture", "                self.captures = {key: value for key, value in self.captures.items() if key[0] != ws.name}",
     "                pass", "test_policy_push_invalidates_capture_and_replaces_worker"),
    ("restart_failure_sessions", "                            self.proxy.drop_sessions(ws)",
     "                            pass", "test_failed_policy_restart_fails_closed_then_recovers"),
    ("restart_recovery_token", "                            self.policy_ids[ws.name] = \"unavailable\"",
     "                            pass", "test_failed_policy_restart_fails_closed_then_recovers"),
]


def main() -> int:
    with tempfile.TemporaryDirectory() as tmp:
        baseline = unittest.defaultTestLoader.loadTestsFromModule(tests)
        with open(Path(tmp) / "baseline.log", "w") as stream:
            result = unittest.TextTestRunner(stream=stream).run(baseline)
        if not result.wasSuccessful():
            raise AssertionError("baseline editor bridge tests failed before mutation")
        for index, (name, needle, replacement, method) in enumerate(CASES):
            expected_count = 2 if name in {"policy_unavailable", "session_invalidation", "sync_worker_fence"} else 1
            if SOURCE.count(needle) != expected_count:
                raise AssertionError(f"guard anchor changed: {name}")
            path = Path(tmp) / f"mutant_{index}.py"
            path.write_text(SOURCE.replace(needle, replacement, 1))
            spec = importlib.util.spec_from_file_location(f"mutant_{index}", path)
            assert spec and spec.loader
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            tests.ControllerBridge = module.ControllerBridge
            tests.BridgeError = module.BridgeError
            tests.policy_feed = module.policy_feed
            tests.attach_p5 = module.attach_p5
            suite = unittest.TestSuite([tests.BridgeTests(method)])
            with open(Path(tmp) / f"{name}.log", "w") as stream:
                result = unittest.TextTestRunner(stream=stream).run(suite)
            if not result.failures or result.errors:
                raise AssertionError(f"guard removal escaped test: {name}")
            print(f"detected {name} by {method}")
        tests.ControllerBridge = __import__("controller_bridge").ControllerBridge
        tests.BridgeError = __import__("controller_bridge").BridgeError
        tests.policy_feed = __import__("controller_bridge").policy_feed
        tests.attach_p5 = __import__("controller_bridge").attach_p5
        router_cases = [
            ("router_response_defer",
             "    async def worker_response(self, ws, message):\n        if self.bridge is not None:\n            await self.bridge.policy_events[ws.name].wait()",
             "    async def worker_response(self, ws, message):\n        if self.bridge is not None:\n            pass", tests.BridgeTests, "test_router_defers_worker_output_during_policy_probe"),
            ("router_diagnostic_defer",
             "    async def worker_message(self, ws, message, generation=None):\n        if self.bridge is not None:\n            await self.bridge.policy_events[ws.name].wait()",
             "    async def worker_message(self, ws, message, generation=None):\n        if self.bridge is not None:\n            pass", tests.BridgeTests, "test_router_defers_worker_output_during_policy_probe"),
            ("router_pinned_environment_reload",
             '        if bound is not None and any(overrides.get(key) != value for key, value in bound.items()):',
             '        if False:', tests.ProvisionTests,
             "test_workspace_env_reload_cannot_replace_bound_p5_settings"),
        ]
        for index, (name, needle, replacement, test_class, method) in enumerate(router_cases):
            if ROUTER_SOURCE.count(needle) != 1:
                raise AssertionError(f"router guard anchor changed: {name}")
            path = Path(tmp) / f"router_mutant_{index}.py"
            path.write_text(ROUTER_SOURCE.replace(needle, replacement, 1))
            spec = importlib.util.spec_from_file_location(f"router_mutant_{index}", path)
            assert spec and spec.loader
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            tests.RouterProxy = module.Proxy
            tests.RouterWorkspace = module.Workspace
            suite = unittest.TestSuite([test_class(method)])
            with open(Path(tmp) / f"{name}.log", "w") as stream:
                result = unittest.TextTestRunner(stream=stream).run(suite)
            if not result.failures or result.errors:
                raise AssertionError(f"guard removal escaped test: {name}")
            print(f"detected {name} by {method}")
        tests.RouterProxy = __import__("lsp").Proxy
        tests.RouterWorkspace = __import__("lsp").Workspace
        name = "ssh_ownership_marker"
        needle = 'f"if test -e {shlex.quote(root)}; then "'
        if PROVISION_SOURCE.count(needle) != 1:
            raise AssertionError(f"guard anchor changed: {name}")
        path = Path(tmp) / "mutant_provision.py"
        path.write_text(PROVISION_SOURCE.replace(needle, 'f"if false; then "', 1))
        spec = importlib.util.spec_from_file_location("mutant_provision", path)
        assert spec and spec.loader
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        tests.provision_ssh_copy = module.provision_ssh_copy
        suite = unittest.TestSuite([tests.ProvisionTests("test_existing_unmarked_remote_root_is_preserved")])
        with open(Path(tmp) / f"{name}.log", "w") as stream:
            result = unittest.TextTestRunner(stream=stream).run(suite)
        if not result.failures or result.errors:
            raise AssertionError(f"guard removal escaped test: {name}")
        print(f"detected {name} by test_existing_unmarked_remote_root_is_preserved")
        name = "ssh_provision_stdin_isolation"
        needle = "stdin=subprocess.DEVNULL"
        if PROVISION_SOURCE.count(needle) != 5:
            raise AssertionError(f"guard anchor changed: {name}")
        path = Path(tmp) / "mutant_provision_stdin.py"
        path.write_text(PROVISION_SOURCE.replace(needle, "stdin=None"))
        spec = importlib.util.spec_from_file_location("mutant_provision_stdin", path)
        assert spec and spec.loader
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        tests.provision_ssh_copy = module.provision_ssh_copy
        suite = unittest.TestSuite([tests.ProvisionTests("test_local_and_ssh_roots_use_distinct_transport")])
        with open(Path(tmp) / f"{name}.log", "w") as stream:
            result = unittest.TextTestRunner(stream=stream).run(suite)
        if not result.failures or result.errors:
            raise AssertionError(f"guard removal escaped test: {name}")
        print(f"detected {name} by test_local_and_ssh_roots_use_distinct_transport")
        name = "ssh_public_trust_mirror"
        needle = 'for name in ("keys.json", "trust.json"):'
        if PROVISION_SOURCE.count(needle) != 1:
            raise AssertionError(f"guard anchor changed: {name}")
        path = Path(tmp) / "mutant_provision_trust.py"
        path.write_text(PROVISION_SOURCE.replace(needle, 'for name in ("keys.json",):', 1))
        spec = importlib.util.spec_from_file_location("mutant_provision_trust", path)
        assert spec and spec.loader
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        tests.provision_ssh_copy = module.provision_ssh_copy
        suite = unittest.TestSuite([tests.ProvisionTests("test_public_trust_is_mirrored_into_remote_worker_root")])
        with open(Path(tmp) / f"{name}.log", "w") as stream:
            result = unittest.TextTestRunner(stream=stream).run(suite)
        if not result.failures or result.errors:
            raise AssertionError(f"guard removal escaped test: {name}")
        print(f"detected {name} by test_public_trust_is_mirrored_into_remote_worker_root")
        name = "backend_public_trust_refresh"
        needle = "if trust_dest.is_file() and trust_dest.read_bytes() == trusted:"
        if BACKEND_SOURCE.count(needle) != 1:
            raise AssertionError(f"guard anchor changed: {name}")
        path = Path(tmp) / "mutant_backend_trust.py"
        path.write_text(BACKEND_SOURCE.replace(needle, "if trust_dest.is_file():", 1))
        spec = importlib.util.spec_from_file_location("mutant_backend_trust", path)
        assert spec and spec.loader
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        tests.P5Backend = module.Backend
        suite = unittest.TestSuite([tests.ProvisionTests("test_backend_provision_refreshes_public_trust")])
        with open(Path(tmp) / f"{name}.log", "w") as stream:
            result = unittest.TextTestRunner(stream=stream).run(suite)
        if not result.failures or result.errors:
            raise AssertionError(f"guard removal escaped test: {name}")
        print(f"detected {name} by test_backend_provision_refreshes_public_trust")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
