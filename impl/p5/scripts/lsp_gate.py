#!/usr/bin/env python3
"""One P5 worker edits through real LSP, captures privately, then publishes explicitly."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "impl/p5"))
sys.path.insert(0, str(ROOT / "impl/p4/tests"))

from editor import Editor, diagnostic
from p5lib.backend import Backend
from p5lib.lsp_provision import SshEndpoint, lsp_workspace_args, provision_ssh_copy
from p5lib.task import load


def rejected(editor: Editor, method: str, params: dict) -> str:
    request = editor.send(method, params)
    reply = editor.take(lambda item: item.get("id") == request)
    if "error" not in reply:
        raise AssertionError(f"{method} unexpectedly accepted: {reply}")
    return reply["error"]["message"]


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("run_dir", type=Path)
    p.add_argument("--ssh-host")
    p.add_argument("--ssh-user")
    p.add_argument("--ssh-port", type=int, default=22)
    p.add_argument("--ssh-identity", type=Path)
    p.add_argument("--ssh-known-hosts", type=Path)
    p.add_argument("--ssh-root", type=Path)
    p.add_argument("--lean-server", default=shutil.which("lean"))
    p.add_argument("--timeout", type=float, default=90)
    p.add_argument("--revoke-policy", action="store_true",
                   help="revoke the private validator after publication and check idle push")
    p.add_argument("--remote-dependent", action="store_true",
                   help="publish a second target by loading the first through remote%%")
    args = p.parse_args()
    if not args.lean_server:
        p.error("a Paralean fork Lean server is required")
    if not os.environ.get("PARALEAN_INSTANCE") or not os.environ.get("PARALEAN_P5_RECOVERY_SECRET"):
        p.error("a private P5 store instance and recovery secret are required")
    library = os.environ.get("PARALEAN_LIB")
    if not library or not Path(library).is_dir():
        p.error("PARALEAN_LIB must name the built Paralean Lean library")
    os.environ["LEAN_PATH"] = library + (os.pathsep + os.environ["LEAN_PATH"]
                                           if os.environ.get("LEAN_PATH") else "")
    os.environ["LEAN_PARALEAN"] = "1"
    run_dir = args.run_dir.resolve()
    run_dir.mkdir(parents=True, exist_ok=False)
    task_path = run_dir / "TASK.toml"
    task_id = "editor-lsp-" + hashlib.sha256(str(run_dir).encode()).hexdigest()[:12]
    # Keep this receipt/revocation fixture isolated from the parent recovery
    # gate even when gate.py passes its own deployment in the environment.
    os.environ["PARALEAN_DEPLOYMENT"] = task_id
    task_spec = """[task]
id = "TASK_ID"
name = "Editor LSP receipt gate"

[controller]
workers = 1
max_attempts = 1

[worker]
kind = "command"
command = ["scripted-lsp-editor"]

[[targets]]
name = "P5Lsp.one"
statement = "True"
file = "A.lean"
owner = "w0"
deps = []
""".replace("TASK_ID", task_id)
    if args.remote_dependent:
        task_spec += """
[[targets]]
name = "P5Lsp.two"
statement = "True"
file = "B.lean"
owner = "w0"
deps = ["P5Lsp.one"]
"""
    task_path.write_text(task_spec)
    task = load(task_path)
    backend = Backend(task.as_dict() | {"agents": ["w0"]}, run_dir)
    result = {"gate": "p5-lsp-worker", "worker": "scripted JSON-RPC editor",
              "transport": "ssh" if args.ssh_host else "local", "checks": {}}
    editor = None
    try:
        backend.setup()
        workspace = run_dir / "w0"
        backend.provision("w0", workspace)
        epoch = backend.assign_target("P5Lsp.one", "w0")
        observed = backend.observe_target("P5Lsp.one", "w0")
        assert observed["assigned_to_agent"] and observed["epoch"] == epoch, observed
        backend.sync("w0", workspace)
        endpoint = None
        if args.ssh_host:
            if not all((args.ssh_user, args.ssh_identity, args.ssh_known_hosts, args.ssh_root)):
                p.error("SSH requires user, identity, known_hosts and dedicated root")
            endpoint = SshEndpoint(args.ssh_host, args.ssh_user, args.ssh_port,
                                   args.ssh_identity, args.ssh_known_hosts, args.ssh_root,
                                   runtime_env={key: os.environ[key] for key in
                                                ("PATH", "LEAN_PATH", "PARALEAN_SYSROOT", "PARALEAN_BIN",
                                                 "PARALEAN_DEPLOYMENT", "PARALEAN_FDB_CLUSTER",
                                                 "PARALEAN_S3_ENDPOINT", "PARALEAN_S3_BUCKET",
                                                 "PARALEAN_S3_REGION", "PARALEAN_PLR",
                                                 "LD_LIBRARY_PATH", "AWS_ACCESS_KEY_ID",
                                                 "AWS_SECRET_ACCESS_KEY", "AWS_SESSION_TOKEN",
                                                 "PARALEAN_S3_ACCESS_KEY", "PARALEAN_S3_SECRET_KEY")
                                                if key in os.environ})
            provision_ssh_copy(workspace, endpoint)
            result["ssh_root"] = str(endpoint.root)
        router = [sys.executable, str(ROOT / "impl/p4/lsp.py")]
        router += lsp_workspace_args("w0", workspace, [args.lean_server, "--server"], endpoint)
        router += ["--p5-task", str(task_path), "--p5-state", str(run_dir)]
        if endpoint is not None:
            ssh_map = run_dir / "ssh-map.json"
            ssh_map.write_text(json.dumps({"w0": {"host": endpoint.host, "user": endpoint.user,
                "port": endpoint.port, "identity_file": str(endpoint.identity_file.resolve()),
                "known_hosts": str(endpoint.known_hosts.resolve()), "root": str(endpoint.root),
                "runtime_env": endpoint.runtime_env}}))
            ssh_map.chmod(0o600)
            router += ["--p5-ssh-map", str(ssh_map)]
        editor = Editor(router, ROOT / "impl/p1", args.timeout)
        init = editor.response(editor.send("initialize", {
            "processId": os.getpid(), "rootUri": workspace.as_uri(),
            "workspaceFolders": [{"uri": workspace.as_uri(), "name": "w0"}],
            "capabilities": {"textDocument": {"publishDiagnostics": {"versionSupport": True}}}}))
        assert "capabilities" in init, init
        editor.send("initialized", {}, request=False)
        uri = (workspace / "work" / "A.lean").as_uri()
        editor.send("textDocument/didOpen", {"textDocument": {"uri": uri,
                    "languageId": "lean4", "version": 1, "text": ""}}, request=False)
        diagnostic(editor, uri, 1)
        bad = "theorem P5Lsp.one : True := by\n  exact missingProof\n"
        editor.send("textDocument/didChange", {"textDocument": {"uri": uri, "version": 2},
                    "contentChanges": [{"text": bad}]}, request=False)
        diagnostic(editor, uri, 2)
        bad_capture = rejected(editor, "paralean/capture", {"uri": uri, "version": 2})
        before = backend.validate(["P5Lsp.one"])
        assert not before.get("ok"), before
        result["checks"]["invalid_buffer_private"] = {
            "ok": True, "capture_rejection": bad_capture}
        good = "theorem P5Lsp.one : True := by\n  trivial\n"
        edit_at = time.monotonic()
        editor.send("textDocument/didChange", {"textDocument": {"uri": uri, "version": 3},
                    "contentChanges": [{"text": good}]}, request=False)
        diagnostic(editor, uri, 3)
        result["checks"]["did_change_ms"] = round((time.monotonic() - edit_at) * 1000, 2)
        captured = editor.response(editor.send("paralean/capture", {"uri": uri, "version": 3}))
        assert any("P5Lsp.one" in x.get("names", []) for x in captured["packages"]), captured
        assert not backend.validate(["P5Lsp.one"]).get("ok")
        stale = rejected(editor, "paralean/publish", {"uri": uri, "version": 2,
            "target": "P5Lsp.one", "owner": "w0", "epoch": epoch,
            "policy": "frozen-target"})
        assert "stale" in stale.lower(), stale
        published = editor.response(editor.send("paralean/publish", {"uri": uri, "version": 3,
            "target": "P5Lsp.one", "owner": "w0", "epoch": epoch,
            "policy": "frozen-target"}), timeout=300)
        assert published["committed"] and published["group"], published
        result["checks"]["explicit_receipt_publication"] = {
            "ok": True, "group": published["group"], "epoch": epoch}
        required = ["P5Lsp.one"]
        if args.remote_dependent:
            # The policy feed must pull this new certified group into the SSH
            # mirror before replacing its Lean worker. No editor request drives it.
            pushed = editor.take(lambda item: item.get("method") == "paralean/environmentChanged"
                and item.get("params", {}).get("workspace") == "w0"
                and item["params"].get("generation", 0) > published["stamp"]["generation"],
                timeout=45)
            assert pushed["params"]["policyReady"], pushed
            backend.sync("w0", workspace)
            epoch_two = backend.assign_target("P5Lsp.two", "w0")
            uri_two = (workspace / "work" / "B.lean").as_uri()
            dependent = (f'theorem P5Lsp.one : True :=\n  remote% "{published["group"]}"\n'
                         "theorem P5Lsp.two : True := by\n  exact P5Lsp.one\n")
            editor.send("textDocument/didOpen", {"textDocument": {"uri": uri_two,
                "languageId": "lean4", "version": 1, "text": ""}}, request=False)
            diagnostic(editor, uri_two, 1)
            editor.send("textDocument/didChange", {"textDocument": {"uri": uri_two,
                "version": 2}, "contentChanges": [{"text": dependent}]}, request=False)
            clean_two = diagnostic(editor, uri_two, 2)
            assert not any(d.get("severity") == 1 for d in clean_two["params"]["diagnostics"]), clean_two
            capture_two = editor.response(editor.send("paralean/capture", {"uri": uri_two,
                "version": 2}))
            assert any("P5Lsp.two" in x.get("names", []) for x in capture_two["packages"]), capture_two
            published_two = editor.response(editor.send("paralean/publish", {"uri": uri_two,
                "version": 2, "target": "P5Lsp.two", "owner": "w0", "epoch": epoch_two,
                "policy": "frozen-target"}), timeout=300)
            assert published_two["committed"] and published_two["group"], published_two
            required.append("P5Lsp.two")
            result["checks"]["remote_percent_dependent"] = {"ok": True,
                "group": published_two["group"], "dependency_group": published["group"],
                "policy_generation": pushed["params"]["generation"]}
        current = backend.validate(required)
        assert current["ok"] and current["targets"]["P5Lsp.one"]["group"] == published["group"], current
        exported = backend.export(run_dir / "export")
        assert exported.get("ok"), exported
        result["checks"]["current_target_and_stock_export"] = {
            "ok": True, "catalog": exported.get("checkpoint", {}).get("catalog")}
        if args.revoke_policy:
            rotation_before = editor.response(editor.send("paralean/source", {"uri": uri}))
            trust_file = run_dir / "trust.json"
            original_trust = trust_file.read_bytes()
            rotated_trust = (json.dumps(json.loads(original_trust), sort_keys=True,
                                        separators=(",", ":")) + "\n").encode()
            if rotated_trust == original_trust:
                rotated_trust += b"\n"
            trust_file.write_bytes(rotated_trust)
            trust_push = editor.take(lambda item: item.get("method") == "paralean/environmentChanged"
                and item.get("params", {}).get("workspace") == "w0"
                and item["params"].get("generation", 0) > rotation_before["generation"], timeout=45)
            assert trust_push["params"]["policyReady"], trust_push
            assert (workspace / "trust.json").read_bytes() == rotated_trust
            if endpoint is not None:
                mirrored = subprocess.run(
                    endpoint.ssh + ["cat " + shlex.quote(str(endpoint.root / "trust.json"))],
                    stdin=subprocess.DEVNULL, capture_output=True, check=True, timeout=30)
                assert mirrored.stdout == rotated_trust
            result["checks"]["idle_controller_trust_push"] = {
                "ok": True, "generation": trust_push["params"]["generation"]}
            source_before = editor.response(editor.send("paralean/source", {"uri": uri}))
            old_session = editor.response(editor.send("$/lean/rpc/connect", {"uri": uri}))["sessionId"]
            key_file = run_dir / "keys.json"
            validator_key = json.loads(key_file.read_text())["validators"]["v0"]["public"]
            bridge_bin = os.environ.get("PARALEAN_P5_BRIDGE", str(ROOT /
                ".runs/w5-controller-cargo/release/paralean-p5-store"))
            worker_attempt = subprocess.run([bridge_bin, "revoke-validator", "--key", validator_key,
                                             "--reason", "worker authority negative gate"],
                                            env={**os.environ, "PARALEAN_KEYS": str(run_dir / "keys-w0.json")},
                                            text=True, capture_output=True, timeout=30)
            assert worker_attempt.returncode and "authority seed required" in worker_attempt.stderr, worker_attempt
            result["checks"]["worker_cannot_revoke_policy"] = {"ok": True}
            revoked = subprocess.run([bridge_bin, "revoke-validator", "--key", validator_key,
                                      "--reason", "isolated LSP policy push gate"],
                                     env={**os.environ, "PARALEAN_KEYS": str(key_file)},
                                     text=True, capture_output=True, timeout=30)
            if revoked.returncode:
                raise RuntimeError("private validator revocation failed: " + revoked.stderr[-1000:])
            pushed = editor.take(lambda item: item.get("method") == "paralean/environmentChanged"
                and item.get("params", {}).get("workspace") == "w0"
                and item["params"].get("generation", 0) > source_before["generation"], timeout=45)
            assert pushed["params"]["policyReady"], pushed
            expired = rejected(editor, "$/lean/rpc/call", {"sessionId": old_session,
                "textDocument": {"uri": uri}, "position": {"line": 0, "character": 0},
                "method": "Lean.Widget.getInteractiveGoals",
                "params": {"textDocument": {"uri": uri},
                           "position": {"line": 0, "character": 0}}})
            assert "expired" in expired.lower(), expired
            result["checks"]["idle_store_policy_push"] = {
                "ok": True, "generation": pushed["params"]["generation"],
                "old_session_rejected": expired}
            # W3 agent-key registry through the same feed: a worker key cannot
            # revoke an author; the authority's revocation reaches the editor and
            # publication is refused before any validator work.
            worker_agent = subprocess.run([bridge_bin, "revoke-agent-key", "--ws", "w0"],
                                          env={**os.environ, "PARALEAN_KEYS": str(run_dir / "keys-w0.json")},
                                          text=True, capture_output=True, timeout=30)
            assert worker_agent.returncode and "authority seed required" in worker_agent.stderr, worker_agent
            agent_before = editor.response(editor.send("paralean/source", {"uri": uri}))
            revoked_agent = subprocess.run([bridge_bin, "revoke-agent-key", "--ws", "w0"],
                                           env={**os.environ, "PARALEAN_KEYS": str(key_file)},
                                           text=True, capture_output=True, timeout=30)
            if revoked_agent.returncode:
                raise RuntimeError("private agent-key revocation failed: " + revoked_agent.stderr[-1000:])
            agent_push = editor.take(lambda item: item.get("method") == "paralean/environmentChanged"
                and item.get("params", {}).get("workspace") == "w0"
                and item["params"].get("generation", 0) > agent_before["generation"], timeout=45)
            editor.response(editor.send("paralean/capture", {"uri": uri, "version": 3}))
            refused = rejected(editor, "paralean/publish", {"uri": uri, "version": 3,
                "target": "P5Lsp.one", "owner": "w0", "epoch": epoch, "policy": "frozen-target"})
            assert "agent key" in refused.lower(), refused
            result["checks"]["agent_key_revocation"] = {
                "ok": True, "generation": agent_push["params"]["generation"],
                "worker_refused": True, "publish_refused": refused}
        result["ok"] = True
        return 0
    finally:
        if editor:
            editor.close()
        backend.close()
        (run_dir / "lsp-gate.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    raise SystemExit(main())
