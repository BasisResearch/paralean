#!/usr/bin/env python3
"""Real SSH LSP round trips with remapped roots and optional stream delay.

Requires an already configured SSH endpoint; creates only private roots under
--run-dir. The benchmark does not change the host's network configuration.
"""
import argparse
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import time

from editor import Editor, diagnostic, percentile

REPO = Path(__file__).resolve().parents[3]


def run(args):
    root = args.run_dir.resolve()
    root.mkdir(parents=True, exist_ok=False)
    ssh = ["ssh", "-T", "-p", str(args.port), "-i", str(args.key.resolve()),
           "-o", "IdentitiesOnly=yes", "-o", "BatchMode=yes",
           "-o", "StrictHostKeyChecking=yes", "-o",
           "UserKnownHostsFile=" + str(args.known_hosts.resolve())]
    if args.delay_ms:
        proxy = [sys.executable, str(Path(__file__).with_name("ssh_delay_proxy.py")),
                 "%h", "%p", "--delay-ms", str(args.delay_ms)]
        ssh += ["-o", "ProxyCommand=" + shlex.join(proxy)]
    ssh += [args.host]
    identity = subprocess.check_output(ssh + ["hostname"], text=True).strip()
    local, remote = root / "editor", root / "remote"
    local.mkdir()
    # The SSH endpoint is on this machine, but the worker root is separately
    # provisioned over SSH. No source file is written into the local root.
    subprocess.run(ssh + [shlex.join(["mkdir", "-p", str(remote)])], check=True)
    config = {"root": str(remote), "command": [args.lean, "--server"],
              "env": {key: os.environ[key] for key in
                      ("PATH", "LEAN_PATH", "LEAN_PARALEAN", "PARALEAN_BIN", "PARALEAN_LIB")
                      if key in os.environ}}
    config["env"].update(PARALEAN_STORE=str(remote / "cache"),
                         PARALEAN_WORK_ROOT=str(remote), PARALEAN_VISIBILITY="1",
                         LEAN_NUM_THREADS="1")
    config_path = remote / "worker.json"
    subprocess.run(ssh + ["cat > " + shlex.quote(str(config_path))],
                   input=json.dumps(config), text=True, check=True)
    worker = ssh + [shlex.join([sys.executable,
                               str(Path(__file__).with_name("ssh_worker.py")), str(config_path)])]
    command = [sys.executable, str(REPO / "impl/p4/lsp.py"),
               "--workspace", f"ssh={local}", "--worker-root", f"ssh={remote}",
               "--worker-command", "ssh=" + json.dumps(worker)]
    client = Editor(command, REPO / "impl/p1", 60)
    uri = (local / "Main.lean").as_uri()
    text = "def alpha : Nat := 1\n#check alpha\n#check Nat.succ\nexample : True := by\n  trivial\n"
    timings = {}

    def request(method, params, key):
        start = time.monotonic()
        result = client.response(client.send(method, params))
        timings.setdefault(key, []).append((time.monotonic() - start) * 1000)
        assert result is not None, (method, result)
        return result

    try:
        client.response(client.send("initialize", {
            "processId": os.getpid(), "rootUri": local.as_uri(),
            "capabilities": {"textDocument": {"publishDiagnostics": {"versionSupport": True}}}}))
        client.send("initialized", {}, request=False)
        client.send("textDocument/didOpen", {"textDocument": {
            "uri": uri, "languageId": "lean4", "version": 1, "text": text}}, request=False)
        diagnostic(client, uri, 1)
        for i in range(args.samples):
            for version, content, error, key in (
                    (i * 2 + 2, text.replace("#check alpha", "#check w5Missing"), True, "edit_error"),
                    (i * 2 + 3, text, False, "edit_clean")):
                start = time.monotonic()
                client.send("textDocument/didChange", {
                    "textDocument": {"uri": uri, "version": version},
                    "contentChanges": [{"text": content}]}, request=False)
                response = diagnostic(client, uri, version, require_error=error)
                assert error == any(d.get("severity") == 1 for d in response["params"]["diagnostics"])
                timings.setdefault(key, []).append((time.monotonic() - start) * 1000)
            doc = {"textDocument": {"uri": uri}}
            hover = request("textDocument/hover", {**doc, "position": {"line": 1, "character": 8}}, "hover")
            assert "alpha" in json.dumps(hover)
            request("$/lean/plainGoal", {**doc, "position": {"line": 4, "character": 2}}, "goals")
            request("textDocument/completion", {**doc, "position": {"line": 2, "character": 12}}, "completion")
        source = client.response(client.send("paralean/source", {"uri": uri}))
        assert source["text"] == text and source["version"] == args.samples * 2 + 1
        assert not (local / "Main.lean").exists(), "edits must remain editor buffers"
    finally:
        client.close()
    report = {"gate": "pass", "transport": "ssh", "host": identity,
              "endpoint": f"{args.host}:{args.port}", "samples": args.samples,
              "one_way_added_delay_ms": args.delay_ms,
              "remote_root": str(remote), "editor_root": str(local),
              "latencies": {key: {"p50_ms": round(percentile(values, 50), 2),
                                  "p95_ms": round(percentile(values, 95), 2),
                                  "samples_ms": [round(v, 2) for v in values]}
                            for key, values in timings.items()}}
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--host", default="127.0.0.1")
    p.add_argument("--port", type=int, required=True)
    p.add_argument("--key", type=Path, required=True)
    p.add_argument("--known-hosts", type=Path, required=True)
    p.add_argument("--lean", required=True)
    p.add_argument("--delay-ms", type=float, default=0)
    p.add_argument("--samples", type=int, default=10)
    p.add_argument("--run-dir", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    run(p.parse_args())
