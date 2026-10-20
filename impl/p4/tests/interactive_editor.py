#!/usr/bin/env python3
"""Drive isolated P4 regression fixtures through a real long-lived LSP server."""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

from editor import Editor


REPO = Path(__file__).resolve().parents[3]


def request(editor, method, params):
    return editor.response(editor.send(method, params))


def diagnostics(editor, uri, version):
    return [d for m in editor.pending if m.get("method") == "textDocument/publishDiagnostics"
            and m.get("params", {}).get("uri") == uri
            and m.get("params", {}).get("version") == version
            for d in m["params"]["diagnostics"]]


def main(args):
    manifest = json.loads(args.manifest.read_text())
    runtime = Path(manifest["runtime"])
    library = runtime / "lib/lean"
    assert (library / "Paralean/Visibility.olean").is_file(), library
    os.environ.update(LEAN_PARALEAN="1", PARALEAN_LIB=str(library),
                      PARALEAN_BIN=str(runtime / "bin/paralean"),
                      PARALEAN_DEPLOYMENT=manifest["deployment"],
                      PARALEAN_TRUST=manifest["trust"])
    os.environ["LEAN_PATH"] = os.pathsep.join(
        part for part in (str(library), os.environ.get("LEAN_PATH", "")) if part)
    workspace_root = Path(manifest["workspace_root"])
    copy = workspace_root.parent if workspace_root.name == "work" else workspace_root
    published = [json.loads(path.read_text()) for path in
                 (copy / "cache/p3/records").glob("m-*.json")]
    groups = {record["group"] for record in published if record.get("receipt")}
    assert manifest["group"] in groups, "fixture group lacks a published receipt"
    if manifest["kind"] == "instances":
        assert manifest["class_group"] in groups, "global class was not published"
    if manifest["kind"] == "open17":
        assert manifest["dependent_group"] in groups, "dependent capsule was not published"
    document = Path(manifest["document"])
    source = document.read_text()
    uri = document.as_uri()
    editor = Editor([sys.executable, str(REPO / "impl/p4/lsp.py"),
                     "--workspace", f"a={copy}"], copy, args.timeout)
    try:
        request(editor, "initialize", {"processId": os.getpid(),
                "rootUri": copy.as_uri(), "capabilities": {
                    "textDocument": {"publishDiagnostics": {"versionSupport": True}}}})
        editor.send("initialized", {}, request=False)
        editor.send("textDocument/didOpen", {"textDocument": {
            "uri": uri, "languageId": "lean4", "version": 1, "text": source}}, request=False)
        request(editor, "textDocument/waitForDiagnostics", {"uri": uri, "version": 1})
        before = diagnostics(editor, uri, 1)
        assert not [d for d in before if d.get("severity") == 1], before
        kind = manifest["kind"]
        if kind == "instances":
            assert "rootPoison" in source and manifest["group"] in source
            assert f"= {manifest['expected_value']}" in source
            # The proof elaborates only if the remote capsule uses its own
            # global instance rather than the caller's root-local poison.
            result = {"gate": "pass", "kind": kind, "diagnostics": before,
                      "provedValue": manifest["expected_value"]}
        elif kind == "open17":
            projection = Path(manifest["source_projection"]).read_text()
            assert all(token in projection for token in manifest["expected_tokens"]), projection
            assert manifest["rewritten_use"] in projection, projection
            assert source.count("remote%") >= 2 and manifest["dependent_group"] in source
            result = {"gate": "pass", "kind": kind, "errorCount": 0,
                      "warningCount": len(before),
                      "rewrittenUse": manifest["rewritten_use"]}
        elif kind == "revocation":
            revoked = subprocess.run(manifest["revoke_command"], env=dict(os.environ,
                        PARALEAN_KEYS=manifest["keys"]), capture_output=True, text=True)
            assert revoked.returncode == 0, revoked.stderr
            repeated_load = source + f'\nremote_decl% "{manifest["group"]}"\n'
            editor.send("textDocument/didChange", {"textDocument": {"uri": uri, "version": 2},
                        "contentChanges": [{"text": repeated_load}]}, request=False)
            request(editor, "textDocument/waitForDiagnostics", {"uri": uri, "version": 2})
            after = diagnostics(editor, uri, 2)
            errors = [d.get("message", "") for d in after if d.get("severity") == 1]
            assert any("revoked" in error.lower() for error in errors), errors
            request(editor, "workspace/executeCommand", {"command": "paralean/setEnvironment",
                    "arguments": ["a", "revoked-policy-epoch"]})
            editor.send("textDocument/didChange", {"textDocument": {"uri": uri, "version": 3},
                        "contentChanges": [{"text": source}]}, request=False)
            request(editor, "textDocument/waitForDiagnostics", {"uri": uri, "version": 3})
            replay_errors = [d.get("message", "") for d in diagnostics(editor, uri, 3)
                             if d.get("severity") == 1]
            assert any("revoked" in error.lower() for error in replay_errors), replay_errors
            result = {"gate": "pass", "kind": kind, "diagnosticsBefore": before,
                      "diagnosticsAfter": errors, "replayDiagnostics": replay_errors,
                      "revokeOutput": revoked.stdout.strip()}
        else:
            raise AssertionError(f"unknown fixture kind: {kind}")
        print(json.dumps(result, indent=2))
        if args.output:
            args.output.write_text(json.dumps(result, indent=2) + "\n")
    finally:
        editor.close()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--timeout", type=float, default=60)
    parser.add_argument("--output", type=Path)
    main(parser.parse_args())
