#!/usr/bin/env python3
"""LSP latency gate on a real P3 working file containing `remote%` loads.

Run with the rebuilt fork and P1 library, after a fresh P3 gate has produced a
copy. The proxy is an actual subprocess and the client uses framed JSON-RPC.
"""

import argparse
import json
import os
from pathlib import Path
import re
import sys
import time

from editor import Editor, percentile


REPO = Path(__file__).resolve().parents[3]


def request(editor, method, params):
    return editor.response(editor.send(method, params))


def diagnostics(editor, uri, version):
    return [d for m in editor.pending if m.get("method") == "textDocument/publishDiagnostics"
            and m.get("params", {}).get("uri") == uri
            and m.get("params", {}).get("version") == version
            for d in m["params"]["diagnostics"]]


def cross_size_group(copy):
    source = (copy / "work/A.lean").read_text()
    group = None
    for match in re.finditer(r"-- paralean:published ([0-9a-f]{64})(.*?)-- paralean:end", source, re.S):
        if "def Cross.size" in match.group(2):
            group = match.group(1)
    assert group, "fixture needs a published Cross.size definition"
    return group


def main(args):
    library = Path(os.environ["PARALEAN_LIB"]).resolve()
    assert (library / "Paralean/Visibility.olean").is_file(), library
    os.environ["LEAN_PARALEAN"] = "1"
    os.environ["LEAN_PATH"] = os.pathsep.join(
        part for part in (str(library), os.environ.get("LEAN_PATH", "")) if part)
    copy = args.copy.resolve()
    path = copy / "work" / args.file
    source = path.read_text()
    assert "remote%" in source, "fixture must contain remote% loads"
    assert (copy / "cache").is_dir() and (copy / "keys.json").is_file()
    if args.mathlib and "import Mathlib.Order.Basic" not in source:
        source = "import Mathlib.Order.Basic\n" + source
    base = source.rstrip() + "\n\n"
    good = base + "#check Shared.dup\nexample : True := by\n  trivial\n"
    bad = good.replace("#check Shared.dup", "#check missingParaleanRemoteName")
    line = len(base.splitlines())
    uri = path.as_uri()
    command = [sys.executable, str(REPO / "impl/p4/lsp.py"), "--workspace", f"a={copy}"]
    editor = Editor(command, copy, args.timeout)
    times = {k: [] for k in ("edit_to_diagnostics_bad", "edit_to_diagnostics_good", "hover", "goals", "completion", "reconnect_to_diagnostics")}
    try:
        init = request(editor, "initialize", {
            "processId": os.getpid(), "rootUri": copy.as_uri(),
            "capabilities": {"textDocument": {"publishDiagnostics": {"versionSupport": True}}},
        })
        assert "capabilities" in init
        editor.send("initialized", {}, request=False)
        editor.send("textDocument/didOpen", {"textDocument": {
            "uri": uri, "languageId": "lean4", "version": 1, "text": good}}, request=False)
        request(editor, "textDocument/waitForDiagnostics", {"uri": uri, "version": 1})
        initial = [m for m in editor.pending if m.get("method") == "textDocument/publishDiagnostics"
                   and m.get("params", {}).get("uri") == uri
                   and m.get("params", {}).get("version") == 1]
        assert initial, "initial working-copy diagnostics not delivered"
        assert not any(d.get("severity") == 1 for m in initial
                       for d in m["params"]["diagnostics"]), initial
        for i in range(args.samples):
            for label, content, version in (("bad", bad, 2 * i + 2),
                                            ("good", good, 2 * i + 3)):
                start = time.monotonic()
                editor.send("textDocument/didChange", {"textDocument": {"uri": uri, "version": version},
                            "contentChanges": [{"text": content}]}, request=False)
                request(editor, "textDocument/waitForDiagnostics", {"uri": uri, "version": version})
                times[f"edit_to_diagnostics_{label}"].append((time.monotonic() - start) * 1000)
                messages = [m for m in editor.pending if m.get("method") == "textDocument/publishDiagnostics"
                            and m.get("params", {}).get("uri") == uri
                            and m.get("params", {}).get("version") == version]
                if label == "bad":
                    assert any("missingParaleanRemoteName" in d.get("message", "")
                               for m in messages for d in m["params"]["diagnostics"]), messages
                else:
                    assert not any(d.get("severity") == 1 for m in messages
                                   for d in m["params"]["diagnostics"]), messages
            doc = {"textDocument": {"uri": uri}}
            for name, method, position in (("hover", "textDocument/hover", {"line": line, "character": 15}),
                                           ("goals", "$/lean/plainGoal", {"line": line + 2, "character": 2}),
                                           ("completion", "textDocument/completion", {"line": line, "character": 15})):
                start = time.monotonic()
                result = request(editor, method, {**doc, "position": position})
                times[name].append((time.monotonic() - start) * 1000)
                assert result is not None, (name, result)
        old_session = request(editor, "$/lean/rpc/connect", {"uri": uri})["sessionId"]
        assert request(editor, "workspace/executeCommand", {
            "command": "paralean/killWorker", "arguments": ["a"]})
        reconnect_version = 2 * args.samples + 2
        start = time.monotonic()
        editor.send("textDocument/didChange", {
            "textDocument": {"uri": uri, "version": reconnect_version},
            "contentChanges": [{"text": good}]}, request=False)
        request(editor, "textDocument/waitForDiagnostics", {"uri": uri, "version": reconnect_version})
        times["reconnect_to_diagnostics"].append((time.monotonic() - start) * 1000)
        assert request(editor, "textDocument/hover", {
            "textDocument": {"uri": uri}, "position": {"line": line, "character": 15}}) is not None
        expired_id = editor.send("$/lean/rpc/call", {
            "sessionId": old_session, "textDocument": {"uri": uri},
            "position": {"line": line, "character": 15},
            "method": "Lean.Widget.getInteractiveGoals", "params": {}})
        expired = editor.take(lambda x: x.get("id") == expired_id)
        assert expired.get("error", {}).get("code") == -32002, expired
        if args.extra_checks:
            group = cross_size_group(copy)
            isolation = copy / "work/P4Isolation.lean"
            isolation_uri = isolation.as_uri()
            isolation_text = ("local instance : OfNat Nat 5 := ⟨999⟩\n"
                              f"remote_decl% \"{group}\"\n")
            editor.send("textDocument/didOpen", {"textDocument": {
                "uri": isolation_uri, "languageId": "lean4", "version": 1,
                "text": isolation_text}}, request=False)
            request(editor, "textDocument/waitForDiagnostics", {"uri": isolation_uri, "version": 1})
            assert not any(d.get("severity") == 1 for d in diagnostics(editor, isolation_uri, 1)), diagnostics(editor, isolation_uri, 1)

            rollback = copy / "work/P4Rollback.lean"
            rollback_uri = rollback.as_uri()
            initial_load = f"remote_decl% \"{group}\"\n"
            editor.send("textDocument/didOpen", {"textDocument": {
                "uri": rollback_uri, "languageId": "lean4", "version": 1,
                "text": initial_load}}, request=False)
            request(editor, "textDocument/waitForDiagnostics", {"uri": rollback_uri, "version": 1})
            assert not any(d.get("severity") == 1 for d in diagnostics(editor, rollback_uri, 1)), diagnostics(editor, rollback_uri, 1)
            conflict = f"def Cross.size : Nat := 999\nremote_decl% \"{group}\"\n"
            editor.send("textDocument/didChange", {"textDocument": {"uri": rollback_uri, "version": 2},
                        "contentChanges": [{"text": conflict}]}, request=False)
            request(editor, "textDocument/waitForDiagnostics", {"uri": rollback_uri, "version": 2})
            failures = [d.get("message", "") for d in diagnostics(editor, rollback_uri, 2)
                        if d.get("severity") == 1]
            assert failures and any("version conflict" in m or "reproduce" in m or "differs" in m
                                    for m in failures), failures
        report = {"gate": "pass", "benchmark": args.label, "file": args.file, "latencies": {}}
        for key, values in times.items():
            item = {"n": len(values), "p50_ms": round(percentile(values, 50), 2),
                    "p95_ms": round(percentile(values, 95), 2),
                    "samples_ms": [round(x, 2) for x in values]}
            if len(values) > 2:
                item.update(first_ms=round(values[0], 2),
                            warm_p50_ms=round(percentile(values[1:], 50), 2),
                            warm_p95_ms=round(percentile(values[1:], 95), 2))
            report["latencies"][key] = item
        print(json.dumps(report, indent=2))
        if args.output:
            Path(args.output).write_text(json.dumps(report, indent=2) + "\n")
    finally:
        editor.close()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("copy", type=Path)
    parser.add_argument("--file", default="Shared.lean")
    parser.add_argument("--samples", type=int, default=10)
    parser.add_argument("--timeout", type=float, default=60)
    parser.add_argument("--label", default="remote Init")
    parser.add_argument("--mathlib", action="store_true",
                        help="prepend a Mathlib import to the remote working copy buffer")
    parser.add_argument("--extra-checks", action="store_true",
                        help="test local instance isolation and same-document cached-load rollback")
    parser.add_argument("--output")
    main(parser.parse_args())
