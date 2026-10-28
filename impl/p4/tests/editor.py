#!/usr/bin/env python3
"""End-to-end editor gate for the P4 stdio proxy.

This is a real LSP client: it speaks Content-Length JSON-RPC to the proxy, which
in turn starts Lean --server. It intentionally does not import the proxy module.
"""

import argparse
import json
import os
from pathlib import Path
import queue
import subprocess
import sys
import tempfile
import threading
import time


REPO = Path(__file__).resolve().parents[3]


def percentile(values, pct):
    values = sorted(values)
    rank = (len(values) - 1) * pct / 100
    lo = int(rank)
    hi = min(lo + 1, len(values) - 1)
    return values[lo] + (values[hi] - values[lo]) * (rank - lo)


class Editor:
    def __init__(self, command, cwd, timeout):
        self.process = subprocess.Popen(command, cwd=cwd, stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                        bufsize=0)
        self.timeout = timeout
        self.inbox = queue.Queue()
        self.pending = []
        self.next_id = 1
        self.stderr = bytearray()
        threading.Thread(target=self._read, daemon=True).start()
        threading.Thread(target=self._read_stderr, daemon=True).start()

    def _read(self):
        try:
            stream = self.process.stdout
            while True:
                headers = {}
                while True:
                    line = stream.readline()
                    if not line:
                        raise EOFError("server stdout closed")
                    if line == b"\r\n":
                        break
                    key, value = line.decode("ascii").split(":", 1)
                    headers[key.lower()] = value.strip()
                length = int(headers["content-length"])
                parts = []
                remaining = length
                while remaining:
                    chunk = stream.read(remaining)
                    if not chunk:
                        raise EOFError("partial LSP frame")
                    parts.append(chunk)
                    remaining -= len(chunk)
                body = b"".join(parts)
                message = json.loads(body)
                message["_received_at"] = time.monotonic()
                self.inbox.put(message)
        except Exception as exc:
            self.inbox.put(exc)

    def _read_stderr(self):
        while chunk := self.process.stderr.read(4096):
            self.stderr.extend(chunk)

    def send(self, method, params=None, request=True):
        msg = {"jsonrpc": "2.0", "method": method}
        if params is not None:
            msg["params"] = params
        if request:
            msg["id"] = self.next_id
            self.next_id += 1
        body = json.dumps(msg, separators=(",", ":")).encode()
        self.process.stdin.write(f"Content-Length: {len(body)}\r\n\r\n".encode() + body)
        self.process.stdin.flush()
        return msg.get("id")

    def take(self, predicate, timeout=None):
        deadline = time.monotonic() + (timeout or self.timeout)
        while True:
            for i, msg in enumerate(self.pending):
                if predicate(msg):
                    return self.pending.pop(i)
            left = deadline - time.monotonic()
            if left <= 0:
                raise TimeoutError(f"LSP response timed out; pending={self.pending[-5:]} "
                                   f"stderr={self.stderr[-3000:].decode(errors='replace')}")
            try:
                msg = self.inbox.get(timeout=left)
            except queue.Empty as exc:
                raise TimeoutError(f"LSP response timed out; pending={self.pending[-5:]} "
                                   f"stderr={self.stderr[-3000:].decode(errors='replace')}") from exc
            if isinstance(msg, Exception):
                raise RuntimeError(f"LSP reader failed: {msg}; stderr={self.stderr.decode(errors='replace')}")
            if predicate(msg):
                return msg
            self.pending.append(msg)

    def response(self, msg_id, timeout=None):
        msg = self.take(lambda x: x.get("id") == msg_id, timeout)
        if "error" in msg:
            raise AssertionError(f"request {msg_id} failed: {msg['error']}; "
                                 f"server stderr={self.stderr[-3000:].decode(errors='replace')}")
        return msg.get("result")

    def close(self):
        if self.process.poll() is None:
            try:
                self.response(self.send("shutdown", {}), 5)
                self.send("exit", request=False)
                self.process.wait(timeout=5)
            except Exception:
                self.process.kill()
                self.process.wait(timeout=5)


def diagnostic(editor, uri, version, require_error=False):
    return editor.take(lambda x: x.get("method") == "textDocument/publishDiagnostics"
                       and x.get("params", {}).get("uri") == uri
                       and x.get("params", {}).get("version") == version
                       and (not require_error or any(d.get("severity") == 1
                                                     for d in x["params"].get("diagnostics", []))))


def timed_request(editor, method, params, timings, key):
    start = time.monotonic()
    result = editor.response(editor.send(method, params))
    timings.setdefault(key, []).append((time.monotonic() - start) * 1000)
    return result


def worker_processes_for(token):
    matches = []
    for path in Path("/proc").iterdir():
        if not path.name.isdigit():
            continue
        try:
            command = (path / "cmdline").read_bytes().replace(b"\0", b" ").decode(errors="replace")
        except OSError:
            continue
        if token in command and ("lean --worker" in command or "lean --server" in command):
            matches.append((int(path.name), command))
    return matches


def run(args):
    timings = {}
    with tempfile.TemporaryDirectory(prefix="paralean-p4-editor-") as temp:
        base = Path(temp)
        ws_a, ws_b = base / "a", base / "b"
        ws_a.mkdir()
        ws_b.mkdir()
        file_a, file_b = ws_a / "Main.lean", ws_b / "Main.lean"
        prefix = "import Mathlib.Order.Basic\n" if args.label.lower() == "mathlib" else ""
        line_shift = prefix.count("\n")
        text_a = prefix + "def alpha : Nat := 1\n#check alpha\n#check Nat.succ\nexample : True := by\n  trivial\n"
        text_b = prefix + "def beta : Nat := 2\n#check beta\n"
        file_a.write_text(text_a)
        file_b.write_text(text_b)
        uri_a, uri_b = file_a.as_uri(), "paralean://b/Main.lean"
        command = [sys.executable, str(REPO / "impl/p4/lsp.py"),
                   "--workspace", f"a={ws_a}", "--workspace", f"b={ws_b}"]
        if args.worker_remap:
            worker_root = base / "worker-a"
            worker_root.mkdir()
            (worker_root / "Main.lean").write_text(text_a)
            command += ["--worker-root", f"a={worker_root}"]
        if args.worker_command_override:
            command += ["--worker-command", 'a=["lean","--server"]']
        if args.lean_cmd:
            command += ["--lean-cmd", args.lean_cmd]
        editor = Editor(command, REPO / "impl/p1", args.timeout)
        try:
            init = editor.response(editor.send("initialize", {
                "processId": os.getpid(), "rootUri": ws_a.as_uri(),
                "workspaceFolders": [{"uri": ws_a.as_uri(), "name": "a"},
                                     {"uri": ws_b.as_uri(), "name": "b"}],
                "capabilities": {"textDocument": {"publishDiagnostics": {"versionSupport": True}}},
            }))
            assert isinstance(init, dict) and "capabilities" in init, init
            editor.send("initialized", {}, request=False)
            for uri, content in ((uri_a, text_a), (uri_b, text_b)):
                editor.send("textDocument/didOpen", {"textDocument": {
                    "uri": uri, "languageId": "lean4", "version": 1, "text": content}}, request=False)
            diagnostic(editor, uri_a, 1)
            diagnostic(editor, uri_b, 1)

            for iteration in range(args.samples):
                bad_version = 2 * iteration + 2
                good_version = bad_version + 1
                bad = text_a.replace("#check alpha", "#check missingParaleanName")
                start = time.monotonic()
                editor.send("textDocument/didChange", {"textDocument": {"uri": uri_a, "version": bad_version},
                            "contentChanges": [{"text": bad}]}, request=False)
                bad_diag = diagnostic(editor, uri_a, bad_version, require_error=True)
                timings.setdefault("edit_to_diagnostics_bad", []).append((time.monotonic() - start) * 1000)
                assert bad_diag["params"]["diagnostics"], bad_diag
                start = time.monotonic()
                editor.send("textDocument/didChange", {"textDocument": {"uri": uri_a, "version": good_version},
                            "contentChanges": [{"text": text_a}]}, request=False)
                good_diag = diagnostic(editor, uri_a, good_version)
                timings.setdefault("edit_to_diagnostics_good", []).append((time.monotonic() - start) * 1000)
                assert not any(d.get("severity") == 1 for d in good_diag["params"]["diagnostics"]), good_diag

                source = editor.response(editor.send("paralean/source", {"uri": uri_a}))
                assert source["workspace"] == "a" and source["version"] == good_version
                assert source["text"] == text_a, source

                doc = {"textDocument": {"uri": uri_a}}
                hover = timed_request(editor, "textDocument/hover", {**doc, "position": {"line": line_shift + 1, "character": 8}}, timings, "hover")
                assert hover is not None, hover
                goal = timed_request(editor, "$/lean/plainGoal", {**doc, "position": {"line": line_shift + 4, "character": 2}}, timings, "goals")
                assert goal is not None, goal
                completion = timed_request(editor, "textDocument/completion", {**doc, "position": {"line": line_shift + 2, "character": 12}}, timings, "completion")
                assert completion is not None, completion
                items = completion.get("items", []) if isinstance(completion, dict) else completion
                assert isinstance(items, list) and items, completion
                if iteration == 0:
                    old_completion_item = items[0]
                    resolved_item = editor.response(editor.send("completionItem/resolve", old_completion_item))
                    assert resolved_item["label"] == old_completion_item["label"], resolved_item

            rename_id = editor.send("textDocument/rename", {
                "textDocument": {"uri": uri_a}, "position": {"line": line_shift + 1, "character": 8},
                "newName": "gamma"})
            refused = editor.take(lambda x: x.get("id") == rename_id)
            assert refused.get("error", {}).get("code") == -32602, refused
            symbols = editor.response(editor.send("workspace/symbol", {"query": "alpha"}))
            assert isinstance(symbols, list), symbols
            second_symbols = editor.response(editor.send("workspace/symbol", {"query": "beta"}))
            assert isinstance(second_symbols, list), second_symbols
            assert any(s.get("name") == "alpha" and s.get("location", {}).get("uri") == uri_a
                       for s in symbols), symbols[:8]
            assert any(s.get("name") == "beta" and s.get("location", {}).get("uri") == uri_b
                       for s in second_symbols), second_symbols[:8]
            virtual_source = editor.response(editor.send("paralean/source", {"uri": uri_b}))
            assert virtual_source["workspace"] == "b" and virtual_source["text"] == text_b
            connect_a = editor.response(editor.send("$/lean/rpc/connect", {"uri": uri_a}))
            connect_b = editor.response(editor.send("$/lean/rpc/connect", {"uri": uri_b}))
            assert connect_a.get("sessionId") != connect_b.get("sessionId"), (connect_a, connect_b)
            old_session = connect_a["sessionId"]
            goal_position = {"line": line_shift + 4, "character": 2}
            valid_rpc = editor.response(editor.send("$/lean/rpc/call", {
                "sessionId": old_session, "textDocument": {"uri": uri_a},
                "position": goal_position, "method": "Lean.Widget.getInteractiveGoals",
                "params": {"textDocument": {"uri": uri_a}, "position": goal_position}}))
            assert isinstance(valid_rpc, dict), valid_rpc
            sibling_file = ws_a / "Sibling.lean"
            sibling_file.write_text("def sibling : Nat := 3\n")
            sibling_uri = sibling_file.as_uri()
            editor.send("textDocument/didOpen", {"textDocument": {"uri": sibling_uri,
                        "languageId": "lean4", "version": 1, "text": sibling_file.read_text()}}, request=False)
            diagnostic(editor, sibling_uri, 1)
            sibling_session = editor.response(editor.send("$/lean/rpc/connect", {"uri": sibling_uri}))
            assert sibling_session["sessionId"] != old_session
            sibling_id = editor.send("$/lean/rpc/call", {
                "sessionId": old_session, "textDocument": {"uri": sibling_uri},
                "position": {"line": 0, "character": 0},
                "method": "Lean.Widget.getInteractiveGoals", "params": {}})
            sibling_mismatch = editor.take(lambda x: x.get("id") == sibling_id)
            assert sibling_mismatch.get("error", {}).get("code") == -32602, sibling_mismatch
            wrong_id = editor.send("$/lean/rpc/call", {
                "sessionId": old_session, "textDocument": {"uri": uri_b},
                "position": {"line": 0, "character": 0},
                "method": "Lean.Widget.getInteractiveGoals", "params": {}})
            wrong_workspace_rpc = editor.take(lambda x: x.get("id") == wrong_id)
            assert wrong_workspace_rpc.get("error", {}).get("code") == -32602, wrong_workspace_rpc
            cancel_id = editor.send("workspace/symbol", {"query": "alpha"})
            editor.send("$/cancelRequest", {"id": cancel_id}, request=False)
            cancelled = editor.take(lambda x: x.get("id") == cancel_id)
            assert cancelled.get("error", {}).get("code") == -32800, cancelled
            # An inactive cancellation must not poison a later request that
            # reuses the same public JSON-RPC ID.
            editor.send("$/cancelRequest", {"id": cancel_id}, request=False)
            editor.next_id = cancel_id
            reused_id = editor.send("textDocument/hover", {
                "textDocument": {"uri": uri_a},
                "position": {"line": line_shift + 1, "character": 8}})
            assert reused_id == cancel_id
            assert editor.response(reused_id) is not None
            if args.kill_worker:
                # The proxy's P4 test hook kills exactly this workspace's Lean process.
                editor.response(editor.send("workspace/executeCommand", {
                    "command": "paralean/killWorker", "arguments": ["a"]}))
                start = time.monotonic()
                editor.send("textDocument/didChange", {"textDocument": {"uri": uri_a, "version": 2 * args.samples + 2},
                            "contentChanges": [{"text": text_a}]}, request=False)
                recovered = diagnostic(editor, uri_a, 2 * args.samples + 2)
                timings.setdefault("reconnect_to_diagnostics", []).append((time.monotonic() - start) * 1000)
                assert not any(d.get("severity") == 1 for d in recovered["params"]["diagnostics"]), recovered
                assert editor.response(editor.send("textDocument/hover", {
                    "textDocument": {"uri": uri_a}, "position": {"line": line_shift + 1, "character": 8}})) is not None
                expired_id = editor.send("$/lean/rpc/call", {
                    "sessionId": old_session, "textDocument": {"uri": uri_a},
                    "position": {"line": 0, "character": 0},
                    "method": "Lean.Widget.getInteractiveGoals", "params": {}})
                expired = editor.take(lambda x: x.get("id") == expired_id)
                assert expired.get("error", {}).get("code") == -32002, expired
                previous_environment = editor.response(editor.send("paralean/source", {"uri": uri_a}))["environment"]
                editor.response(editor.send("workspace/executeCommand", {
                    "command": "paralean/setEnvironment", "arguments": ["a", "test-env-2"]}))
                env_source = editor.response(editor.send("paralean/source", {"uri": uri_a}))
                assert env_source["environment"] != previous_environment, env_source
                assert editor.response(editor.send("textDocument/hover", {
                    "textDocument": {"uri": uri_a}, "position": {"line": line_shift + 1, "character": 8}})) is not None
            edit_session = editor.response(editor.send("$/lean/rpc/connect", {"uri": uri_a}))["sessionId"]
            # Two rapid UTF-16 ranged edits must both reach Lean before an
            # immediately following semantic request; this catches coalescing
            # and request/notification reordering in the proxy.
            latest = 2 * args.samples + (2 if args.kill_worker else 1)
            for version, line, start_char in ((latest + 1, line_shift, 4),
                                              (latest + 2, line_shift + 1, 7)):
                editor.send("textDocument/didChange", {
                    "textDocument": {"uri": uri_a, "version": version},
                    "contentChanges": [{"range": {"start": {"line": line, "character": start_char},
                                                  "end": {"line": line, "character": start_char + 5}},
                                        "text": "theta"}]}, request=False)
            newest = text_a.replace("alpha", "theta")
            hover_after_edits = editor.response(editor.send("textDocument/hover", {
                "textDocument": {"uri": uri_a}, "position": {"line": line_shift + 1, "character": 8}}))
            assert hover_after_edits is not None and "theta" in json.dumps(hover_after_edits), hover_after_edits
            newest_source = editor.response(editor.send("paralean/source", {"uri": uri_a}))
            assert newest_source["version"] == latest + 2 and newest_source["text"] == newest, newest_source
            final_diag = diagnostic(editor, uri_a, latest + 2)
            assert not any(d.get("severity") == 1 for d in final_diag["params"]["diagnostics"]), final_diag
            stale_completion_id = editor.send("completionItem/resolve", old_completion_item)
            stale_completion = editor.take(lambda x: x.get("id") == stale_completion_id)
            assert stale_completion.get("error", {}).get("code") == -32800, stale_completion
            stale_rpc_id = editor.send("$/lean/rpc/call", {
                "sessionId": edit_session, "textDocument": {"uri": uri_a},
                "position": {"line": line_shift + 1, "character": 8},
                "method": "Lean.Widget.getInteractiveGoals", "params": {}})
            stale_rpc = editor.take(lambda x: x.get("id") == stale_rpc_id)
            assert stale_rpc.get("error", {}).get("code") == -32002, stale_rpc
            # No older diagnostic may be delivered after the latest version.
            latest += 2
            latest_received_at = final_diag["_received_at"]
            quiet_until = time.monotonic() + 0.35
            while time.monotonic() < quiet_until:
                try:
                    editor.pending.append(editor.inbox.get(timeout=quiet_until - time.monotonic()))
                except queue.Empty:
                    break
            stale = [m for m in editor.pending if m.get("method") == "textDocument/publishDiagnostics"
                     and m.get("params", {}).get("uri") == uri_a
                     and m.get("params", {}).get("version", latest) < latest
                     and m.get("_received_at", 0) > latest_received_at]
            assert not stale, stale
        finally:
            editor.close()
            deadline = time.monotonic() + 2
            while time.monotonic() < deadline and worker_processes_for(base.name):
                time.sleep(0.05)
            assert not worker_processes_for(base.name), "orphan Lean worker survived proxy exit"
    result = {}
    for key, values in timings.items():
        item = {"n": len(values), "p50_ms": round(percentile(values, 50), 2),
                "p95_ms": round(percentile(values, 95), 2),
                "samples_ms": [round(x, 2) for x in values]}
        if len(values) > 2:
            item.update(first_ms=round(values[0], 2),
                        warm_p50_ms=round(percentile(values[1:], 50), 2),
                        warm_p95_ms=round(percentile(values[1:], 95), 2))
        result[key] = item
    report = {"gate": "pass", "benchmark": args.label,
              "search_counts": {"alpha": len(symbols), "beta": len(second_symbols)},
              "latencies": result}
    print(json.dumps(report, indent=2))
    if args.output:
        Path(args.output).write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-cmd", help="Lean server command; uses proxy default otherwise")
    parser.add_argument("--samples", type=int, default=10)
    parser.add_argument("--timeout", type=float, default=30)
    parser.add_argument("--label", default="Init")
    parser.add_argument("--output")
    parser.add_argument("--kill-worker", action="store_true")
    parser.add_argument("--worker-remap", action="store_true",
                        help="map workspace a to a separate worker filesystem root")
    parser.add_argument("--worker-command-override", action="store_true",
                        help="use per-workspace worker transport argv")
    run(parser.parse_args())
