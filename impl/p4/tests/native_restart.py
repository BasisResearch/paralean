#!/usr/bin/env python3
"""Kill Lean's file worker while its watchdog and the editor remain alive.

Requires the Paralean fork patch that emits `$/paralean/fileWorkerStarted`.
The test only signals a `lean --worker` descendant of its own LSP subprocess.
"""

import argparse
import os
from pathlib import Path
import signal
import sys
import tempfile
import time

from editor import Editor


REPO = Path(__file__).resolve().parents[3]


def descendants(root):
    processes = {}
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        try:
            stat = (entry / "stat").read_text().rsplit(")", 1)[1].split()
            processes[int(entry.name)] = (int(stat[1]), (entry / "cmdline").read_bytes().replace(b"\0", b" ").decode(errors="replace"))
        except (OSError, IndexError, ValueError):
            continue
    children = {root}
    for _ in range(8):
        children.update(pid for pid, (parent, _) in processes.items() if parent in children)
    return [(pid, processes[pid][1]) for pid in children if pid in processes and pid != root]


def main(args):
    library = Path(os.environ["PARALEAN_LIB"]).resolve()
    assert (library / "Paralean/Visibility.olean").is_file(), library
    os.environ["LEAN_PARALEAN"] = "1"
    os.environ["LEAN_PATH"] = os.pathsep.join(
        part for part in (str(library), os.environ.get("LEAN_PATH", "")) if part)
    with tempfile.TemporaryDirectory(prefix="paralean-native-worker-") as temp:
        root = Path(temp)
        path = root / "Main.lean"
        source = "def alpha : Nat := 1\n#check alpha\n"
        path.write_text(source)
        uri = path.as_uri()
        editor = Editor([sys.executable, str(REPO / "impl/p4/lsp.py"), "--workspace", f"a={root}"],
                        root, args.timeout)
        try:
            editor.response(editor.send("initialize", {"processId": os.getpid(),
                "rootUri": root.as_uri(), "capabilities": {}}))
            editor.send("initialized", {}, request=False)
            editor.send("textDocument/didOpen", {"textDocument": {
                "uri": uri, "languageId": "lean4", "version": 1, "text": source}}, request=False)
            editor.response(editor.send("textDocument/waitForDiagnostics", {"uri": uri, "version": 1}))
            before = editor.response(editor.send("paralean/source", {"uri": uri}))["generation"]
            session = editor.response(editor.send("$/lean/rpc/connect", {"uri": uri}))["sessionId"]
            deadline = time.monotonic() + args.timeout
            workers = []
            while time.monotonic() < deadline:
                workers = [(pid, cmd) for pid, cmd in descendants(editor.process.pid)
                           if "lean" in cmd and "--worker" in cmd and "Main.lean" in cmd]
                if workers:
                    break
                time.sleep(0.1)
            assert len(workers) == 1, workers
            os.kill(workers[0][0], signal.SIGKILL)
            changed_source = source.replace("Nat := 1", "Bool := true")
            editor.send("textDocument/didChange", {"textDocument": {"uri": uri, "version": 2},
                        "contentChanges": [{"text": changed_source}]}, request=False)
            deadline = time.monotonic() + args.timeout
            while time.monotonic() < deadline:
                current = editor.response(editor.send("paralean/source", {"uri": uri}))
                if current["generation"] > before:
                    break
                time.sleep(0.1)
            else:
                raise AssertionError("native file-worker death did not fence proxy generation; "
                                     + editor.stderr[-4000:].decode(errors="replace"))
            editor.response(editor.send("textDocument/waitForDiagnostics", {"uri": uri, "version": 2}))
            hover = editor.response(editor.send("textDocument/hover", {
                "textDocument": {"uri": uri}, "position": {"line": 1, "character": 8}}))
            assert "Bool" in str(hover), hover
            old_id = editor.send("$/lean/rpc/call", {
                "sessionId": session, "textDocument": {"uri": uri},
                "position": {"line": 1, "character": 8},
                "method": "Lean.Widget.getInteractiveGoals", "params": {}})
            old = editor.take(lambda x: x.get("id") == old_id)
            assert old.get("error", {}).get("code") == -32002, old
            print(f"PASS native file-worker death: generation {before} -> {current['generation']}, editor buffer replayed")
        finally:
            editor.close()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=float, default=30)
    main(parser.parse_args())
