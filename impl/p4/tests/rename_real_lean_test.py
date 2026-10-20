#!/usr/bin/env python3
"""Exercise the buffer transaction with two real Lean LSP workers.

The dependency inventory is supplied by this fixture. The source and worker
definition/rename plans are real Lean outputs; a P3 published dependency gate
is separate because this fixture imports a compiled local module.
"""

import asyncio
import copy
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "impl/p4"))
from lsp import Proxy, Workspace, file_uri  # noqa: E402
from rename_transaction import source_digest  # noqa: E402


class Inventory:
    def __init__(self, documents):
        self.documents = documents
        self.policy_ready = {"a", "b"}
        self.policy_events = {name: asyncio.Event() for name in self.policy_ready}
        for event in self.policy_events.values():
            event.set()
        self.complete = True

    def rename_inventory(self):
        return {"complete": self.complete, "documents": copy.deepcopy(self.documents), "missing": []}

    def observe(self, ws, uri, method):
        pass


class RealLeanRenameTests(unittest.IsolatedAsyncioTestCase):
    async def exercise(self, mode):
        lean = ROOT / ".deps/lean4-paralean/build/release/stage1/bin/lean"
        if not lean.is_file():
            self.skipTest("P4 Lean fork is not built")
        with tempfile.TemporaryDirectory(prefix="paralean-rename-real-") as temp:
            root = Path(temp).resolve()
            a, b = root / "a", root / "b"
            a.mkdir()
            b.mkdir()
            source_a = "def old : Nat := 1\ndef localUse : Nat := old + 1\n"
            source_b = "import A\ndef use : Nat := old + 1\n"
            (a / "A.lean").write_text(source_a)
            (b / "B.lean").write_text(source_b)
            env = {**os.environ, "LEAN_PATH": str(a), "LEAN_SRC_PATH": str(a)}
            compile_result = subprocess.run([str(lean), "-o", "A.olean", "-i", "A.ilean", "A.lean"],
                                            cwd=a, env=env, capture_output=True, text=True)
            self.assertEqual(compile_result.returncode, 0, compile_result.stderr)
            proxy = Proxy({}, [str(lean), "--server"])
            proxy.initialize = {"jsonrpc": "2.0", "id": 1, "method": "initialize",
                                "params": {"processId": os.getpid(), "capabilities": {}}}
            sent = []
            async def send(message):
                sent.append(message)
            proxy.send = send
            uris = {"a": file_uri(a / "A.lean"), "b": file_uri(b / "B.lean")}
            for name, work, text in (("a", a, source_a), ("b", b, source_b)):
                overrides = {"PARALEAN_STORE": str(work / "cache"), "PARALEAN_WORK_ROOT": str(work),
                             "LEAN_PATH": str(a), "LEAN_SRC_PATH": str(a)}
                (work / "cache").mkdir()
                ws = Workspace(proxy, name, work, "local", overrides)
                ws.open_documents[uris[name]] = {"version": 1, "text": text, "public_uri": uris[name]}
                proxy.workspaces[name] = ws
            documents = []
            for name, text, groups in (
                ("a", source_a, [{"group": "g-old", "pid": "p-old", "capsule": "c-old",
                                   "names": ["old"], "line": 1, "deps": []}]),
                ("b", source_b, [{"group": "g-use", "pid": "p-use", "capsule": "c-use",
                                   "names": ["use"], "line": 2, "deps": ["p-old"]}])):
                ws = proxy.workspaces[name]
                documents.append({"workspace": name, "uri": uris[name], "version": 1,
                                  "environment": ws.environment, "generation": 1,
                                  "source_sha256": source_digest(text), "groups": groups})
            proxy.bridge = Inventory(documents)
            if mode == "incomplete":
                proxy.bridge.complete = False
            try:
                for name in ("a", "b"):
                    ws = proxy.workspaces[name]
                    await ws.start()
                    await asyncio.wait_for(ws.ready.wait(), 15)
                    documents[0 if name == "a" else 1]["generation"] = ws.generation
                    wait = {"jsonrpc": "2.0", "method": "textDocument/waitForDiagnostics",
                            "params": {"uri": proxy.to_worker_uri(ws, uris[name]), "version": 1}}
                    _, future = await ws.request(wait, 100 + len(name), uris[name], expected_version=1)
                    await asyncio.wait_for(future, 20)
                message = {"id": 7, "params": {"uri": uris["a"], "group": "g-old", "newName": "new",
                           "position": {"line": 1, "character": 23},
                           "anchors": [{"uri": uris["a"], "position": {"line": 1, "character": 23}},
                                       {"uri": uris["b"], "position": {"line": 1, "character": 18}}]}}
                if mode == "wrong-anchor":
                    message["params"]["anchors"][1]["position"] = {"line": 1, "character": 5}
                await proxy.rename_transaction(message)
                if mode == "success":
                    self.assertIn("result", sent[-1], sent)
                    self.assertEqual(proxy.workspaces["a"].open_documents[uris["a"]]["text"],
                                     source_a.replace("old", "new"))
                    self.assertEqual(proxy.workspaces["b"].open_documents[uris["b"]]["text"],
                                     source_b.replace("old", "new"))
                    self.assertEqual(len(sent[-1]["result"]["documents"]), 2)
                else:
                    self.assertIn("error", sent[-1], sent)
                    self.assertEqual(proxy.workspaces["a"].open_documents[uris["a"]]["text"], source_a)
                    self.assertEqual(proxy.workspaces["b"].open_documents[uris["b"]]["text"], source_b)
                    self.assertEqual(proxy.workspaces["a"].open_documents[uris["a"]]["version"], 1)
                    self.assertEqual(proxy.workspaces["b"].open_documents[uris["b"]]["version"], 1)
            finally:
                proxy.stopping = True
                for ws in proxy.workspaces.values():
                    ws.stop_process()
                for ws in proxy.workspaces.values():
                    if ws.process is not None:
                        await asyncio.wait_for(ws.process.wait(), 5)
                    if ws.reader_task is not None:
                        await asyncio.wait_for(ws.reader_task, 5)

    async def test_two_real_workers_commit_declaration_and_imported_use(self):
        await self.exercise("success")

    async def test_wrong_dependent_anchor_keeps_both_buffers(self):
        await self.exercise("wrong-anchor")

    async def test_incomplete_inventory_keeps_both_buffers(self):
        await self.exercise("incomplete")


if __name__ == "__main__":
    unittest.main()
