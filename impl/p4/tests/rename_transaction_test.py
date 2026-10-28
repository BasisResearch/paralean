#!/usr/bin/env python3
"""Two-workspace buffer transaction and fail-closed mutation cases."""

import asyncio
import copy
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from lsp import Proxy, file_uri  # noqa: E402
from rename_transaction import source_digest  # noqa: E402


def edit(uri, old, new, version=1):
    return {"documentChanges": [{"textDocument": {"uri": uri, "version": version},
                                 "edits": [{"range": {"start": {"line": 0, "character": 4},
                                                       "end": {"line": 0, "character": 7}},
                                            "newText": new}]}]}


class FakeWorkspace:
    def __init__(self, proxy, name, root, uri, text, result, definition_uri):
        self.proxy = proxy
        self.name = name
        self.root = root
        self.worker_root = root
        self.environment = "env"
        self.generation = 1
        self.open_documents = {uri: {"version": 1, "text": text, "public_uri": uri}}
        self.result = result
        self.definition = {"result": {"uri": definition_uri,
                                      "range": {"start": {"line": 0, "character": 4},
                                                "end": {"line": 0, "character": 7}}}}
        self.requests = []
        self.pending = {}

    def refresh_environment(self):
        return False

    async def request(self, message, client_id, document=None, expected_version=None):
        self.requests.append(message)
        future = asyncio.get_running_loop().create_future()
        future.set_result(self.definition if message["method"] == "textDocument/definition" else self.result)
        worker_id = len(self.requests)
        self.pending[worker_id] = (client_id, document, expected_version, self.generation,
                                   self.environment, future, None, message["method"])
        return worker_id, future


class FakeBridge:
    def __init__(self, documents):
        self.documents = documents
        self.complete = True
        self.observed = []
        self.policy_ready = {"a", "b"}
        self.policy_fresh = True

    def rename_inventory(self):
        return {"complete": self.complete, "documents": copy.deepcopy(self.documents), "missing": []}

    def observe(self, ws, uri, method):
        self.observed.append((ws.name, uri, method))

    async def assert_policy_fresh(self, workspaces):
        if not self.policy_fresh:
            raise ValueError("Authoritative store policy changed")


class PublishingBridge(FakeBridge):
    """A controller bridge that publishes published declarations as one batch."""

    def __init__(self, documents, workspaces):
        super().__init__(documents)
        self.workspaces = workspaces
        self.publications = []
        self.refusal = None
        self.outcome = {"outcome": "committed", "batch": "b" * 64}

    async def publish_rename(self, affected, planned, group):
        # Buffers must still be unchanged while the batch is published.
        self.publications.append((sorted(affected), group, [ws.open_documents[uri]["text"] for ws in self.workspaces
                                                            for uri in ws.open_documents]))
        if self.refusal is not None:
            raise self.refusal
        return self.outcome


class TransactionTests(unittest.IsolatedAsyncioTestCase):
    async def asyncSetUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        root = Path(self.temp.name).resolve()
        (root / "a").mkdir()
        (root / "b").mkdir()
        self.proxy = Proxy({}, ["unused"])
        self.uri_a = file_uri(root / "a" / "A.lean")
        self.uri_b = file_uri(root / "b" / "B.lean")
        self.a = FakeWorkspace(self.proxy, "a", root / "a", self.uri_a, "def old := 1\n",
                               {"result": edit(self.uri_a, "old", "new")}, self.uri_a)
        self.b = FakeWorkspace(self.proxy, "b", root / "b", self.uri_b, "use old\n",
                               {"result": edit(self.uri_b, "old", "new")}, self.uri_a)
        self.proxy.workspaces = {"a": self.a, "b": self.b}
        documents = [
            {"workspace": "a", "uri": self.uri_a, "version": 1, "environment": "env",
             "generation": 1, "source_sha256": source_digest("def old := 1\n"),
             "groups": [{"group": "g-old", "pid": "p-old", "capsule": "c-old", "names": ["old"], "line": 1, "deps": []}]},
            {"workspace": "b", "uri": self.uri_b, "version": 1, "environment": "env",
             "generation": 1, "source_sha256": source_digest("use old\n"),
             "groups": [{"group": "g-use", "pid": "p-use", "capsule": "c-use", "names": ["use"], "line": 1, "deps": ["p-old"]}]},
        ]
        self.bridge = FakeBridge(documents)
        self.proxy.bridge = self.bridge
        self.sent = []
        async def send(message):
            self.sent.append(message)
        async def replay(*args):
            pass
        self.proxy.send = send
        self.proxy.deliver_change = replay
        self.message = {"id": 7, "params": {"uri": self.uri_a,
                        "position": {"line": 0, "character": 5}, "group": "g-old",
                        "newName": "new", "anchors": [
                            {"uri": self.uri_a, "position": {"line": 0, "character": 5}},
                            {"uri": self.uri_b, "position": {"line": 0, "character": 5}}]}}

    def assert_unchanged(self):
        self.assertEqual(self.a.open_documents[self.uri_a]["text"], "def old := 1\n")
        self.assertEqual(self.b.open_documents[self.uri_b]["text"], "use old\n")
        self.assertEqual(self.a.open_documents[self.uri_a]["version"], 1)
        self.assertEqual(self.b.open_documents[self.uri_b]["version"], 1)
        self.assertEqual(self.sent[-1].get("error", {}).get("code"), -32800)

    async def test_two_workspace_commit(self):
        await self.proxy.rename_transaction(self.message)
        self.assertEqual(self.a.open_documents[self.uri_a]["text"], "def new := 1\n")
        self.assertEqual(self.b.open_documents[self.uri_b]["text"], "use new\n")
        self.assertEqual([self.a.open_documents[self.uri_a]["version"],
                          self.b.open_documents[self.uri_b]["version"]], [2, 2])
        self.assertEqual(len(self.sent[0]["params"]["documents"]), 2)
        self.assertIn("result", self.sent[1])

    async def test_duplicate_identical_cross_worker_edit_commits_once(self):
        self.b.result["result"]["documentChanges"].append(edit(self.uri_a, "old", "new")["documentChanges"][0])
        await self.proxy.rename_transaction(self.message)
        self.assertEqual(self.a.open_documents[self.uri_a]["text"], "def new := 1\n")
        self.assertEqual(self.a.open_documents[self.uri_a]["version"], 2)

    async def test_disagreeing_cross_worker_edit_refuses_all(self):
        self.b.result["result"]["documentChanges"].append(edit(self.uri_a, "old", "other")["documentChanges"][0])
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()

    async def test_incomplete_inventory_refuses_all(self):
        self.bridge.complete = False
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()

    async def test_standalone_reference_outside_captured_groups_refuses_all(self):
        uri = file_uri(self.b.root / "Check.lean")
        self.b.open_documents[uri] = {"version": 1, "text": "#check old\n", "public_uri": uri}
        self.bridge.documents.append({"workspace": "b", "uri": uri, "version": 1,
                                      "environment": "env", "generation": 1,
                                      "source_sha256": source_digest("#check old\n"), "groups": []})
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()
        self.assertEqual(self.b.open_documents[uri]["text"], "#check old\n")

    async def test_standard_rename_without_bridge_refuses_in_multiworkspace(self):
        self.proxy.bridge = None
        await self.proxy.dispatch({"jsonrpc": "2.0", "id": 8,
                                   "method": "textDocument/rename",
                                   "params": {"textDocument": {"uri": self.uri_a},
                                              "position": {"line": 0, "character": 5},
                                              "newName": "new"}})
        for _ in range(10):
            if self.sent:
                break
            await asyncio.sleep(0)
        self.assertTrue(self.sent and "error" in self.sent[-1])
        self.assertEqual(self.sent[-1]["error"]["code"], -32602)
        self.assertEqual(self.a.open_documents[self.uri_a]["text"], "def old := 1\n")
        self.assertEqual(self.b.open_documents[self.uri_b]["text"], "use old\n")

    async def test_uncaptured_dependency_refuses_all(self):
        self.bridge.documents[1]["source_sha256"] = "stale"
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()

    async def test_generation_change_refuses_all(self):
        self.b.generation += 1
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()

    async def test_missing_anchor_refuses_all(self):
        self.message["params"]["anchors"].pop()
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()

    async def test_origin_anchor_mismatch_refuses_all(self):
        self.message["params"]["anchors"][0]["position"]["character"] = 6
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()

    async def test_rejected_worker_refuses_all(self):
        self.b.result = {"error": {"code": -1, "message": "no rename"}}
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()

    async def test_worker_omits_dependent_source_refuses_all(self):
        self.b.result = {"result": {"changes": {}}}
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()

    async def test_worker_omits_second_dependent_document_refuses_all(self):
        uri = file_uri(self.b.root / "Other.lean")
        source = "use old\n"
        self.b.open_documents[uri] = {"version": 1, "text": source, "public_uri": uri}
        self.bridge.documents.append({"workspace": "b", "uri": uri, "version": 1,
                                      "environment": "env", "generation": 1,
                                      "source_sha256": source_digest(source),
                                      "groups": [{"group": "g-other", "pid": "p-other", "capsule": "c-other",
                                                  "names": ["other"], "line": 1, "deps": ["p-old"]}]})
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()
        self.assertEqual(self.b.open_documents[uri]["text"], source)

    async def test_out_of_scope_edit_refuses_all(self):
        self.b.result = {"result": edit(file_uri(self.b.root / "Other.lean"), "old", "new")}
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()

    async def test_overlapping_edits_refuse_all(self):
        self.b.result["result"]["documentChanges"][0]["edits"] *= 2
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()

    async def test_ambiguous_worker_plan_refuses_all(self):
        edits = self.b.result["result"]["documentChanges"][0]["edits"]
        self.b.result["result"]["changes"] = {self.uri_b: edits}
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()

    async def test_stale_worker_edit_version_refuses_all(self):
        self.b.result["result"]["documentChanges"][0]["textDocument"]["version"] = 0
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()

    async def test_worker_edits_other_token_in_same_source_refuses_all(self):
        self.b.result["result"]["documentChanges"][0]["edits"][0]["range"] = {
            "start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 3}}
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()

    async def test_dependent_anchor_resolves_to_other_group_refuses_all(self):
        self.b.definition["result"]["range"]["start"]["character"] = 0
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()

    async def test_origin_definition_misses_captured_member_refuses_all(self):
        self.bridge.documents[0]["groups"][0]["names"] = ["different"]
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()

    async def test_changed_inventory_during_planning_refuses_all(self):
        original = self.b.request
        async def request(*args, **kwargs):
            result = await original(*args, **kwargs)
            self.bridge.documents[1]["groups"][0]["deps"] = []
            return result
        self.b.request = request
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()

    async def test_environment_changes_during_planning_refuses_all(self):
        original = self.b.request
        async def request(*args, **kwargs):
            result = await original(*args, **kwargs)
            self.b.environment = "changed"
            return result
        self.b.request = request
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()

    async def test_cancellation_after_worker_plans_refuses_all(self):
        original = self.b.request
        async def request(*args, **kwargs):
            result = await original(*args, **kwargs)
            if args[0]["method"] == "textDocument/rename":
                self.proxy.cancelled.add(7)
            return result
        self.b.request = request
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()

    async def test_policy_changes_during_planning_refuses_all(self):
        original = self.b.request
        async def request(*args, **kwargs):
            result = await original(*args, **kwargs)
            if args[0]["method"] == "textDocument/rename":
                self.bridge.policy_fresh = False
            return result
        self.b.request = request
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()

    def publish_bridge(self):
        for doc in self.bridge.documents:
            for record in doc["groups"]:
                record["alreadyPublished"] = True
        bridge = PublishingBridge(self.bridge.documents, [self.a, self.b])
        self.proxy.bridge = self.bridge = bridge
        return bridge

    async def renamed(self):
        """Run the rename; a refusal must come back as an error reply, never escape."""
        try:
            await self.proxy.rename_transaction(self.message)
        except Exception as exc:  # noqa: BLE001 - recorded, then asserted below
            self.sent.append({"escaped": repr(exc)})
        self.assertTrue(self.sent, "no reply")

    async def test_published_rename_commits_buffers_after_atomic_publication(self):
        bridge = self.publish_bridge()
        await self.renamed()
        self.assertEqual(bridge.publications, [([("a", self.uri_a), ("b", self.uri_b)], "g-old",
                                                ["def old := 1\n", "use old\n"])])
        self.assertEqual(self.a.open_documents[self.uri_a]["text"], "def new := 1\n")
        self.assertEqual(self.b.open_documents[self.uri_b]["text"], "use new\n")
        self.assertEqual(self.sent[-1]["result"]["publication"]["outcome"], "committed")

    async def test_refused_publication_keeps_every_buffer(self):
        self.publish_bridge().refusal = RuntimeError("store refused the batch: not the owner of P5.goal")
        await self.renamed()
        self.assert_unchanged()
        self.assertIn("not the owner", self.sent[-1]["error"]["message"])

    async def test_unresolved_publication_keeps_every_buffer(self):
        self.publish_bridge().refusal = RuntimeError("batch publication outcome unresolved")
        await self.renamed()
        self.assert_unchanged()
        self.assertIn("unresolved", self.sent[-1]["error"]["message"])

    async def test_published_rename_without_batch_support_refuses(self):
        for doc in self.bridge.documents:
            doc["groups"][0]["alreadyPublished"] = True
        await self.renamed()
        self.assert_unchanged()

    async def test_publication_without_committed_batch_refuses(self):
        self.publish_bridge().outcome = None
        await self.renamed()
        self.assert_unchanged()

    async def test_unpublished_rename_does_not_publish(self):
        bridge = PublishingBridge(self.bridge.documents, [self.a, self.b])
        self.proxy.bridge = bridge
        await self.renamed()
        self.assertEqual(bridge.publications, [])
        self.assertNotIn("publication", self.sent[-1]["result"])
        self.assertEqual(self.b.open_documents[self.uri_b]["text"], "use new\n")

    async def test_policy_probe_mutates_generation_refuses_all(self):
        async def probe(workspaces):
            await asyncio.sleep(0)
            self.b.generation += 1
        self.bridge.assert_policy_fresh = probe
        await self.proxy.rename_transaction(self.message)
        self.assert_unchanged()


if __name__ == "__main__":
    unittest.main()
