#!/usr/bin/env python3
"""ws.py publish never writes through links planted in the working copy (W2-20)."""

import importlib.util, json, os, sys, tempfile, unittest
from pathlib import Path
from unittest.mock import patch

GROUP = "1" * 64
CAPSULE = "2" * 64


def load_ws():
    with patch.dict(os.environ, {"PARALEAN_BIN": "lean-bin", "PARALEAN_PLR": "plr"}):
        spec = importlib.util.spec_from_file_location("ws", Path(__file__).with_name("ws.py"))
        ws = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(ws)
    return ws


class PublishStagingTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name).resolve()
        self.d = self.root / "copy"
        self.d.mkdir()
        self.sentinels = {}
        for name in ("receipt.json", "plan.json", "plan-targets.json"):
            sentinel = self.root / ("outside-" + name)
            sentinel.write_text("outside sentinel")
            (self.d / name).symlink_to(sentinel)
            self.sentinels[name] = sentinel
        self.ws = load_ws()
        self.calls = {}

    def fake_run(self, cmd, d, file=None, check=True):
        verb = cmd[1]
        if verb == "ws-capture":
            return {"packages": [{"group": GROUP, "capsule": CAPSULE, "names": ["T.x"], "deps": []}],
                    "rejected": 0}
        if verb == "target-get":
            return {"exists": True}
        if verb == "validate":
            return {"accepted": True, "targets": ["T.x:" + "b" * 64], "ms": 1}
        if verb == "ws-plan":
            receipt = Path(cmd[cmd.index("--receipts") + 1])
            out = Path(cmd[cmd.index("--out") + 1])
            self.calls["receipt"] = receipt
            self.calls["receipt_text"] = receipt.read_text()
            # Like the Lean binary, an ordinary file write follows symlinks.
            out.write_text(json.dumps([{"group": GROUP}, {"group": "3" * 64}]))
            return {"planned": 2}
        if verb == "publish":
            plan = Path(cmd[cmd.index("--plan") + 1])
            self.calls["plan"] = plan
            self.calls["plan_entries"] = json.loads(plan.read_text())
            return {"ok": True}
        return {}

    def publish(self, env):
        env = {"PARALEAN_AGENT": "alice", "PARALEAN_VALIDATOR": "127.0.0.1:1", "PARALEAN_NO_PULL": "1", **env}
        with patch.dict(os.environ, env), patch.object(self.ws, "run", self.fake_run), \
                patch.object(self.ws, "emit", lambda step, obj: None):
            os.environ.pop("PARALEAN_TARGETS", None)
            if "PARALEAN_CONTROLLER" not in env:
                os.environ.pop("PARALEAN_CONTROLLER", None)
            return self.ws.publish(str(self.d), "A.lean")

    def check_staged(self):
        for name, sentinel in self.sentinels.items():
            self.assertEqual(sentinel.read_text(), "outside sentinel", name)
            self.assertTrue((self.d / name).is_symlink(), name)
        self.assertEqual(json.loads(self.calls["receipt_text"])["accepted"], True)
        for path in (self.calls["receipt"], self.calls["plan"]):
            self.assertNotIn(self.d, path.parents)
            self.assertFalse(path.exists(), "staging directory was not removed")

    def test_publish_does_not_follow_planted_links(self):
        self.assertEqual(self.publish({}), [GROUP])
        self.check_staged()
        self.assertEqual(len(self.calls["plan_entries"]), 2)

    def test_target_publish_does_not_follow_planted_links(self):
        self.assertEqual(self.publish({"PARALEAN_CONTROLLER": "127.0.0.1:2"}), [GROUP])
        self.check_staged()
        self.assertEqual(self.calls["plan_entries"][0]["targets"], ["T.x:" + "b" * 64])


if __name__ == "__main__":
    unittest.main()
