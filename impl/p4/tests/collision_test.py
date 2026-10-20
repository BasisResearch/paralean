#!/usr/bin/env python3
"""Exercise the guided OPEN-26 tombstone and certified post-collision snapshot.

This publishes one tombstone to the configured *own* cluster. Use a completed P3
gate fixture and a dedicated PARALEAN_INSTANCE; do not run against a shared copy.
"""

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


SCRIPT = Path(__file__).resolve().parents[1] / "workspace.py"


def call(*argv, env):
    p = subprocess.run([str(x) for x in argv], env=env, capture_output=True, text=True)
    if p.returncode:
        raise AssertionError(f"{argv}: {p.stdout[-1200:]} {p.stderr[-2000:]}")
    return json.loads(p.stdout.strip().splitlines()[-1])


def git(work, *args):
    p = subprocess.run(["git", "-C", str(work), *args], capture_output=True, text=True)
    if p.returncode:
        raise AssertionError(p.stderr)
    return p.stdout.strip()


def main(args):
    source = args.copy.resolve()
    env = dict(os.environ)
    assert env.get("PARALEAN_INSTANCE"), "set an isolated PARALEAN_INSTANCE first"
    manifest_path = source.parent / "manifest.json"
    manifest = json.loads(manifest_path.read_text()) if manifest_path.is_file() else None
    env["PARALEAN_TRUST"] = manifest["trust"] if manifest else str(source.parent / "trust.json")
    env["PARALEAN_DEPLOYMENT"] = (manifest["deployment"] if manifest else
                                  (source.parent / "deployment").read_text().strip())
    with tempfile.TemporaryDirectory(prefix="paralean-p4-collision-") as temp:
        target = Path(temp) / "copy"
        shutil.copytree(source, target)
        env["PARALEAN_KEYS"] = str(target / "keys.json")
        env["PARALEAN_STORE"] = str(target / "cache")
        if manifest:
            raw = manifest["renamed"]
        else:
            diagnostic_text = (source / "diagnostics.log").read_text()
            matches = [name for name in re.findall(r"it is now `([^`]+)`", diagnostic_text)
                       if name.startswith("Shared.dup")]
            assert matches, diagnostic_text[-1500:]
            raw = matches[-1]
        suffix = re.search(r"✝pl([0-9a-f]{8})", raw)
        assert suffix, raw
        losing_prefix = suffix.group(1)
        before = (target / "work/Shared.lean").read_text()
        assert f"dup✝pl{losing_prefix}" in before and f"-- paralean:published {losing_prefix}" in before
        if args.resume:
            # Resume after an earlier guided tombstone succeeded but a later
            # checkpoint step failed; never publish a duplicate tombstone.
            call(env["PARALEAN_PLR"], "pull", "--cache", target / "cache", env=env)
            call(env["PARALEAN_BIN"], "ws-sync", "--dir", target, env=env)
            heads = call(env["PARALEAN_BIN"], "ws-live", env=env)
            result = {"resolution": "already-tombstoned", "target": losing_prefix,
                      "revisions": heads["revisions"],
                      "checkpointArgs": ["checkpoint", "--cache", str(target / "cache"),
                                         "--ws", "bob", "--revisions", ",".join(heads["revisions"])]}
        else:
            result = call("python3", SCRIPT, "resolve", target, "Shared.lean", raw, env=env)
            assert result["resolution"] == "tombstone" and result["target"].startswith(losing_prefix), result
        after = (target / "work/Shared.lean").read_text()
        assert f"-- paralean:published {losing_prefix}" not in after, after
        assert "theorem Shared.dup" in after, after
        # The editor draft that mentioned the losing declaration is now revised
        # by its author, then checked before making the certified checkpoint.
        revised = re.sub(r"example : 3 = 3 := Shared\.\u00abdup\u271dpl[0-9a-f]{8}\u00bb",
                         "example : 3 = 3 := by decide", after)
        (target / "work/Shared.lean").write_text(revised)
        checked = call(env["PARALEAN_BIN"], "ws-check", "--dir", target, "Shared.lean", env=env)
        assert not checked.get("errors"), checked
        marker_records = [json.loads(path.read_text())
                          for path in (target / "cache/p3/records").glob("m-*.json")]
        losing_records = [record for record in marker_records
                          if record["group"].startswith(losing_prefix)]
        assert len(losing_records) == 1, losing_records
        heads = call(env["PARALEAN_BIN"], "ws-live", env=env)
        if args.resume:
            assert set(heads["revisions"]) == set(result["revisions"]), (heads, result)
        assert set(losing_records[0]["revisions"]).isdisjoint(heads["revisions"]), result
        # The P3 adversarial gate also leaves a forged Bad.lean group live.
        # This checkpoint certifies the checked Shared.lean resolution only.
        shared = [record for record in marker_records
                  if record["group"] in heads["groups"] and record["file"] == "Shared.lean"]
        assert shared and any("dup" in str(record.get("lineageKeys")) for record in shared), shared
        revisions = sorted({rev for record in shared for rev in record["revisions"]})
        if not args.resume:
            assert result["checkpointFiles"] == ["Shared.lean"], result
            assert result["revisions"] == revisions, result
        bad_revisions = {rev for record in marker_records if record["file"] == "Bad.lean"
                         for rev in record["revisions"]}
        assert set(revisions).isdisjoint(bad_revisions), revisions
        checkpoint_env = dict(env, PARALEAN_KEYS=(manifest["keys"] if manifest else
                                                  str(source.parent / "keys.json")))
        checkpoint = call(env["PARALEAN_PLR"], "checkpoint", "--cache", target / "cache",
                          "--ws", "bob", "--revisions", ",".join(revisions), env=checkpoint_env)
        projected = call("python3", SCRIPT, "project", target, env=env)
        snapshot = call("python3", SCRIPT, "snapshot", target, "--workspace", "bob",
                        "--catalog", checkpoint["catalog"], env=env)
        certified = git(target / "work", "show", f"{snapshot['tag']}:Shared.lean")
        assert f"dup✝pl{losing_prefix}" not in certified, certified
        assert "Shared.dup" in certified, certified
        assert "Bad.lean" not in git(target / "work", "ls-tree", "-r", "--name-only", snapshot["tag"])
        with tempfile.TemporaryDirectory(prefix="paralean-p4-certified-lean-") as checkdir:
            compiled = Path(checkdir) / "Shared.lean"
            compiled.write_text(certified)
            check_env = dict(env, LEAN_PARALEAN="0")
            check_env.pop("PARALEAN_STORE", None)
            subprocess.run(["lean", str(compiled)], env=check_env, check=True,
                           capture_output=True, text=True)
        assert projected["added"] >= 1
        print(json.dumps({"gate": "pass", "tombstone": result["target"],
                          "checkpoint": checkpoint["catalog"], "snapshot": snapshot["snapshot"],
                          "projectionAdded": projected["added"],
                          "checkedRevisions": revisions}, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("copy", type=Path, help="completed P3 gate losing working copy")
    parser.add_argument("--resume", action="store_true",
                        help="resume after a previously successful tombstone without publishing it twice")
    main(parser.parse_args())
