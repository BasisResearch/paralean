#!/usr/bin/env python3
"""Real-record Git projection and snapshot gate over a P3 working-copy fixture.

Provide a completed P3 gate's `bob` directory and its certified snapshot catalog.
The fixture is copied before mutation, so the running workspace is untouched.
"""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


SCRIPT = Path(__file__).resolve().parents[1] / "workspace.py"
sys.path.insert(0, str(SCRIPT.parent))
from workspace import records, render  # noqa: E402


def command(*args, env=None):
    p = subprocess.run([str(a) for a in args], capture_output=True, text=True, env=env)
    if p.returncode:
        raise AssertionError(f"{args}: {p.stdout[-1200:]} {p.stderr[-2000:]}")
    return p.stdout.strip()


def tool(directory, *args, env):
    return json.loads(command("python3", SCRIPT, *args[:1], directory, *args[1:], env=env))


def git(work, *args):
    return command("git", "-C", work, *args)


def main(args):
    source = args.copy.resolve()
    assert (source / "cache/p3/records").is_dir(), source
    env = dict(os.environ)
    env.setdefault("PARALEAN_TRUST", str(source.parent / "trust.json"))
    env.setdefault("PARALEAN_DEPLOYMENT", (source.parent / "deployment").read_text().strip())
    with tempfile.TemporaryDirectory(prefix="paralean-p4-projection-") as temporary:
        target = Path(temporary) / "copy"
        shutil.copytree(source, target, ignore=shutil.ignore_patterns(".git", "projection"))
        work = target / "work"
        git(work, "init", "-q")
        git(work, "config", "user.name", "Fixture User")
        git(work, "config", "user.email", "fixture@paralean.invalid")
        git(work, "add", ".")
        git(work, "commit", "-qm", "working copy seed")
        draft = work / "Shared.lean"
        draft.write_text(draft.read_text() + "\n-- uncommitted editor draft\n")
        head = git(work, "rev-parse", "HEAD")
        status = git(work, "status", "--porcelain=v1")
        records_dir = target / "cache/p3/records"
        entries = []
        for path in records_dir.glob("*.json"):
            if path.name.startswith(("m-", "t-")):
                record = json.loads(path.read_text())
                entries.append((record["lamport"], record["author"], record["id"], path))
        entries.sort()
        assert len(entries) >= 3, "fixture needs at least three published records"
        parked = target / "parked-records"
        parked.mkdir()
        retained = {entries[0][3].name, entries[2][3].name}
        for _, _, _, path in entries:
            if path.name in retained:
                continue
            path.rename(parked / path.name)
        first = tool(target, "project", env=env)
        assert first["added"] == 2, first
        prefix_head = first["commit"]
        late = parked / entries[1][3].name
        late.rename(records_dir / late.name)
        second = tool(target, "project", env=env)
        assert second["added"] == 1 and second["commit"] != prefix_head, second
        assert git(work, "merge-base", "--is-ancestor", prefix_head, second["commit"]) == ""
        for path in parked.iterdir():
            path.rename(records_dir / path.name)
        final = tool(target, "project", env=env)
        assert final["records"] == len(entries) and final["added"] == len(entries) - 3, final
        repeated = tool(target, "project", env=env)
        assert repeated["added"] == 0 and repeated["commit"] == final["commit"], repeated
        assert git(work, "rev-parse", "HEAD") == head
        assert git(work, "status", "--porcelain=v1") == status
        assert "uncommitted editor draft" in draft.read_text()
        projected = git(work, "show", "paralean/projection:Shared.lean")
        assert "uncommitted editor draft" not in projected
        assert "theorem Shared.dup" in projected and "by decide" in projected
        assert "remote%" not in projected and "remote_decl%" not in projected
        assert "-- paralean:published" not in projected
        ordered = records(target / "cache")
        forward = render(target / "cache", ordered, env)
        reverse = render(target / "cache", list(reversed(ordered)), env)
        assert forward == reverse, "full source projection depends on delivery order"
        snapshot = None
        if args.catalog:
            snapshot = tool(target, "snapshot", "--workspace", args.workspace,
                            "--catalog", args.catalog, env=env)
            assert snapshot["created"], snapshot
            again = tool(target, "snapshot", "--workspace", args.workspace,
                         "--catalog", args.catalog, env=env)
            assert not again["created"] and again["commit"] == snapshot["commit"], again
            assert git(work, "status", "--porcelain=v1") == status
            snapshot_files = [name for name in git(work, "ls-tree", "-r", "--name-only",
                                                    snapshot["tag"]).splitlines()
                              if name.endswith(".lean")]
            assert snapshot_files, snapshot
            certified = "\n".join(git(work, "show", f"{snapshot['tag']}:{name}")
                                  for name in snapshot_files)
            assert "def Cross.size" in certified and "by decide" in certified, certified
            assert "remote%" not in certified and "remote_decl%" not in certified
            assert "-- paralean:published" not in certified
        print(json.dumps({"gate": "pass", "records": final["records"],
                          "prefix": prefix_head, "late": second["commit"],
                          "final": final["commit"], "snapshot": snapshot}, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("copy", type=Path, help="completed P3 gate working copy")
    parser.add_argument("--workspace", default="bob")
    parser.add_argument("--catalog", help="certified snapshot catalog ID")
    main(parser.parse_args())
