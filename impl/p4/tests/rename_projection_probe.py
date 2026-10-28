#!/usr/bin/env python3
"""Read-only audit of a published P3 projection against rename inventory rules."""

import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from rename_transaction import RenameRefused, affected_documents, source_digest  # noqa: E402


def inspect(fixture):
    documents = []
    capsules = {}
    for workspace in ("alice", "bob"):
        copy = fixture / workspace
        store = copy / "cache"
        by_file = {}
        for path in (store / "p3/records").glob("m-*.json"):
            marker = json.loads(path.read_text())
            capsule = json.loads((store / "p3/capsules" / (marker["capsule"] + ".json")).read_text())
            by_file.setdefault(marker["file"], []).append({
                "pid": marker["pid"], "group": marker["group"], "capsule": marker["capsule"],
                "deps": capsule.get("deps", []) + capsule.get("feDeps", []),
                "names": capsule.get("publicNames", []),
                "line": capsule.get("capsule", {}).get("startLine")})
            capsules[marker["group"]] = capsule
        for source in sorted((copy / "work").glob("*.lean")):
            text = source.read_text()
            documents.append({"workspace": workspace, "uri": source.resolve().as_uri(),
                              "version": 1, "environment": "audit", "generation": 1,
                              "source_sha256": source_digest(text), "groups": by_file.get(source.name, [])})
    method = next(g for doc in documents for g in doc["groups"]
                  if ["Foo", "field"] in next((c.get("publicNames", []) for key, c in capsules.items()
                                                 if key == g["group"]), []))
    target = method["group"]
    signed_use = next(c["capsule"]["text"] for c in capsules.values()
                      if ["use"] in c.get("publicNames", []))
    projected_use = (fixture / "bob/work/Use.lean").read_text()
    assert "x.field" in signed_use and "x.field" not in projected_use
    try:
        affected_documents({"complete": True, "documents": documents}, target)
    except RenameRefused as exc:
        reason = str(exc)
    else:
        raise AssertionError("published projection was accepted without source coverage")
    return {"gate": "safe-refusal", "reason": reason,
            "workspaces": 2, "sourceFiles": len(documents),
            "signedUseHasReference": True, "projectedUseHasReference": False,
            "targetGroup": target}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fixture", type=Path)
    args = parser.parse_args()
    print(json.dumps(inspect(args.fixture.resolve()), indent=2))
