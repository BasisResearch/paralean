#!/usr/bin/env python3
"""Check and combine the two W1 certification shards and immutable-base evidence."""
import argparse
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    out = args.directory
    rows = []
    for shard in ("odd", "even"):
        rows.extend(json.loads((out / f"certification-{shard}.json").read_text()))
    rows.sort(key=lambda row: row["module"])
    expected = [f"M{i:02}" for i in range(1, 19)]
    assert [row["module"] for row in rows] == expected, "missing or repeated module"
    captured = {
        row["module"]: row
        for row in json.loads((out / "capture.json").read_text())
    }
    assert sum(row["groups"] for row in rows) == 1105
    assert len({row["checker"] for row in rows}) == 1, "different checkers"
    assert len({row["lean_githash"] for row in rows}) == 1, "different toolchains"
    for row in rows:
        assert row["groups"] == captured[row["module"]]["groups"], row
        assert row["failures"] == [], row
        assert row["accepted"] == row["groups"], row
        assert row["published"] + row["duplicate"] == row["groups"], row
    before = json.loads((out / "base-before.json").read_text())
    after = json.loads((out / "base-after.json").read_text())
    for key in ("files", "bytes", "sha256"):
        assert before[key] == after[key], f"Mathlib base changed: {key}"
    summary = {
        "modules": len(rows),
        **{
            key: sum(row[key] for row in rows)
            for key in (
                "groups", "accepted", "published", "duplicate",
                "validation_s", "upload_s", "publish_s", "total_s",
            )
        },
        "failures": [],
        "store_audits_passed": len(rows),
        "checker": rows[0]["checker"],
        "lean_githash": rows[0]["lean_githash"],
        "max_observed_checker_rss_kb": max(
            row["peak_checker_rss_kb"] for row in rows
        ),
        "unchanged_base_sha256": before["sha256"],
        "timing_scope": "Summed per-module elapsed times on a shared host.",
        "audit_scope": "Each report row is written only after c.audit_ok() succeeds.",
    }
    (out / "certification.json").write_text(json.dumps(rows, indent=2) + "\n")
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
