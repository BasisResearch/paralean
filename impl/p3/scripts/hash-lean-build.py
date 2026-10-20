#!/usr/bin/env python3
"""Hash a private Lean package's build outputs, including dependency packages."""
import argparse
import hashlib
import json
from pathlib import Path


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("root", type=Path)
parser.add_argument("output", type=Path)
args = parser.parse_args()
root = args.root.resolve()
directories = [root / ".lake/build"] + sorted(
    (root / ".lake/packages").glob("*/.lake/build")
)
rows = []
for directory in directories:
    for path in sorted(directory.rglob("*")):
        if path.is_file():
            data = path.read_bytes()
            rows.append([
                str(path.relative_to(root)),
                len(data),
                hashlib.sha256(data).hexdigest(),
            ])
encoded = json.dumps(rows, separators=(",", ":")).encode()
args.output.with_suffix(".files.json").write_bytes(encoded + b"\n")
summary = {
    "root": str(root),
    "files": len(rows),
    "bytes": sum(row[1] for row in rows),
    "sha256": hashlib.sha256(encoded).hexdigest(),
}
args.output.write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps(summary))
