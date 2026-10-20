#!/usr/bin/env python3
"""Hash generated source plus all OLean artifacts used by G4 and verifyExport."""
from hashlib import sha256
from pathlib import Path
import sys

work = Path(sys.argv[1])
sets = ["core", "crossws", "f15", "f16", "diagmap"] + [f"M{i:02d}" for i in range(1, 19)]
print("set\tpath\tsha256")
for label in sets:
    exp = work / (f"mathlib/{label}" if label.startswith("M") else label) / "export"
    if not exp.is_dir():
        raise SystemExit(f"missing export for {label}: {exp}")
    files = [p for p in exp.rglob("*") if p.is_file() and
             (p.suffix == ".lean" or p.name == "lakefile.toml" or
              p.name.endswith((".olean", ".olean.server", ".olean.private")))]
    if not any(p.suffix == ".olean" for p in files):
        raise SystemExit(f"missing built OLean for {label}: {exp}")
    for path in sorted(files):
        print(f"{label}\t{path.relative_to(exp)}\t{sha256(path.read_bytes()).hexdigest()}")
