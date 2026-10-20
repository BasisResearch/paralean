#!/usr/bin/env python3
"""Inspect canonical group sections produced by DumpExistingExportGroup.lean.

Usage: summarize-export-group-diff.py STORE_OBJECTS DUMP_LOG EXPORTED_GROUP_DIR
The output identifies literal bytes in the *expression* section, separately
from normalized name/reference tables; it does not infer semantic equivalence.
"""
from pathlib import Path
import re
import sys


def read_uv(data: bytes, at: int) -> tuple[int, int]:
    value = shift = 0
    while True:
        byte = data[at]
        at += 1
        value |= (byte & 0x7f) << shift
        if byte < 128:
            return value, at
        shift += 7


def read_bytes(data: bytes, at: int) -> tuple[bytes, int]:
    length, at = read_uv(data, at)
    return data[at:at + length], at + length


def sections(path: Path) -> dict[str, tuple[int, bytes] | bytes]:
    data = path.read_bytes()
    _, at = read_uv(data, 0)  # format
    _, at = read_bytes(data, at)  # magic
    _, at = read_bytes(data, at)  # base identity
    parts: dict[str, tuple[int, bytes] | bytes] = {}
    for name in ("names", "refs", "levels", "exprs"):
        count, at = read_uv(data, at)
        payload, at = read_bytes(data, at)
        parts[name] = count, payload
    body, at = read_bytes(data, at)
    assert at == len(data), path
    parts["body"] = body
    return parts


def string_literals(count: int, data: bytes) -> list[bytes]:
    """Decode Expr entries to distinguish `.lit (.strVal _)` from other bytes."""
    at = 0
    out = []
    for _ in range(count):
        tag = data[at]
        at += 1
        if tag in (0, 7):  # bvar or Nat literal
            _, at = read_bytes(data, at)
        elif tag == 1:  # sort
            _, at = read_uv(data, at)
        elif tag == 2:  # const and levels
            _, at = read_uv(data, at)
            levels, at = read_uv(data, at)
            for _ in range(levels):
                _, at = read_uv(data, at)
        elif tag == 3:  # app
            for _ in range(2):
                _, at = read_uv(data, at)
        elif tag in (4, 5):  # lam or forall
            for _ in range(3):
                _, at = read_uv(data, at)
            at += 1  # binder info
        elif tag == 6:  # let
            for _ in range(4):
                _, at = read_uv(data, at)
            at += 1  # nondependent flag
        elif tag == 8:  # string literal
            value, at = read_bytes(data, at)
            out.append(value)
        elif tag == 9:  # metadata
            _, at = read_uv(data, at)
            entries, at = read_uv(data, at)
            for _ in range(entries):
                _, at = read_uv(data, at)
                value_tag = data[at]
                at += 1
                if value_tag in (0, 3, 4, 5):
                    _, at = read_bytes(data, at)
                elif value_tag == 1:
                    at += 1
                elif value_tag == 2:
                    _, at = read_uv(data, at)
                else:
                    raise ValueError(f"unknown metadata value tag {value_tag}")
        elif tag == 10:  # projection
            _, at = read_uv(data, at)
            _, at = read_bytes(data, at)  # Nat index
            _, at = read_uv(data, at)
        else:
            raise ValueError(f"unknown Expr tag {tag} at offset {at-1}")
    assert at == len(data), (at, len(data))
    return out


def main() -> None:
    objects, log, exported = map(Path, sys.argv[1:])
    print("line\tcaptured_id\texported_id\tnames_equal\trefs_equal\tlevels_equal\t"
          "captured_exprs\texported_exprs\tcaptured_private\texported_private\t"
          "captured_hygiene\texported_hygiene\tcaptured_mathlib\texported_mathlib\t"
          "captured_paralean_export\texported_paralean_export\t"
          "captured_literal_paralean_export\texported_literal_paralean_export\tbyte_delta")
    pattern = re.compile(r"line=(\d+) captured=([a-f0-9]{64}) exported=([a-f0-9]{64}) members=(\d+)")
    for text in log.read_text().splitlines():
        match = pattern.fullmatch(text)
        if not match:
            continue
        line, captured_id, exported_id, _ = match.groups()
        old_path = objects / f"{captured_id}.grp"
        new_path = exported / f"{line}.grp"
        old, new = sections(old_path), sections(new_path)
        old_exprs, new_exprs = old["exprs"], new["exprs"]
        assert isinstance(old_exprs, tuple) and isinstance(new_exprs, tuple)
        old_literals = string_literals(*old_exprs)
        new_literals = string_literals(*new_exprs)
        print("\t".join(map(str, (
            line, captured_id, exported_id,
            int(old["names"] == new["names"]),
            int(old["refs"] == new["refs"]),
            int(old["levels"] == new["levels"]),
            old_exprs[0], new_exprs[0],
            old_exprs[1].count(b"_private"), new_exprs[1].count(b"_private"),
            old_exprs[1].count(b"_@"), new_exprs[1].count(b"_@"),
            old_exprs[1].count(b"Mathlib"), new_exprs[1].count(b"Mathlib"),
            old_exprs[1].count(b"ParaleanExport"),
            new_exprs[1].count(b"ParaleanExport"),
            old_literals.count(b"ParaleanExport"),
            new_literals.count(b"ParaleanExport"),
            new_path.stat().st_size - old_path.stat().st_size,
        ))))


if __name__ == "__main__":
    if len(sys.argv) != 4:
        raise SystemExit(__doc__)
    main()
