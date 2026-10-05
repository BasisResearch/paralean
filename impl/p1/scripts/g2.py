#!/usr/bin/env python3
"""G2 (docs/p1-corpus.md): compare P1's published public names per command with the
oracle's `public` set (corpus/reference/<id>.jsonl), and count reserved names published,
and groups lacking an anchor. Usage: g2.py GATE_WORKDIR"""
import json, sys, pathlib, collections

repo = pathlib.Path(__file__).resolve().parents[3]
ref = repo / "corpus" / "reference"
work = pathlib.Path(sys.argv[1])

def name(c):  # component-array JSON name -> dotted string (oracle spelling, unescaped)
    return ".".join(str(x) for x in c)

def store_groups(store):
    """All captured groups (published + rejected) of the latest capture of each file."""
    files = {}
    for f in sorted((store / "files").glob("*.json"), key=lambda p: int(p.stem)):
        r = json.load(open(f))
        files[(r["workspace"], r["file"])] = r
    out = []
    for r in files.values():
        for gid in r["groups"] + r.get("rejected", []):
            g = json.load(open(store / "meta" / f"{gid}.json"))
            out.append((r["file"], g))
    return out

def oracle(id_):
    rows = []
    p = ref / f"{id_}.jsonl"
    if not p.exists():
        return None
    for line in open(p):
        rows.append(json.loads(line))
    return rows

def gen_instance(n, row):
    # provenance correction: auto-named instances / deriving outputs are scoped-generated
    return any(c.startswith("inst") for c in n.split("."))

cases = []  # (oracle id, store, file filter)
core = work / "core" / "store"
for fid in ["F01Theorem", "F02Def", "F03Structure", "F04Inductive", "F05Mutual", "F06Structural",
            "F07WellFounded", "F08PrivateGenerated", "F09InstanceOnly", "F10SimpAttrDecl",
            "F10SimpAttrUse", "F11ScopedDecl", "F11ScopedUse", "F12Macro", "F13InitDecl", "F13InitUse"]:
    cases.append((fid, core, f"Fixtures/{fid}.lean"))
cases.append(("F15Module", work / "f15" / "store", "Fixtures/F15Module.lean"))
cases.append(("F16MathlibAttrs", work / "f16" / "store", "F16MathlibAttrs.lean"))
for i in range(1, 19):
    m = f"M{i:02d}"
    cases.append((m, work / "mathlib" / m / "store", None))

tot = collections.Counter()
details = []
for id_, store, ffilter in cases:
    rows = oracle(id_)
    if rows is None or not store.exists():
        details.append(f"{id_}: missing data"); continue
    groups = [g for f, g in store_groups(store) if ffilter is None or f == ffilter]
    by_line = collections.defaultdict(set)
    reserved_pub = 0
    for g in groups:
        by_line[g["capsule"]["startLine"]] |= {name(n) for n in g["publicNames"]}
        if not g["publicNames"] and g["members"] and g.get("anchor") is None:
            tot["no_anchor"] += 1
    oracle_reserved = set()
    for row in rows:
        for a in row["added"]:
            if a["class"] == "reserved":
                oracle_reserved.add(a["name"])
    for g in groups:
        for m in g["members"]:
            if name(m["name"]) in oracle_reserved:
                reserved_pub += 1
    tot["reserved_published"] += reserved_pub
    for row in rows:
        exp = {a["name"].replace("«", "").replace("»", "") for a in row["added"] if a["class"] == "public" and not gen_instance(a["name"], row)}
        got = {n for n in by_line.get(row["line"], set()) if not gen_instance(n, row)}
        if not exp and not got:
            continue
        tot["commands"] += 1
        if exp == got:
            tot["match"] += 1
        else:
            tot["mismatch"] += 1
            details.append(f"{id_} L{row['line']}: oracle-only {sorted(exp - got)[:4]} p1-only {sorted(got - exp)[:4]}")

print(f"G2 commands with public names: {tot['commands']}; exact public-set match {tot['match']}; "
      f"mismatch {tot['mismatch']}; reserved names published {tot['reserved_published']}; "
      f"groups without public name lacking an anchor {tot['no_anchor']}")
for d in details:
    print("  " + d)
