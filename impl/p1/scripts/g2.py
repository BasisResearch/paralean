#!/usr/bin/env python3
"""G2 (docs/p1-corpus.md): compare P1's published public names per command with the
oracle's `public` set (corpus/reference/<id>.jsonl), and count reserved names published,
and groups lacking an anchor. Usage: g2.py GATE_WORKDIR

Provenance corrections (docs/p1-corpus.md G2, as revised with canonical instance names):
auto-named instances and deriving outputs are public on both sides. P1 spells an anonymous
instance canonically (`instFooNat_<8 hex>`); its member record keeps the stock spelling
(`stock`), which is what the oracle (stock Lean) produced, so the comparison maps the
canonical name back to it. Reserved names never count as public."""
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
            p = store / "meta" / f"{gid}.json"
            if not p.exists():  # rejected groups live in the audit namespace
                p = store / "audit" / "meta" / f"{gid}.json"
            g = json.load(open(p))
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

def oracle_spelling(m, renamed=None):
    """Name of a P1 member as stock Lean spells it (canonical instance -> stock name). With the
    fork, deriving handlers name their auxiliaries after the instance (`instReprBox_<hex>.repr`);
    `renamed` maps the group's canonical instance names to stock ones for those."""
    if m.get("stock"):
        return name(m["stock"])
    n = name(m["name"])
    for c, st in (renamed or {}).items():
        if n.startswith(c + "."):
            return st + n[len(c):]
    return n

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
        pubs = {name(n) for n in g["publicNames"]}
        renamed = {name(m["name"]): name(m["stock"]) for m in g["members"] if m.get("stock")}
        by_line[g["capsule"]["startLine"]] |= {oracle_spelling(m, renamed) for m in g["members"] if name(m["name"]) in pubs}
        for m in g["members"]:
            if m.get("stock"):
                tot["canonical_instances"] += 1
                if name(m["name"]) not in pubs:
                    tot["canonical_instance_not_public"] += 1
                details.append(f"{id_} L{g['capsule']['startLine']}: canonical instance {name(m['name'])} (stock {name(m['stock'])})")
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
        exp = {a["name"].replace("«", "").replace("»", "") for a in row["added"] if a["class"] == "public"}
        got = set(by_line.get(row["line"], set()))
        tot["oracle_instances"] += sum(1 for n in exp if n.split(".")[-1].startswith("inst"))
        tot["instances_public_both"] += sum(1 for n in exp & got if n.split(".")[-1].startswith("inst"))
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
print(f"instances: oracle public names spelled inst* {tot['oracle_instances']}, public in P1 too "
      f"{tot['instances_public_both']}; anonymous instances named canonically {tot['canonical_instances']} "
      f"(not public: {tot['canonical_instance_not_public']})")
for d in details:
    print("  " + d)
