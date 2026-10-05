#!/usr/bin/env python3
"""Aggregate impl/p1/results/*.log into results/summary.md (P1 gate tables)."""
import json, re, sys, pathlib

R = pathlib.Path(__file__).resolve().parent.parent / "results"

def parse(text):
    d = {}
    m = re.findall(r"source replay: (\d+)/(\d+)", text)
    if m: d["src"] = tuple(map(int, m[-1]))
    m = re.findall(r"kernel replay: (\d+)/(\d+) groups accepted; (\d+) declarations added, (\d+) reserved", text)
    if m: d["ker"] = tuple(map(int, m[-1]))
    m = re.findall(r"isolated replay \(exact deps only\): (\d+)/(\d+)", text)
    if m: d["iso"] = tuple(map(int, m[-1]))
    m = re.findall(r"materialized: (\d+)", text)
    if m: d["mat"] = int(m[-1])
    m = re.findall(r"stock lake build: (OK|FAILED) \((\d+) ms\)", text)
    if m: d["build"] = (m[-1][0], int(m[-1][1]))
    m = re.findall(r"verify: (\d+)/(\d+) declaration groups identical.*?; (\d+) effect-only", text)
    if m: d["verify"] = tuple(map(int, m[-1]))
    m = re.findall(r"export: (\d+) modules", text)
    if m: d["modules"] = int(m[-1])
    m = re.findall(r"STATS (\{.*\})", text)
    if m: d["stats"] = json.loads(m[-1])
    m = re.findall(r"capture-time ([\d.]+) s maxrss (\d+)", text)
    if m: d["capture_s"] = float(m[-1][0]); d["capture_rss_mb"] = int(m[-1][1]) // 1024
    m = re.findall(r"=> (\d+) groups, (\d+) skipped, (\d+) diagnostics \((\d+) reject\)", text)
    if m:
        d["captured"] = sum(int(x[0]) for x in m)
        d["rejects"] = sum(int(x[3]) for x in m)
    d["needs_larger"] = re.findall(r"needs larger capsule: (\S+)", text)
    d["unsupported"] = sorted(set(re.findall(r"\[unsupported:([\w-]+)\]", text)))
    return d

def frac(t):
    return f"{t[0]}/{t[1]}" if t else "—"

rows = []
def add(label, path):
    p = R / path
    if p.exists():
        rows.append((label, parse(p.read_text(errors="replace"))))

add("core F01–F13", "core.log")
add("F14 B→A→B", "crossws.log")
add("F15 module", "f15.log")
add("F16 Mathlib attrs", "f16.log")
for p in sorted(R.glob("mathlib-M*.log")):
    add(p.stem.replace("mathlib-", ""), p.name)

out = ["| set | groups | source replay | kernel replay | isolated replay | export build | verified in stock oleans | capsule bytes median / p95 / max | needs larger capsule | unsupported |",
       "|---|---|---|---|---|---|---|---|---|---|"]
tot = dict(src=[0, 0], ker=[0, 0], iso=[0, 0], ver=[0, 0], builds=[0, 0])
for label, d in rows:
    st = d.get("stats", {})
    cb = st.get("capsuleBytes", {})
    b = d.get("build")
    v = d.get("verify")
    for k, key in (("src", "src"), ("iso", "iso")):
        if key in d: tot[k][0] += d[key][0]; tot[k][1] += d[key][1]
    if "ker" in d: tot["ker"][0] += d["ker"][0]; tot["ker"][1] += d["ker"][1]
    if v: tot["ver"][0] += v[0]; tot["ver"][1] += v[1]
    if b: tot["builds"][0] += b[0] == "OK"; tot["builds"][1] += 1
    out.append(f"| {label} | {st.get('groups', '—')} | {frac(d.get('src'))} | "
               f"{frac(d['ker'][:2]) if 'ker' in d else '—'} | {frac(d.get('iso'))} | "
               f"{b[0] + f' ({b[1]/1000:.1f} s)' if b else '—'} | "
               f"{f'{v[0]}/{v[1]} (+{v[2]} effect-only)' if v else '—'} | "
               f"{cb.get('median', '—')} / {cb.get('p95', '—')} / {cb.get('max', '—')} | "
               f"{len(d['needs_larger'])} | {', '.join(d['unsupported']) or '—'} |")
pct = lambda t: f"{t[0]}/{t[1]} = {100*t[0]/t[1]:.1f}%" if t[1] else "—"
out.append("")
out.append(f"Totals: source replay {pct(tot['src'])}; kernel replay {pct(tot['ker'])}; "
           f"isolated replay {pct(tot['iso'])}; export builds {tot['builds'][0]}/{tot['builds'][1]}; "
           f"verified declaration groups {pct(tot['ver'])}.")
(R / "summary.md").write_text("\n".join(out) + "\n")
print("\n".join(out))
