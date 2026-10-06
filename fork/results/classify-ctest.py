#!/usr/bin/env python3
"""Classify the failures of a ctest run of the fork in Paralean mode (fork/results)."""
import re,sys,collections
import gzip
# usage: classify-ctest.py CTEST_LOG[.gz] [TEST...]  (prints categories; with TEST names, their output)
p=sys.argv[1]
log=(gzip.open(p,'rt',errors='ignore') if p.endswith('.gz') else open(p,errors='ignore')).read()
fails=[l.strip().split(' - ',1)[1].split(' (')[0] for l in log.split('The following tests FAILED:')[-1].split('\n') if ' - ' in l]
# split log into per-test output chunks: from "Test #N: name ...***Failed" up to next "Test #"/"Start"
chunks={}
for m in re.finditer(r"Test +#\d+: (\S+) \.+\*\*\*(Failed|Timeout)[^\n]*\n(.*?)(?=\n\s*\d+/\d+ Test +#|\n\s+Start \d+:|\Z)", log, re.S):
    chunks[m.group(1)]=m.group(3)
cats=collections.defaultdict(list)
for t in fails:
    c=chunks.get(t,"")
    plus="\n".join(l for l in c.split("\n") if l.startswith("+") or l.startswith("-") or "error" in l)
    if re.search(r"PANIC|INTERNAL PANIC|Segmentation|stack overflow|uncaught exception|unreachable", c): k="crash?"
    elif t.startswith("server"): k="server (sync mode)"
    elif "pinned to `false` in Paralean mode" in c: k="set_option Elab.async true rejected"
    elif "instance name collision" in c: k="instance name collision"
    elif re.search(r"inst[A-Z]\w*_[0-9a-f]{8}", c): k="canonical instance name in output"
    elif "(kernel) unknown constant" in c: k="no axiom fallback (follow-up kernel error)"
    elif "Timeout" in c or c=="" : k="timeout/no output"
    else: k="other"
    cats[k].append(t)
for k,v in sorted(cats.items(), key=lambda x:-len(x[1])):
    print(f"{len(v):4d} {k}")
    if k in ("other","crash?","timeout/no output"): print("      "+" ".join(v))
if len(sys.argv)>2:
    for t in sys.argv[2:]:
        print("=====",t); print("\n".join(chunks.get(t,"").split("\n")[:25]))
