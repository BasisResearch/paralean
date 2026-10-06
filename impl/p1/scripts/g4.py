#!/usr/bin/env python3
"""G4 (docs/p1-corpus.md) parts not covered by `paralean export`'s identity check:

1. `#print axioms`: for every public member of every exported group, the axiom set in the
   stock-built export equals the axiom set of the same declaration in the reference build
   (the stock build of the agent's original file: the corpus fixture package, a stock
   `lean -o` of F16, or the Mathlib cache for M01-M18).
2. Source/line mappings: every diagnostic that stock `lean` reports on an exported module
   is mapped back through the group headers (`-- paralean group <gid> (<ws>/<file>:<s>-<e>)`)
   to the agent's file and line. A diagnostic *resolves* if it falls inside a group's
   command text; it is *reproduced* if the reference elaboration of the agent file reports
   a diagnostic of the same severity on that line.

Usage: g4.py GATE_WORKDIR [SET...]   (sets: core crossws f15 f16 M01..M18; default: all present)
Needs the environment of scripts/env.sh (ELAN_TOOLCHAIN, PARALEAN_MATHLIB).
"""
import json, os, re, subprocess, sys, pathlib, collections, tempfile

P1 = pathlib.Path(__file__).resolve().parents[1]
REPO = P1.parents[1]
TOOL = P1 / "tools" / "Axioms.lean"
ML = pathlib.Path(os.environ.get("PARALEAN_MATHLIB", REPO / ".deps" / "mathlib"))
FX = REPO / "corpus" / "fixtures"
DM = P1 / "fixtures" / "diagmap"
work = pathlib.Path(sys.argv[1]).resolve()
only = set(sys.argv[2:])

def run(cmd, cwd, env=None):
    r = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)
    return r.returncode, r.stdout, r.stderr

_lp = {}
def lean_path(pkg):
    if pkg not in _lp:
        _lp[pkg] = run(["lake", "env", "printenv", "LEAN_PATH"], cwd=pkg)[1].strip()
    return _lp[pkg]

def axioms(lp, mods):
    env = dict(os.environ, LEAN_PATH=lp)
    rc, out, err = run(["lean", "--run", str(TOOL)] + mods, cwd=str(P1), env=env)
    if rc != 0:
        raise RuntimeError(f"axiom dump failed for {mods}: {err[-500:]}")
    res = {}
    for line in out.splitlines():
        if line.startswith("{"):
            j = json.loads(line)
            res[tuple(j["name"])] = j["axioms"]
    return res

def norm(comps, canon2stock):
    """Module-independent spelling: drop `_private.<Mod>.0`, `_pl_*` relocation components,
    and map canonical instance names back to the stock spelling of the reference build."""
    c = list(comps)
    if c and c[0] == "_private":
        i = c.index(0) if 0 in c else 0
        c = c[i + 1:]
    c = [x for x in c if not (isinstance(x, str) and x.startswith("_pl_"))]
    return to_stock(".".join(map(str, c)), canon2stock)

def to_stock(n, canon2stock):
    """Canonical instance name -> stock spelling, including deriving auxiliaries named after a
    canonical instance on the fork (`instReprBox_<hex>.repr`)."""
    if n in canon2stock:
        return canon2stock[n]
    for cn, st in canon2stock.items():
        if n.startswith(cn + "."):
            return st + n[len(cn):]
    return n

def metas(store):
    out = {}
    for p in (store / "meta").glob("*.json"):
        g = json.load(open(p))
        out[g["gid"]] = g
    return out

def current_groups(store):
    files = {}
    for f in sorted((store / "files").glob("*.json"), key=lambda p: int(p.stem)):
        r = json.load(open(f))
        files[(r["workspace"], r["file"])] = r
    return files

def export_modules(exp):
    txt = (exp / "lakefile.toml").read_text()
    m = re.search(r"roots = \[(.*)\]", txt)
    return [x.strip().strip('"') for x in m.group(1).split(",")] if m else []

def diag_lines(out):
    """(line, severity, first line of message) of every diagnostic `lean` prints."""
    ds = []
    for line in out.splitlines():
        m = re.match(r"^(.*?):(\d+):(\d+): (error|warning|info)(\([^)]*\))?: ?(.*)$", line)
        if m:
            ds.append((int(m.group(2)), m.group(4), m.group(6)[:80]))
    return ds

def map_export_diag(path, line, gmetas):
    """Map an export-module line to (agent file, agent line) or None (scaffolding)."""
    lines = path.read_text().splitlines()
    hdr = None
    for i in range(min(line, len(lines)) - 1, -1, -1):
        m = re.match(r"^-- paralean group ([0-9a-f]+) \((.*?)/(.*):(\d+)-(\d+)\)$", lines[i])
        if m:
            hdr = (i + 1, m)
            break
    if hdr is None:
        return None
    hline, m = hdr
    g = gmetas.get(m.group(1))
    if g is None:
        return None
    text = g["capsule"]["text"]
    block = "\n".join(lines[hline:])
    k = block.find(text)
    if k < 0:
        return None
    tstart = hline + 1 + block[:k].count("\n")   # 1-based export line of the text's first line
    tend = tstart + text.count("\n")
    if not (tstart <= line <= tend):
        return None
    return (m.group(3), g["capsule"]["startLine"] + (line - tstart))

def sets():
    out = []
    for s in ["core", "crossws", "f15", "f16", "diagmap"]:
        out.append(s)
    for i in range(1, 19):
        out.append(f"M{i:02d}")
    return [s for s in out if not only or s in only]

def set_dirs(s):
    if s.startswith("M"):
        return work / "mathlib" / s / "store", work / "mathlib" / s / "export"
    return work / s / "store", work / s / "export"

mods_txt = {l.split()[0]: l.split()[1] for l in open(REPO / "corpus" / "modules.txt") if l.startswith("M")}

tot = collections.Counter()
report = []
for s in sets():
    store, exp = set_dirs(s)
    if not (store.exists() and (exp / ".lake").exists()):
        report.append(f"{s}: no store/export (not run)")
        continue
    gm = metas(store)
    files = current_groups(store)
    gids = [g for r in files.values() for g in r["groups"]]
    canon2stock = {}
    pubs = set()
    for gid in gids:
        g = gm[gid]
        for m in g["members"]:
            if m.get("stock"):
                canon2stock[".".join(map(str, m["name"]))] = ".".join(map(str, m["stock"]))
        pubs |= {norm(n, {}) for n in g["publicNames"]}
    pubs = {to_stock(n, canon2stock) for n in pubs}
    emods = export_modules(exp)
    # reference build
    tmp = None
    if s in ("core", "crossws", "f15"):
        ref_lp = lean_path(str(FX))
        ref_mods = sorted({".".join(map(str, r["module"])) for r in files.values()}) if s != "crossws" else \
            ["Fixtures.F14.B1", "Fixtures.F14.A", "Fixtures.F14.B2"]
    elif s == "f16":
        tmp = tempfile.mkdtemp()
        mlp = lean_path(str(ML))
        rc, _, err = run(["lean", "-R", str(REPO / "corpus" / "mathlib-fixtures"), "-o", f"{tmp}/F16MathlibAttrs.olean",
                          str(REPO / "corpus" / "mathlib-fixtures" / "F16MathlibAttrs.lean")],
                         cwd=str(ML), env=dict(os.environ, LEAN_PATH=mlp))
        ref_lp = mlp; ref_mods = [f"F16MathlibAttrs={tmp}/F16MathlibAttrs.olean"]
    elif s == "diagmap":
        tmp = tempfile.mkdtemp()
        rc, _, err = run(["lean", "-o", f"{tmp}/DiagMap.olean", str(DM / "DiagMap.lean")], cwd=str(DM))
        ref_lp = tmp; ref_mods = ["DiagMap"]
    else:
        ref_lp = lean_path(str(ML)); ref_mods = [mods_txt[s]]
    try:
        ref = axioms(ref_lp, ref_mods)
        # export modules from explicit artifacts: their root may also be on LEAN_PATH
        elib = exp / ".lake" / "build" / "lib" / "lean"
        got = axioms(lean_path(str(exp)),
                     [f"{m}={elib / (m.replace('.', '/') + '.olean')}" for m in emods])
    except RuntimeError as e:
        report.append(f"{s}: {e}"); tot["axiom_errors"] += 1; continue
    refn = {norm(k, {}): v for k, v in ref.items()}
    gotn = {norm(k, canon2stock): v for k, v in got.items()}
    n_eq = n_ne = n_miss = 0
    for n in sorted(pubs):
        if n not in gotn or n not in refn:
            n_miss += 1
            report.append(f"{s}: public {n} missing in {'export' if n not in gotn else 'reference'}")
            continue
        if sorted(gotn[n]) == sorted(refn[n]):
            n_eq += 1
        else:
            n_ne += 1
            report.append(f"{s}: axioms differ for {n}: export {gotn[n]} vs reference {refn[n]}")
    tot["pub"] += len(pubs); tot["ax_eq"] += n_eq; tot["ax_ne"] += n_ne; tot["ax_missing"] += n_miss
    allk = set(gotn) & set(refn)
    tot["all_eq"] += sum(1 for n in allk if sorted(gotn[n]) == sorted(refn[n])); tot["all"] += len(allk)
    # source mappings
    ref_diags = collections.defaultdict(set)
    if s in ("core", "f15"):
        for r in files.values():
            _, out, _ = run(["lake", "env", "lean", r["file"]], cwd=str(FX))
            for (l, sev, msg) in diag_lines(out):
                ref_diags[r["file"]].add((l, sev))
    elif s == "f16":
        _, out, _ = run(["lean", str(REPO / "corpus" / "mathlib-fixtures" / "F16MathlibAttrs.lean")],
                        cwd=str(ML), env=dict(os.environ, LEAN_PATH=lean_path(str(ML))))
        for (l, sev, msg) in diag_lines(out):
            ref_diags["F16MathlibAttrs.lean"].add((l, sev))
    elif s == "diagmap":
        _, out, _ = run(["lean", "DiagMap.lean"], cwd=str(DM))
        for (l, sev, msg) in diag_lines(out):
            ref_diags["DiagMap.lean"].add((l, sev))
    elif s.startswith("M"):
        f = mods_txt[s].replace(".", "/") + ".lean"
        _, out, _ = run(["lake", "env", "lean", f], cwd=str(ML))
        for (l, sev, msg) in diag_lines(out):
            ref_diags[f].add((l, sev))
    nd = nres = nrep = 0
    for em in emods:
        path = exp / (em.replace(".", "/") + ".lean")
        _, out, _ = run(["lake", "env", "lean", str(path)], cwd=str(exp))
        for (l, sev, msg) in diag_lines(out):
            nd += 1
            mp = map_export_diag(path, l, gm)
            if mp is None:
                report.append(f"{s}: unresolved {sev} at {em}:{l}: {msg}")
                continue
            nres += 1
            if (mp[1], sev) in ref_diags.get(mp[0], set()):
                nrep += 1
            elif s != "crossws":
                report.append(f"{s}: {sev} at {em}:{l} maps to {mp[0]}:{mp[1]}, not reported there by the reference: {msg}")
    nref = sum(len(v) for v in ref_diags.values())
    tot["diags"] += nd; tot["resolved"] += nres; tot["reproduced"] += nrep; tot["ref_diags"] += nref
    report.append(f"{s}: axioms equal {n_eq}/{len(pubs)} public members ({n_ne} differ, {n_miss} missing); "
                  f"diagnostics {nd}, resolved {nres}, reproduced at the same agent line {nrep} (reference has {nref})")

print(f"G4 axioms: {tot['ax_eq']}/{tot['pub']} public members have the reference's axiom set "
      f"({tot['ax_ne']} differ, {tot['ax_missing']} missing); all shared constants {tot['all_eq']}/{tot['all']}")
pct = lambda a, b: f"{100*a/b:.1f}%" if b else "n/a"
print(f"G4 source mappings: {tot['resolved']}/{tot['diags']} export diagnostics resolve to an agent "
      f"file and line ({pct(tot['resolved'], tot['diags'])}); {tot['reproduced']} reproduce a reference "
      f"diagnostic at that line (reference total {tot['ref_diags']})")
for r in report:
    print("  " + r)
