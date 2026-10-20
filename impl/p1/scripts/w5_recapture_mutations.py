#!/usr/bin/env python3
"""Rebuild isolated W5 recapture guard mutants against a signed legacy fixture.

Source impl/p5/scripts/w5-env.sh first. The fixture is produced by
w5_recapture_gate.py legacy-prepare/legacy-verify. Every build and mutated trust
file lives under OUT; the production P1 source, binary, and signed cache stay intact.

    python3 impl/p1/scripts/w5_recapture_mutations.py \
      .runs/w5/legacy-fixture2 .runs/w5/guard-mutants --reuse

Omit --reuse to recreate/build all mutant copies from the current P1 source.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess


ROOT = Path(__file__).resolve().parents[3]
P1 = ROOT / "impl/p1"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def replace_once(source, old, new):
    if source.count(old) != 1:
        raise RuntimeError(f"mutation anchor occurs {source.count(old)} times: {old!r}")
    return source.replace(old, new)


def mutate(kind, source):
    if kind == "no-receipt":
        return replace_once(source, "  Remote.checkReceipt g\n",
                            "  -- MUTATION: Remote.checkReceipt g\n")
    if kind.startswith("replay-"):
        anchor = "  let replay ← sourceReplay cat order imports\n"
        injected = ("  let replay : SourceReplay := { replay with results := replay.results.map "
                    "(fun (r : ReplayRes) =>\n    if r.gid == pid then { r with ok := false } else r) }\n")
        source = replace_once(source, anchor, anchor + injected)
        if kind.endswith("removed"):
            start = source.index("  unless replay.results.size == order.size && replay.results.all (·.ok) do\n")
            stop = source.index("  let some original := metas[pid]?", start)
            source = source[:start] + source[stop:]
        return source
    if kind.startswith("identity-"):
        guard = ("  unless fresh.declId == original.declId && fresh.capsule.text == original.capsule.text do\n"
                 "    throw <| IO.userError \"recapture: replay changed declaration identity or capsule source\"\n")
        injected = "  let fresh := { fresh with declId := fresh.declId ++ \"-injected-mismatch\" }\n"
        return replace_once(source, guard, injected + (guard if kind.endswith("kept") else ""))
    if kind.startswith("span-"):
        anchor = "  let bytes := original.capsule.text.toUTF8\n"
        source = replace_once(source, anchor,
                              "  let refs := refs.map (fun ref => { ref with start := 0 })\n" + anchor)
        if kind.endswith("removed"):
            start = source.index(anchor)
            stop = source.index("  return refs\n", start) + len("  return refs\n")
            source = source[:start] + "  return refs\n" + source[stop:]
        return source
    raise RuntimeError(kind)


def mutate_extra(source):
    """Inject one bad replay field per variant and bypass just its named guard."""
    source = replace_once(source, "  Remote.recapturing.set true\n",
                          "  Remote.recapturing.set true\n"
                          '  let variant ← IO.getEnv "PARALEAN_W5_MUTANT"\n')
    source = replace_once(source, "  let replay ← sourceReplay cat order imports\n",
        '''  let replay ← sourceReplay cat order imports
  let replay : SourceReplay := if variant == some "size-kept" || variant == some "size-removed" then
    { replay with results := replay.results.filter (fun (r : ReplayRes) => r.gid == pid) }
    else replay
''')
    source = replace_once(source,
        "  unless replay.results.size == order.size && replay.results.all (·.ok) do\n",
        '''  unless (variant == some "size-removed" || replay.results.size == order.size) && replay.results.all (·.ok) do
''')
    source = replace_once(source,
        '  let some fresh := result.replayed | throw <| IO.userError "recapture: command yielded no group"\n',
        '''  let some fresh := result.replayed | throw <| IO.userError "recapture: command yielded no group"
  let textMut := variant == some "text-kept" || variant == some "text-removed"
  let utf8Mut := variant == some "utf8-kept" || variant == some "utf8-removed"
  let original := if utf8Mut then
    { original with capsule := { original.capsule with text := original.capsule.text ++ ".é" } }
    else original
  let fresh := if textMut || utf8Mut then
    { fresh with capsule := { fresh.capsule with text := fresh.capsule.text ++ (if utf8Mut then ".é" else " ") } }
    else fresh
''')
    source = replace_once(source,
        "  unless fresh.declId == original.declId && fresh.capsule.text == original.capsule.text do\n",
        '''  unless fresh.declId == original.declId && (variant == some "text-removed" || fresh.capsule.text == original.capsule.text) do
''')
    source = replace_once(source, "  let bytes := original.capsule.text.toUTF8\n",
        '''  let bytes := original.capsule.text.toUTF8
  let mut refs := refs
  if variant == some "order-kept" || variant == some "order-removed" then
    refs := refs.reverse
  if variant == some "bounds-kept" || variant == some "bounds-removed" then
    let r := refs[0]!
    let some written := String.fromUTF8? (bytes.extract r.start (bytes.size + 1))
      | throw <| IO.userError "mutant: bounds extraction returned invalid UTF-8"
    refs := #[{ r with stop := bytes.size + 1, target := .str `Foo written }]
  if variant == some "token-kept" || variant == some "token-removed" then
    refs := refs.map fun r => { r with target := .str `Foo "wrong" }
  if variant == some "shape-kept" || variant == some "shape-removed" then
    refs := refs.map fun r => { r with target := .anonymous }
  if utf8Mut then
    refs := #[{ refs[0]! with start := bytes.size - 2, stop := bytes.size - 1, target := .str `Foo "é" }]
''')
    source = replace_once(source,
        "    unless stop ≤ ref.start && ref.start < ref.stop && ref.stop ≤ bytes.size do\n",
        '''    unless (variant == some "order-removed" || stop ≤ ref.start) && ref.start < ref.stop && (variant == some "bounds-removed" || ref.stop ≤ bytes.size) do
''')
    source = replace_once(source,
        '    let .str _ field := ref.target | throw <| IO.userError "recapture: field target has no final identifier"\n',
        '''    let field ← match ref.target with
      | .str _ field => pure field
      | _ =>
        if variant == some "shape-removed" then
          pure ((String.fromUTF8? (bytes.extract ref.start ref.stop)).getD "")
        else
          throw <| IO.userError "recapture: field target has no final identifier"
''')
    source = replace_once(source,
        '''    let some written := String.fromUTF8? (bytes.extract ref.start ref.stop)
      | throw <| IO.userError "recapture: invalid field UTF-8"
''',
        '''    let written ← if variant == some "utf8-removed" then pure "é" else
      match String.fromUTF8? (bytes.extract ref.start ref.stop) with
      | some written => pure written
      | none => throw <| IO.userError "recapture: invalid field UTF-8"
''')
    return replace_once(source,
        '    unless written == field || written == s!"«{field}»" do\n',
        '''    unless variant == some "token-removed" || written == field || written == s!"«{field}»" do
''')


def build(out, kind, reuse):
    copy = out / f"p1-{kind}"
    expected = (mutate_extra((P1 / "Main.lean").read_text()) if kind == "extra-guards"
                else mutate(kind, (P1 / "Main.lean").read_text()))
    if reuse and copy.exists():
        if (copy / "Main.lean").read_text() != expected:
            raise RuntimeError(f"cached {kind} mutant differs from current source")
        for source in (P1 / "Paralean").rglob("*.lean"):
            if sha(source) != sha(copy / source.relative_to(P1)):
                raise RuntimeError(f"cached {kind} dependency differs: {source.name}")
    if not reuse or not copy.exists():
        if copy.exists():
            shutil.rmtree(copy)
        subprocess.run(["cp", "-a", "--reflink=auto", str(P1), str(copy)], check=True)
        main = copy / "Main.lean"
        main.write_text(expected)
        with (out / f"build-{kind}.log").open("w") as log:
            subprocess.run([str(Path(os.environ["PARALEAN_FORK_PREFIX"]) / "bin/lake"),
                            "build", "paralean"], cwd=copy, stdout=log, stderr=log,
                           check=True)
    return copy


def execute(binary, library, fixture, trust, pid, variant=None):
    manifest = json.loads((fixture / "manifest.json").read_text())
    env = dict(os.environ, PARALEAN_BIN=str(binary), PARALEAN_LIB=str(library),
               PARALEAN_KEYS=manifest["keys"], PARALEAN_TRUST=str(trust),
               PARALEAN_DEPLOYMENT=manifest["deployment"], PARALEAN_VISIBILITY="1",
               PARALEAN_STORE=str(fixture / "bob/cache"))
    if variant is not None:
        env["PARALEAN_W5_MUTANT"] = variant
    p = subprocess.run([str(binary), "recapture-one", "--store", env["PARALEAN_STORE"],
                        "--pid", pid], text=True, capture_output=True, env=env)
    return {"exit": p.returncode, "stdout": p.stdout.strip(), "stderr": p.stderr.strip()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fixture", type=Path)
    parser.add_argument("out", type=Path)
    parser.add_argument("--reuse", action="store_true")
    args = parser.parse_args()
    if os.environ.get("PARALEAN_INSTANCE") != "p5-w5":
        raise RuntimeError("source impl/p5/scripts/w5-env.sh first")
    fixture, out = args.fixture.resolve(), args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((fixture / "manifest.json").read_text())
    records = [json.loads(p.read_text()) for p in (fixture / "bob/cache/p3/records").glob("*.json")]
    pids = {r["pid"] for r in records if r.get("kind") == "marker" and
            r.get("group") == manifest["ids"]["group"] and
            r.get("capsule") == manifest["ids"]["capsule"]}
    if len(pids) != 1:
        raise RuntimeError("legacy marker does not have exactly one package identity")
    pid = pids.pop()
    if manifest["ids"]["capsuleSha256"] != sha(
        fixture / "bob/cache/p3/capsules" / (manifest["ids"]["capsule"] + ".json")):
        raise RuntimeError("legacy signed capsule bytes changed")
    trust = Path(manifest["trust"])
    revoked = out / "trust-revoked.json"
    altered = json.loads(trust.read_text())
    altered["validators"] = []
    revoked.write_text(json.dumps(altered) + "\n")
    original = {"bin": sha(Path(os.environ["PARALEAN_BIN"])),
                "Main.lean": sha(P1 / "Main.lean"),
                "Remote.lean": sha(P1 / "Paralean/Remote.lean"),
                "Capture.lean": sha(P1 / "Paralean/Capture.lean")}
    observations = {}
    observations["receipt-kept"] = execute(Path(os.environ["PARALEAN_BIN"]),
        Path(os.environ["PARALEAN_LIB"]), fixture, revoked, pid)
    for kind in ("no-receipt", "replay-kept", "replay-removed", "identity-kept",
                 "identity-removed", "span-kept", "span-removed"):
        copy = build(out, kind, args.reuse)
        observations[kind] = execute(copy / ".lake/build/bin/paralean",
            copy / ".lake/build/lib/lean", fixture, revoked if kind == "no-receipt" else trust, pid)
    extra = build(out, "extra-guards", args.reuse)
    extra_bin, extra_lib = extra / ".lake/build/bin/paralean", extra / ".lake/build/lib/lean"
    for variant in ("size-kept", "size-removed", "text-kept", "text-removed", "order-kept", "order-removed",
                    "bounds-kept", "bounds-removed", "token-kept", "token-removed",
                    "shape-kept", "shape-removed", "utf8-kept", "utf8-removed"):
        observations[variant] = execute(extra_bin, extra_lib, fixture, trust, pid, variant)
    for kept, removed, reason in (
            ("receipt-kept", "no-receipt", "signed by an untrusted key"),
            ("replay-kept", "replay-removed", "original capsule closure did not reproduce signed content"),
            ("identity-kept", "identity-removed", "replay changed declaration identity or capsule source"),
            ("span-kept", "span-removed", "field span is not preceded by a dot")):
        refused = observations[kept]
        if (refused["exit"] == 0 or reason not in refused["stdout"] + refused["stderr"]
                or observations[removed]["exit"] != 0):
            raise RuntimeError(f"guard mutation did not distinguish {kept}/{removed}")
        if len(json.loads(observations[removed]["stdout"])) != 2:
            raise RuntimeError(f"{removed} did not return the fixture's two field references")
    for name, reason in (("size", "original capsule closure did not reproduce signed content"),
                         ("text", "replay changed declaration identity or capsule source"),
                         ("order", "invalid or overlapping field span"),
                         ("bounds", "invalid or overlapping field span"),
                         ("token", "field token disagrees with resolved target"),
                         ("shape", "field target has no final identifier"),
                         ("utf8", "invalid field UTF-8")):
        kept, removed = observations[f"{name}-kept"], observations[f"{name}-removed"]
        if kept["exit"] == 0 or reason not in kept["stdout"] + kept["stderr"]:
            raise RuntimeError(f"{name} guard did not reject for its exact reason")
        if removed["exit"] != 0 or not isinstance(json.loads(removed["stdout"]), list):
            raise RuntimeError(f"{name} guard bypass did not return field refs")
    order = json.loads(observations["order-removed"]["stdout"])
    bounds = json.loads(observations["bounds-removed"]["stdout"])
    token = json.loads(observations["token-removed"]["stdout"])
    shape = json.loads(observations["shape-removed"]["stdout"])
    utf8 = json.loads(observations["utf8-removed"]["stdout"])
    if not (order[0]["start"] > order[1]["start"] and
            bounds[0]["stop"] > len("def Foo.use (x : Foo) (y : Other) : Nat := x.field + y.field") and
            token[0]["target"][-1] == "wrong" and shape[0]["target"] == [] and
            utf8[0]["start"] + 1 == utf8[0]["stop"]):
        raise RuntimeError("a bypass did not expose the intended malformed field reference")
    after = {key: sha(Path(os.environ["PARALEAN_BIN"]) if key == "bin" else
                      P1 / ("Paralean/" + key if key in ("Remote.lean", "Capture.lean") else key))
             for key in original}
    if original != after:
        raise RuntimeError("production source or binary changed")
    report = {"fixture": manifest["ids"], "productionSha256": original,
              "sourceMutations": {
                  "receipt": {"removed": "Remote.checkReceipt g"},
                  "replay": {"injected": "if r.gid == pid then { r with ok := false } else r",
                             "removed": "replay.results.all (·.ok)"},
                  "identity": {"injected": "fresh.declId ++ \"-injected-mismatch\"",
                               "removed": "fresh.declId == original.declId && fresh.capsule.text == original.capsule.text"},
                  "span": {"injected": "{ ref with start := 0 }",
                           "removed": "field span validation loop"},
                  "text": {"injected": "fresh.capsule.text ++ \" \"",
                           "removed": "fresh.capsule.text == original.capsule.text"},
                  "order": {"injected": "refs.reverse", "removed": "stop ≤ ref.start"},
                  "bounds": {"injected": "ref.stop := bytes.size + 1",
                             "removed": "ref.stop ≤ bytes.size"},
                  "token": {"injected": "target := .str `Foo \"wrong\"",
                            "removed": "written == field || written == s!\"«{field}»\""},
                  "shape": {"injected": "target := .anonymous",
                            "removed": "let .str _ field := ref.target"},
                  "utf8": {"injected": "signed text mirrored as .é; span selects only UTF-8 lead byte",
                           "removed": "String.fromUTF8? byte-slice decoding"},
                  "size": {"injected": "filter replay.results to root gid only",
                           "removed": "replay.results.size == order.size"}},
              "extraMutantMainSha256": sha(extra / "Main.lean"),
              "observations": observations}
    (out / "result.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "result": str(out / "result.json")}))


if __name__ == "__main__":
    main()
