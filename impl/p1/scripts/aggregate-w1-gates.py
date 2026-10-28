#!/usr/bin/env python3
"""Assert and combine the final W1 P1 stock/fork G1–G6 measurements."""
import csv
import hashlib
import json
import re
from pathlib import Path

P1 = Path(__file__).resolve().parents[1]
REPO = P1.parents[1]
RESULTS = P1 / "results"
SETS = ["core", "crossws", "f15", "f16"] + [f"M{i:02d}" for i in range(1, 19)]
ALL = set(SETS + ["diagmap"])


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def rows(path):
    data = list(csv.DictReader(path.open(), delimiter="\t"))
    assert len(data) == 23 and {r["set"] for r in data} == ALL, path
    return {r["set"]: r for r in data}


def pattern(text, regex):
    m = re.search(regex, text, re.M)
    assert m, regex
    return tuple(map(int, m.groups()))


def measure(mode):
    out = RESULTS / f"w1-{mode}"
    verify = out / "verify-existing-final2-complete"
    replay = out / "replay-final2"
    vr = rows(verify / "status.tsv")
    rr = rows(replay / "status.tsv")
    replay_counts = {}
    for kind in ("source", "kernel", "isolated"):
        ok = total = 0
        for label in SETS:
            r = rr[label]
            assert int(r["exit"]) == 0, (mode, label, r)
            a, b = int(r[f"{kind}_ok"]), int(r[f"{kind}_total"])
            assert a == b, (mode, label, kind, a, b)
            ok += a; total += b
        assert (ok, total) == (1225, 1225), (mode, kind, ok, total)
        p = rr["diagmap"]
        assert int(p["exit"]) == 0 and (int(p[f"{kind}_ok"]), int(p[f"{kind}_total"])) == (8, 8)
        replay_counts[kind] = {"ok": ok, "total": total}

    identity_ok = sum(int(vr[s]["verified"]) for s in SETS)
    identity_total = sum(int(vr[s]["denominator"]) for s in SETS)
    effect_only = sum(int(vr[s]["effect_only"]) for s in SETS)
    assert (identity_ok, identity_total, effect_only) == (1121, 1142, 83)
    assert (int(vr["diagmap"]["verified"]), int(vr["diagmap"]["denominator"])) == (7, 7)
    assert {s for s in SETS if int(vr[s]["exit"]) != 0} == {"M08", "M17"}
    assert (int(vr["core"]["verified"]), int(vr["core"]["denominator"])) == (85, 85)
    assert (int(vr["M08"]["verified"]), int(vr["M08"]["denominator"])) == (1, 2)
    assert (int(vr["M17"]["verified"]), int(vr["M17"]["denominator"])) == (1, 21)
    for s in ("M08", "M17"):
        log = (verify / f"{s}.log").read_text()
        assert log.count("[reject:export-mismatch]") == (1 if s == "M08" else 20)
        assert "[reject:export-missing]" not in log

    manifest_before = verify / "artifacts-before.tsv"
    manifest_after = verify / "artifacts-after.tsv"
    assert manifest_before.read_bytes() == manifest_after.read_bytes()
    assert len(manifest_before.read_text().splitlines()) == 186  # header + 185 files
    sidecars = sum(p.endswith((".olean.server", ".olean.private"))
                   for _, p, _ in csv.reader(manifest_before.open(), delimiter="\t") if p != "path")
    assert sidecars == 38

    g2 = (out / "g2.txt").read_text()
    public_total, public_ok, mismatch, reserved, anchor = pattern(
        g2, r"G2 commands with public names: (\d+); exact public-set match (\d+); mismatch (\d+); reserved names published (\d+); groups without public name lacking an anchor (\d+)")
    canonical, nonpublic = pattern(g2, r"anonymous instances named canonically (\d+) \(not public: (\d+)\)")
    assert (public_ok, public_total, mismatch, reserved, anchor, nonpublic) == (1122, 1127, 5, 0, 0, 0)
    assert canonical == (78 if mode == "stock" else 90)

    summary = (out / "summary-final2.md").read_text().splitlines()
    table = [line.split("|") for line in summary if line.startswith("| ") and not line.startswith("| set")]
    assert len(table) == 22, (mode, len(table))
    fixture_max = mathlib_max = groups = 0
    for cells in table:
        label = cells[1].strip()
        groups += int(cells[2].strip())
        cap_max = int(cells[8].strip().split("/")[-1])
        assert int(cells[9].strip()) == 0
        if label.startswith("M"):
            mathlib_max = max(mathlib_max, cap_max)
        else:
            fixture_max = max(fixture_max, cap_max)
    assert (groups, fixture_max, mathlib_max) == (1225, 390, 2868)

    ratios = {"fixtures": [], "mathlib": []}
    above_bound = 0
    for label in SETS:
        name = f"mathlib-{label}.log" if label.startswith("M") else f"{label}.log"
        stats = [json.loads(line.split("STATS ", 1)[1])
                 for line in (out / name).read_text().splitlines() if line.startswith("STATS ")]
        assert stats, (mode, label)
        stats = stats[-1]
        ratios["mathlib" if label.startswith("M") else "fixtures"].append(stats["ratio"])
        above_bound += len(stats["aboveP95Bound"])
    mathlib_p50 = max(x["p50"] for x in ratios["mathlib"])
    mathlib_p95 = max(x["p95"] for x in ratios["mathlib"])
    fixture_p50 = max(x["p50"] for x in ratios["fixtures"])
    fixture_p95 = max(x["p95"] for x in ratios["fixtures"])
    assert (mathlib_p50, mathlib_p95, fixture_p50, fixture_p95, above_bound) == (
        3.795918, 9.826087, 5.542857, 6.555556, 0)

    g4 = (out / "g4.txt").read_text()
    ax_ok, ax_total, ax_diff, ax_missing, shared_ok, shared_total = pattern(
        g4, r"G4 axioms: (\d+)/(\d+) public members have the reference's axiom set \((\d+) differ, (\d+) missing\); all shared constants (\d+)/(\d+)")
    mapped, mapping_total, reproduced, reference_lines = pattern(
        g4, r"G4 source mappings: (\d+)/(\d+) export diagnostics resolve to an agent file and line \([^)]*\); (\d+) reproduce a reference diagnostic at that line \(reference total (\d+)\)")
    assert (ax_ok, ax_total, ax_diff, ax_missing, shared_ok, shared_total) == (1445, 1448, 0, 3, 2495, 2502)
    assert (mapped, mapping_total, reproduced, reference_lines) == (5, 5, 5, 4)

    for label in ALL:
        name = f"mathlib-{label}.log" if label.startswith("M") else f"{label}.log"
        log = (out / name).read_text()
        assert "stock lake build: OK " in log, (mode, label)
    negative = (out / "negative.log").read_text()
    cases = {
        "N1Sorry": ([(0, 1, 1)], {"axiom"}, (0, 0, 1)),
        "N2Axiom": ([(0, 4, 4)], {"axiom", "new-axiom", "rejected-dep"}, (0, 0, 2)),
        "N3SkipKernel": ([(0, 1, 1)], {"bypass-option"}, (0, 0, 1)),
        "N4ChangedTarget": ([(1, 0, 0), (0, 1, 1)], {"changed-target"}, (0, 0, 1)),
        "N5ChangedDep": ([(2, 0, 0), (1, 2, 2)], {"elab-error"}, (3, 3, 0)),
        "N6NativeDecide": ([(0, 2, 2)], {"axiom", "new-axiom"}, (0, 0, 1)),
    }
    negative_cases = {}
    for label, (expected_summaries, expected_reasons, expected_store) in cases.items():
        headings = list(re.finditer(rf"^### {re.escape(label)}$", negative, re.M))
        assert len(headings) == 1, (mode, label, "heading")
        start = headings[0].end()
        following = re.search(r"^### ", negative[start:], re.M)
        block = negative[start:start + following.start()] if following else negative[start:]
        exits = re.findall(r"^exit=(\d+)$", block, re.M)
        assert exits == ["1"], (mode, label, "exit", exits)
        summaries = [tuple(map(int, m)) for m in re.findall(
            r"^  => (\d+) groups, \d+ skipped, (\d+) diagnostics \((\d+) reject\)$", block, re.M)]
        assert summaries == expected_summaries, (mode, label, "capture summaries", summaries)
        reasons = set(re.findall(r"\[reject:([a-z-]+)\]", block))
        assert reasons == expected_reasons, (mode, label, "rejections", reasons)
        stores = [tuple(map(int, m)) for m in re.findall(
            r"^  store: publishable objects (\d+) \(published groups (\d+)\); audit objects (\d+)$",
            block, re.M)]
        assert stores == [expected_store], (mode, label, "store", stores)
        store = REPO / ".runs" / "w1" / f"gate-{mode}" / "negative" / (
            "N4" if label == "N4ChangedTarget" else "N5" if label == "N5ChangedDep" else label)
        actual_store = (
            len(list((store / "objects").glob("*.grp"))),
            sum(len(json.loads(p.read_text())["groups"]) for p in (store / "files").glob("*.json")),
            len(list((store / "audit/objects").glob("*.grp"))),
        )
        assert actual_store == expected_store, (mode, label, "persisted store", actual_store)
        negative_cases[label] = {
            "capture_exit": 1, "capture_group_summaries": [
                {"accepted": a, "diagnostics": d, "rejections": r} for a, d, r in summaries],
            "rejection_codes": sorted(reasons), "publishable_objects": stores[0][0],
            "published_groups": stores[0][1], "audit_objects": stores[0][2],
        }
    # N5 retains two groups from the original capture and one valid revised
    # value; the failed dependent proof contributes no published group.
    assert [x["accepted"] for x in negative_cases["N5ChangedDep"]["capture_group_summaries"]] == [2, 1]
    assert "-- upstream revision value := 1, same file re-captured:" in negative
    audit = negative.split("### N3 audit: kernel re-check of the rejected group by the validator", 1)[1].split("### ", 1)[0]
    assert "source replay: 1/1 groups reproduce their declaration ID" in audit
    assert "kernel replay: 0/1 groups accepted; 0 declarations added, 0 reserved names re-realized" in audit
    assert "[reject:kernel]" in audit
    crossws = (out / "crossws.log").read_text()
    assert "Unknown identifier `helper`" in crossws and "export: 3 modules, 3 groups" in crossws
    assert "verify: 3/3 declaration groups identical" in crossws

    snap = REPO / ".runs" / "w1" / f"p1-{mode}-final2"
    binary = snap / ".lake/build/bin/paralean"
    return {
        "G1": {**replay_counts, "diagnostic_probe": {"ok": 8, "total": 8}, "corpus_sets": 22},
        "G2": {"public_sets": {"ok": public_ok, "total": public_total}, "explained_instance_spellings": mismatch,
               "canonical_instances": canonical, "reserved_published": reserved, "missing_anchors": anchor},
        "G3": {"groups": groups, "max_fixture_capsule_bytes": fixture_max,
               "max_mathlib_capsule_bytes": mathlib_max, "needs_larger_capsule": 0,
               "above_p95_bound": above_bound,
               "max_mathlib_p50_ratio": mathlib_p50, "max_mathlib_p95_ratio": mathlib_p95,
               "max_fixture_p50_ratio": fixture_p50, "max_fixture_p95_ratio": fixture_p95},
        "G4": {"export_builds": {"ok": 23, "total": 23},
               "identity": {"ok": identity_ok, "total": identity_total, "effect_only_build_checked": effect_only},
               "diagnostic_probe_identity": {"ok": 7, "total": 7},
               "axiom_sets": {"ok": ax_ok, "total": ax_total, "differ": ax_diff, "missing_reference_names": ax_missing},
               "shared_constants": {"ok": shared_ok, "total": shared_total},
               "source_mappings": {"resolved": mapped, "total": mapping_total, "reproduced": reproduced,
                                   "distinct_reference_lines": reference_lines},
               "residuals": {"M08": {"mismatches": 1, "verified": 1, "total": 2},
                             "M17": {"mismatches": 20, "verified": 1, "total": 21}}},
        "G5": {"required_negative_cases": {"ok": len(negative_cases), "total": 6},
               "rejected_objects_published": 0, "cases": negative_cases,
               "N3_validator_recheck": {"source_replayed": 1, "kernel_accepted": 0, "total": 1}},
        "G6": {"acyclic_modules": 3, "identity": {"ok": 3, "total": 3}, "expected_early_failure": True},
        "provenance": {"binary_sha256": sha(binary), "export_source_sha256": sha(snap / "Paralean/Export.lean"),
                       "replay_source_sha256": sha(snap / "Paralean/Replay.lean"),
                       "export_olean_sha256": sha(snap / ".lake/build/lib/lean/Paralean/Export.olean"),
                       "artifact_manifest_sha256": sha(manifest_before), "artifact_files": 185,
                       "artifact_olean_sidecars": sidecars,
                       "replay_status": str((replay / "status.tsv").relative_to(REPO)),
                       "identity_status": str((verify / "status.tsv").relative_to(REPO)),
                       "g4_report": str((out / "g4.txt").relative_to(REPO))},
    }


def baseline(mode):
    return {
        "G1": {"source": {"ok": 1224, "total": 1225}, "kernel": {"ok": 1225, "total": 1225},
               "isolated": {"ok": 1224, "total": 1225}},
        "G2": {"public_sets": {"ok": 1122, "total": 1127},
               "canonical_instances": 78 if mode == "stock" else 90},
        "G3": {"max_fixture_capsule_bytes": 390, "max_mathlib_capsule_bytes": 2868,
               "needs_larger_capsule": 0, "above_p95_bound": 0,
               "max_mathlib_p50_ratio": 3.795918, "max_mathlib_p95_ratio": 9.826087},
        "G4": {"export_builds": {"ok": 23, "total": 23}, "identity": {"ok": 1116, "total": 1142},
               "axiom_sets": {"ok": 1445, "total": 1448, "differ": 0, "missing_reference_names": 3},
               "source_mappings": {"resolved": 5, "total": 5, "reproduced": 5}},
        "G5": {"required_negative_cases": {"ok": 6, "total": 6}},
        "G6": {"acyclic_modules": 3, "identity": {"ok": 3, "total": 3}},
    }


def main():
    modes = {mode: measure(mode) for mode in ("stock", "fork")}
    for mode, got in modes.items():
        base = baseline(mode)
        assert got["G1"]["source"]["ok"] >= base["G1"]["source"]["ok"]
        assert got["G1"]["isolated"]["ok"] >= base["G1"]["isolated"]["ok"]
        assert got["G4"]["identity"]["ok"] >= base["G4"]["identity"]["ok"]
    data = {"schema": "paralean-w1-p1-gates/v1",
            "baseline_sources": ["docs/p1-gate.md", "docs/fork-log.md"],
            "baseline": {mode: baseline(mode) for mode in modes},
            "final": modes,
            "improvement": {mode: {"G1_source_groups": 1, "G1_isolated_groups": 1,
                                   "G4_identity_groups": 5} for mode in modes}}
    dest = RESULTS / "w1-measurement.json"
    dest.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    print(dest)


if __name__ == "__main__":
    main()
