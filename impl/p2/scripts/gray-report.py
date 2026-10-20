#!/usr/bin/env python3
"""Summarize paired FDB pause/partition probe runs from robustness-study.sh.

Each failed probe is timed from call start to completion. Since probes run serially,
the interval between the adjacent successful completions bounds the observed
unavailability, but a single timeout is not itself a one-second outage.
"""
import json
import statistics
import sys
from pathlib import Path


def windows(rows):
    result = []
    start = None
    for i, row in enumerate(rows + [(0, 0, 0)]):
        if row[2] and start is None:
            start = i
        if not row[2] and start is not None:
            previous = rows[start - 1][1] if start else None
            following = rows[i][1] if i < len(rows) else None
            result.append(
                {
                    "first_failed_start_ns": rows[start][0],
                    "last_failed_end_ns": rows[i - 1][1],
                    "failed_samples": i - start,
                    "first_to_last_failed_s": round((rows[i - 1][1] - rows[start][0]) / 1e9, 3),
                    "success_bracket_s": round((following - previous) / 1e9, 3)
                    if previous and following
                    else None,
                }
            )
            start = None
    return result


def main(out: Path) -> None:
    faults = {}
    for line in (out / "faults.tsv").read_text().splitlines():
        when, label, kind, edge = line.split("\t")
        faults.setdefault(label, {}).setdefault(kind, {})[edge] = int(when)

    report = {}
    for label, fault_times in faults.items():
        rows = [tuple(map(int, line.split())) for line in (out / f"{label}.probe.tsv").read_text().splitlines()]
        found = windows(rows)
        by_kind = {"stop": [], "split": []}
        unassociated = []
        for window in found:
            matches = [kind for kind in ("stop", "split") if
                       window["first_failed_start_ns"] <= fault_times[kind]["end"] and
                       window["last_failed_end_ns"] >= fault_times[kind]["begin"]]
            if len(matches) == 1:
                by_kind[matches[0]].append(window)
            else:
                unassociated.append(window)
        report[label] = {"unassociated_failure_windows": unassociated}
        for kind, group in by_kind.items():
            lo, hi = fault_times[kind]["begin"], fault_times[kind]["end"]
            successful_latencies = [(end - start) / 1e9 for start, end, bad in rows
                                    if not bad and start <= hi and end >= lo]
            bounded = [w["success_bracket_s"] for w in group if w["success_bracket_s"] is not None]
            report[label][kind] = {
                "failed_samples": sum(w["failed_samples"] for w in group),
                "observed_windows": len(group),
                "max_success_bracket_s": max(bounded) if group and len(bounded) == len(group) else None,
                "max_successful_probe_latency_s": round(max(successful_latencies), 3)
                if successful_latencies else None,
                "windows": group,
            }

    aggregate = {}
    settings = sorted({label.rsplit("-", 1)[0] for label in report})
    for setting in settings:
        aggregate[setting] = {}
        labels = sorted(k for k in report if k.startswith(setting + "-"))
        for kind in ("stop", "split"):
            samples = [report[label][kind]["failed_samples"] for label in labels]
            brackets = [report[label][kind]["max_success_bracket_s"] for label in labels]
            latencies = [report[label][kind]["max_successful_probe_latency_s"] for label in labels]
            aggregate[setting][kind] = {
                "trials": len(labels),
                "failed_samples": samples,
                "max_success_bracket_s": brackets,
                "max_successful_probe_latency_s": latencies,
                "median_bracket_s": statistics.median(brackets)
                if brackets and all(x is not None for x in brackets) else None,
                "median_observed_bracket_s": statistics.median(x for x in brackets if x is not None)
                if any(x is not None for x in brackets) else None,
            }
    result = {"trials": report, "aggregate": aggregate,
              "caveat": "A null bracket means the failed window lacks bounding successful calls, or no failure was sampled; inspect failed_samples to distinguish these. Timeouts bound outages only between adjacent successful completions. Calls are serial with variable duration; unassociated failures are reported separately."}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: gray-report.py <gray output directory>")
    main(Path(sys.argv[1]))
