#!/usr/bin/env python3
"""Kill selected rename safety guard mutants against the behavioral fixtures."""

from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import py_compile

P4 = Path(__file__).resolve().parents[1]
CASES = [
    ("standard multi-workspace refusal", "lsp.py",
     'if method == "textDocument/rename" and len(self.workspaces) > 1:',
     'if method == "textDocument/rename" and False:',
     "test_standard_rename_without_bridge_refuses_in_multiworkspace"),
    ("complete inventory", "rename_transaction.py",
     'inventory.get("complete") is not True', 'False',
     "test_incomplete_inventory_refuses_all"),
    ("uncertified source coverage", "rename_transaction.py",
     'if affected != set(owners):', 'if False:',
     "test_standalone_reference_outside_captured_groups_refuses_all"),
    ("captured source digest", "lsp.py",
     'source_digest(state["text"])):', 'captured.get("source_sha256")):',
     "test_uncaptured_dependency_refuses_all"),
    ("final environment stamp", "lsp.py",
     'ws.environment, ws.generation, state["version"], source_digest(state["text"])) != stamp:',
     'stamp[0], ws.generation, state["version"], source_digest(state["text"])) != stamp:',
     "test_environment_changes_during_planning_refuses_all"),
    ("postprobe final generation", "lsp.py",
     'if ws.refresh_environment() or state is None or (',
     'if False and (', "test_policy_probe_mutates_generation_refuses_all"),
    ("authoritative policy before commit", "lsp.py",
     'if hasattr(self.bridge, "assert_policy_fresh"):',
     'if False:', "test_policy_changes_during_planning_refuses_all"),
    ("definition member", "rename_transaction.py",
     'if not isinstance(name, str) or selected not in (name, name.rsplit(".", 1)[-1]):',
     'if False:', "test_origin_definition_misses_captured_member_refuses_all"),
    ("same definition across workers", "lsp.py",
     'elif (definition_actual, definition_range) != target_location:',
     'elif False:', "test_dependent_anchor_resolves_to_other_group_refuses_all"),
    ("rename plan covers anchor", "lsp.py",
     'if not anchor_covered(ws.open_documents[anchor_uri]["text"], position, edits[anchor_public]):',
     'if False:', "test_worker_edits_other_token_in_same_source_refuses_all"),
    ("origin anchor identity", "lsp.py",
     'if anchor_by_workspace[origin_ws.name][0] != origin_uri or anchor_by_workspace[origin_ws.name][1] != params.get("position"):',
     'if False:', "test_origin_anchor_mismatch_refuses_all"),
    ("cancel before commit", "lsp.py",
     'if client_id in self.cancelled or set(planned) != set(affected):',
     'if set(planned) != set(affected):',
     "test_cancellation_after_worker_plans_refuses_all"),
    ("all affected documents planned", "lsp.py",
     [('if not own_public.issubset(edits):', 'if False:'),
      ('if client_id in self.cancelled or set(planned) != set(affected):', 'if client_id in self.cancelled:')],
     None, "test_worker_omits_second_dependent_document_refuses_all"),
    ("worker agreement", "lsp.py",
     'if key in planned and planned[key] != updated:',
     'if False:', "test_disagreeing_cross_worker_edit_refuses_all"),
    ("all-buffer commit", "lsp.py",
     'for name, uri in sorted(planned):', 'for name, uri in sorted(planned)[:1]:',
     "test_two_workspace_commit"),
    ("worker edit version", "rename_transaction.py",
     'if version is not None and version != expected_versions[uri]:',
     'if False:', "test_stale_worker_edit_version_refuses_all"),
    ("unambiguous worker plan", "rename_transaction.py",
     'if (changes is None) == (document_changes is None):',
     'if False:', "test_ambiguous_worker_plan_refuses_all"),
    ("nonoverlapping worker edits", "rename_transaction.py",
     'if previous[1] > current[0] or previous[:2] == current[:2]:',
     'if False:', "test_overlapping_edits_refuse_all"),
]


def run(test_path, name):
    return subprocess.run([sys.executable, str(test_path), f"TransactionTests.{name}"],
                          capture_output=True, text=True, timeout=20)


def main():
    with tempfile.TemporaryDirectory(prefix="paralean-rename-mutants-") as temporary:
        temporary = Path(temporary)
        for filename in ("lsp.py", "rename_transaction.py"):
            shutil.copy2(P4 / filename, temporary / filename)
        test_path = temporary / "tests" / "rename_transaction_test.py"
        test_path.parent.mkdir()
        shutil.copy2(P4 / "tests" / "rename_transaction_test.py", test_path)
        baseline = subprocess.run([sys.executable, str(test_path)], capture_output=True,
                                  text=True, timeout=30)
        if baseline.returncode:
            raise AssertionError("baseline failed before mutation:\n" + baseline.stderr)
        for label, filename, old, new, test in CASES:
            path = temporary / filename
            source = (P4 / filename).read_text()
            patches = old if isinstance(old, list) else [(old, new)]
            mutated = source
            for before, after in patches:
                if before not in mutated:
                    raise AssertionError(f"mutation target missing: {label}")
                mutated = mutated.replace(before, after, 1)
            path.write_text(mutated)
            py_compile.compile(str(path), doraise=True)
            result = run(test_path, test)
            if result.returncode == 0 or "FAIL:" not in result.stderr or "ERROR:" in result.stderr:
                raise AssertionError(f"expected assertion failure missing for {label}:\n{result.stderr}")
            path.write_text(source)
            print(f"KILLED {label}")


if __name__ == "__main__":
    main()
