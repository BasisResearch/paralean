# W1 export lookup guard check

The parent-run `check-export-lookup-mutations.sh` passed against the first
lookup repair and was independently repeated against the final stock P1
library on 2026-10-20. The top-level logs retain the earlier measurement;
`parent-final2/first/` contains the final-library run and its source hashes.
It used the captured F13 store and its exported
`Fixtures.F13InitDecl.olean`, then compiled two private copies of
`Paralean/Export.lean`. It did not edit production source.

| Run | Exact source change in private copy | Required result |
|---|---|---|
| `baseline-f13.log` | none | F13 raw hygiene keys match and duplicate use is rejected |
| `baseline-ambiguous.log` | none | two distinct exported constants with one raw key are rejected |
| `no-reuse-test.log` | `if used.contains n then` → `if false then` | executable F13 test fails because a second captured group reused one exported member |
| `no-singleton-test.log` | `if q.size == 1 then q[0]?` → nonempty queue check | executable ambiguity test fails because the first of two candidates was selected |

The mutation runner requires each negative execution to exit unsuccessfully
with the expected diagnostic. `MANIFEST.sha256` records the checked production
source, test sources, and copied textual logs. To reproduce, run
`impl/p1/scripts/check-export-lookup-mutations.sh F13_STORE F13_EXPORTED_OLEAN`
with `PARALEAN_LIB` set to the P1 library under test; the script writes its
complete logs and source hash manifest under the chosen work directory.

The second-pass residual lookup was checked with
`check-export-lookup-residual-mutations.sh`. Its generated module has an exact
owner whose stored ID is deliberately invalid, a residual that could steal its
candidate, an ambiguous full-key owner with another residual and a third
unclaimed exported candidate, two captures for one candidate, two candidates
for one capture, and an F10-like exact-scope-5 / residual-scope-22 /
exported-scope-28 case. The baseline associates the F10-like pair and the
unique residual of the ambiguous owner, while rejecting the ambiguous owner
and the other ambiguous cases. Four private-source mutations of
`exactClaimed`, `residualCount`, candidate singleton selection, and the
`q.isEmpty` fallback guard each fail a targeted executable assertion. The
production lookup source was not mutated. The final-stock run logs are under
`residual-final4/`. The primary agent independently reran this final fixture
and all four residual mutations against the frozen final stock library;
those logs are in `parent-residual-final4/`.
The older `parent-final2/residual/` run predates the added third-candidate
fixture and covers the original three residual mutations; it is supplementary
history rather than evidence for the new fallback-eligibility mutation.
Run with `PARALEAN_LIB` set to the library under test and an optional work
directory; the runner writes logs and `MANIFEST.sha256` there.

`m17-encoded-diff.tsv` and `m08-encoded-diff.tsv` compare the captured canonical
group objects with an exact re-encoding of the existing stock-built export
`.olean`s; their `-fork` counterparts do the same for the pinned Lean fork.
`DumpExistingExportGroup.lean` writes the exported group bytes and IDs;
`summarize-export-group-diff.py` parses canonical sections and counts the
module-sensitive markers specifically in the **expression** section. Each
run's stdout is retained as `m17-dump-stock.log`, `m17-dump-fork.log`,
`m08-dump-stock.log`, or `m08-dump-fork.log`. `encoded-evidence.sha256` hashes
those text artifacts and their generating source. For example, reproduce M17
with the stock `LEAN_PATH` including the final P1 library and Mathlib dependencies:

```sh
mkdir -p .runs/w1/identity/m17-exported-groups
lean --run impl/p1/tests/DumpExistingExportGroup.lean \
  .runs/w1/gate-stock/mathlib/M17/store \
  .runs/w1/gate-stock/mathlib/M17/export \
  .runs/w1/p1-stock-final2/.lake/build/lib/lean "$(lean --print-prefix)" \
  all .runs/w1/identity/m17-exported-groups \
  > .runs/w1/identity/m17-all-dump.log
python3 impl/p1/scripts/summarize-export-group-diff.py \
  .runs/w1/gate-stock/mathlib/M17/store/objects \
  .runs/w1/identity/m17-all-dump.log \
  .runs/w1/identity/m17-exported-groups
```

The run's relevant toolchain is the pinned stock nightly; the corresponding
fork run requires the pinned fork's `lean`, P1 library, and Mathlib dependency
path. No bytes are trimmed or replaced before the comparison. The section
parser reports the equality of the complete canonical name, reference, and
level sections; expression entries and literal marker counts expose the
specific content change. A changed exact ID remains a rejection, regardless
of whether a restricted metaprogram might admit a separate semantic proof.
