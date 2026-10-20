# W1 P1 gate remeasurement provenance

The machine-readable stock/fork comparison is in `w1-measurement.json`. The per-set
logs are under `w1-stock/` and `w1-fork/`; the gate work directories are private
`.runs/w1/gate-stock` and `.runs/w1/gate-fork`.

Both gate runs used private Mathlib and toolchain copies. Stock Lean is
`193c3589a4fc16c4059261ab38cfa365eb24f323`; the fork is
`99967f1ee50a1ee82bb178359ad95b723c8196a2`. Both Mathlib copies are at
`0575336843263378752eeb5f4c75a612327768a2`. The fork Mathlib cache was
rebuilt with Paralean mode off (2,354 jobs), then checked with
`LEAN_PARALEAN=1 lake build --no-build` (2,354/2,354). The stock Mathlib cache
and both fixture reference builds are private copies, with no hardlinks to the
shared caches.

The full capture/replay/build gates used the frozen first exporter fix in
`.runs/w1/p1-stock-final` and `.runs/w1/p1-fork-final`. The final identity
verification and final G1 replay use independent `p1-stock-final2` and
`p1-fork-final2` snapshots. Each final2 P1 snapshot built 80/80 jobs. The
final2 `Paralean/Export.lean` SHA-256 is
`429f2b0a43b8465b3506dc87fe234d7dc1ddf845772e6a1b3b07c8ac5c2743f1`;
the final2 stock and fork binaries are respectively
`6442bc7a11b04458fdc1b84c056f07fc70f6a03439f5897622b51ead8072993f`
and `217657e1f31ab6ab0eb6d1bd2c87d558b590180cf452d82cbc23507fe1776601`.
Among 25 production Lean source files (`Main.lean` and `Paralean/*.lean`), only
`Paralean/Export.lean` differs between the first-fix and final2 snapshots; the
delta is confined to `exportIdentity`. The `Replay.lean` source and compiled
OLean are byte-identical across each pair of snapshots.

`scripts/check-existing-export.sh` uses the production `exportPlanFor` and
`verifyExport` through `tests/VerifyExistingExport.lean` on the already-built
packages. It records each real exit code and every identity diagnostic. It
hashes generated `.lean`, `.olean`, `.olean.server`, `.olean.private`, and
`lakefile.toml` files before and after, refusing changed artifacts. There are
185 files per mode, including 38 OLean sidecars. `writeExport` and `runBuild`
are unchanged by the final2 source delta, so this checks final2 identity on
the exact built packages without a redundant Lake rebuild. The first stock
manifest covered only 147 files and was insufficient to reuse G4 because
`tools/Axioms.lean` imports OLean sidecars. It is retained as
`w1-stock/g4-reuse-incomplete.txt`; a fresh full stock G4 run replaces that
reuse claim. The fork G4 run directly checked the built fork packages, and
final2 verification did not change them.

`scripts/replay-existing-gates.sh` runs final2 source, kernel, and isolated G1
replay against every existing gate store, including the separate diagnostic
probe. Its per-set logs and binary/source hashes are under each mode's
`replay-final2/` directory. The original capture logs and rejection audit are
preserved; the final2 replay does not recapture or rewrite export packages.
Both final2 full replays pass source, kernel, and isolated checks for all
1,225 corpus groups in each mode; the separate diagnostic probe passes 8/8.
The captured G3 statistics retain the largest Mathlib p50 ratio 3.795918 and
p95 ratio 9.826087 (the historical gate rounds the latter to 9.8), with no
group above the p95 bound.

Export identity failures remain visible. On each mode, M08 `ByCases.lean:37`
is one `export-mismatch`, and M17 `Attr/Register.lean` has 20
`export-mismatch` diagnostics after successful member association. The final2
stock core is 85/85: F10 and all three F13 initializer groups now match their
stored IDs. G4's three missing reference names are M13's canonical
`@[to_dual]` instance names; every public member present in both builds has
the same axiom set. The G5 N5 store contains three accepted objects; its
rejected changed proof is not publishable. The aggregate checks
each N1–N6 block's capture exit, exact rejection codes, accepted-group counts,
and logged and persisted store counts. N1/N2/N3/N4/N6 have no published groups.
N5's three accepted groups comprise two from the original capture and the
valid revised value; its changed dependent proof fails elaboration. The N3
audit separately confirms the rejected group still fails kernel replay.

The stock and fork `summary-final2.md` tables combine final2 identity counts
with frozen capture/build data. Use `verify-existing-final2-complete/status.tsv`
for per-command identity exit codes: a nonzero exit for M08 or M17 is a
measured identity rejection, not a failed Lake build. The first-fix
`stage-status.tsv` records top-level script exits; the nested F15/F16/diagmap
subshells end with an `echo`, so their per-command `*-exit=` lines and build/
verify lines in the individual logs are the evidence for those stages.
