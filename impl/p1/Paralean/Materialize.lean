import Lean
import Paralean.Export

/-!
Module boundaries for `initialize`.

An `initialize` command runs its initializer only when its module is *imported*. A
consumer in the same module, which is what the transparent prelude provides, can never
observe it. Groups with initializer effects are therefore materialized: their closure is
exported to a scratch Lake package, built with stock Lean, and imported as base modules
(with explicit artifacts). Their constants are mapped back to their package identities,
so consumers still pin exact package IDs.
-/

namespace Paralean
open Lean System

def hasInitEffect (g : GroupRec) : Bool :=
  g.touched.any fun (n, _) => n == `Lean.regularInitAttr || n == `Lean.builtinInitAttr

/-- Build `gids` (a dependency-closed set) as real modules; return how to import them. -/
unsafe def materialize (store : Store) (cat : Catalog) (gids : Array String) : IO MatResult := do
  let key := Sha256.hashHex (String.intercalate "," gids.toList).toUTF8
  let out := store.root / "materialized" / (key.take 16).toString
  let mathlib? := (← IO.getEnv "PARALEAN_MATHLIB").map FilePath.mk
  -- the directory is keyed by the group IDs, so a successful earlier build is reused
  let marker := out / ".paralean-built"
  let (plan, ok, log, ms) ← if ← marker.pathExists then
      pure ((← exportPlanFor cat gids), true, "", 0)
    else do
      let (plan, _) ← writeExport cat gids out mathlib?
      let (ok, log, ms) ← runBuild out
      if ok then IO.FS.writeFile marker ""
      pure (plan, ok, log, ms)
  if !ok then
    return { imports := #[], arts := {}, covered := #[], identOf := fun _ => {}, buildMs := ms
             diags := #[{ severity := "unsupported", code := "materialize-failed",
                          msg := s!"stock build of initializer groups failed: {(log.take 400).toString}" }] }
  let arts ← exportArts plan out
  return {
    imports := plan.modules.map fun m => { module := m.name }
    arts, covered := gids, buildMs := ms
    pkgs := gids.foldl (fun m gid => let g := cat.get! gid; m.insert gid (g.declId, g.members.map (·.local_))) {}
    identOf := fun env => (exportIdentity cat plan env).1
    diags := #[{ severity := "info", code := "materialized",
                 msg := s!"{gids.size} groups with initializer effects built as {plan.modules.size} module(s) in {ms} ms" }] }

end Paralean
