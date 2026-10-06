import Lean
import Paralean.Materialize
import Paralean.Rga

/-!
Trusted validator (P3 stand-in until the control branch's validator lands): for each
requested package, source replay and stock-kernel replay of its dependency closure, an
axiom audit, and the reserved-name rule (§11.5: no group may declare a name in the fresh
namespace). The verdicts are signed by `plr validate` (Ed25519, `impl/p3-remote`).

The validator reads only its own cache, which `plr` filled from the store: payloads,
capsules and their dependency closures. It never reads a worker's files.
-/

namespace Paralean
open Lean

/-- A catalogue over the closure of `roots` in a cache (metadata from `meta/`). -/
partial def Catalog.ofStore (s : Store) (roots : Array String) : IO Catalog := do
  let mut metas : Std.HashMap String GroupRec := {}
  let mut order : Array String := #[]
  let mut state : Std.HashMap String Bool := {}  -- false: on stack, true: done
  for r in roots do
    let mut stack : Array (String × Bool) := #[(r, false)]
    while !stack.isEmpty do
      let (g, post) := stack.back!
      stack := stack.pop
      if post then
        state := state.insert g true
        unless order.contains g do order := order.push g
        continue
      if state.contains g then continue
      state := state.insert g false
      let m ← match metas[g]? with
        | some m => pure m
        | none => do let m ← s.getMeta g; pure m
      metas := metas.insert g m
      stack := stack.push (g, true)
      for d in (m.deps ++ m.feDeps).reverse do
        unless state.contains d do stack := stack.push (d, false)
  return { metas, order }

structure Verdict where
  ok : Bool
  reason : String
  axioms : Array Name
  replayMs : Nat
  deriving ToJson

/-- Validate `roots` (package IDs) against the closure held by `store`. -/
unsafe def validatePkgs (store : Store) (roots : Array String) (log : String → IO Unit := fun _ => pure ()) :
    IO (Std.HashMap String Verdict) := do
  let t0 ← IO.monoMsNow
  let cat ← Catalog.ofStore store roots
  let imports := cat.order.foldl (fun acc g => (cat.get! g).capsule.imports.foldl
    (fun acc m => if acc.contains m then acc else acc.push m) acc) #[]
  let sr ← sourceReplay cat cat.order imports (materialize? := some (materialize store))
  let (kr, _) ← kernelReplay store cat cat.order sr
  let ms := (← IO.monoMsNow) - t0
  let mut bad : Std.HashMap String String := {}
  for gid in cat.order do
    let g := cat.get! gid
    let mut why := #[]
    match sr.results.find? (·.gid == gid) with
    | some r => unless r.ok do why := why.push s!"source replay: {r.diags.map toString}"
    | none => why := why.push "not replayed"
    match kr.find? (·.gid == gid) with
    | some r => unless r.ok do why := why.push s!"kernel: {r.diags.map toString}"
    | none => why := why.push "not kernel-checked"
    for m in g.members do
      if m.cls != "scoped" && Rga.isReserved m.name then
        why := why.push s!"declares {m.name}, a name in the reserved fresh namespace"
    for d in g.deps ++ g.feDeps do
      if bad.contains d then why := why.push s!"depends on rejected {(d.take 12).toString}"
    unless why.isEmpty do
      bad := bad.insert gid ("; ".intercalate why.toList)
      log s!"  rejected {g.short}: {bad[gid]!}"
  let mut out := {}
  for r in roots do
    let axioms := (kr.find? (·.gid == r)).map (·.axioms) |>.getD #[]
    let v : Verdict := match bad[r]? with
      | some why => { ok := false, reason := why, axioms, replayMs := ms }
      | none => { ok := true, reason := "", axioms, replayMs := ms }
    out := out.insert r v
  return out

end Paralean
