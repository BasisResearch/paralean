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

/-! ## P3 validator: one group from its exact dependencies

`checkGroup` is what the P3 validator service runs (as `paralean check-group`). The job's
input store holds the group and its dependency closure only, each object re-hashed on read.
Every group of the closure is source-replayed (it must reproduce its declaration ID) and
kernel-replayed with the stock kernel; axioms are read from the kernel environment, never
from worker metadata. A pinned target's statement hash is compared with the hash that the
validator's own replay re-derives. -/

namespace Paralean
open Lean

structure CheckResult where
  declId : String
  gid : String := ""
  ok : Bool
  /-- Declaration IDs of the rebuilt closure, dependencies first, the group last. -/
  closure : Array String := #[]
  /-- Transitive axioms of the group's members, from the kernel environment. -/
  axioms : Array Name := #[]
  publicNames : Array Name := #[]
  /-- (member name, statement hash) of the group, as re-derived by source replay. -/
  statements : Array (Name × String) := #[]
  /-- Every pinned target is declared with its statement hash (`none`: no target). -/
  targetOk : Option Bool := none
  diags : Array String := #[]
  deriving ToJson

unsafe def checkGroup (store : Store) (gids : Array String) (declId : String)
    (targets : Array TargetContract := #[]) : IO CheckResult := do
  let fail (msg : String) : CheckResult := { declId, ok := false, diags := #[msg] }
  let file : FileRec := { (default : FileRec) with workspace := "validator", file := "<job>", groups := gids }
  let cat ← try Catalog.load store #[file] catch e => return fail s!"load: {e}"
  let some root := cat.order.find? (fun g => (cat.get! g).declId == declId)
    | return fail "no group of the job has this declaration ID"
  let clo ← match cat.closure #[root] with
    | .ok c => pure c
    | .error e => return fail e
  let imports := clo.foldl (fun acc g => (cat.get! g).capsule.imports.foldl
    (fun acc m => if acc.contains m then acc else acc.push m) acc) #[]
  let res ← try
      let sr ← sourceReplay cat clo imports (materialize? := some (materialize store))
      let (kr, _) ← kernelReplay store cat clo sr
      pure (Except.ok (sr, kr))
    catch e => pure (Except.error s!"replay: {e}")
  let (sr, kr) ← match res with
    | .ok v => pure v
    | .error e => return fail e
  let mut diags : Array String := #[]
  for gid in clo do
    let short := ((cat.get! gid).declId.take 12).toString
    match sr.results.find? (·.gid == gid) with
    | some r => unless r.ok do diags := diags ++ #[s!"source replay of {short} failed"] ++ r.diags.map toString
    | none => diags := diags.push s!"source replay of {short} missing"
    match kr.find? (·.gid == gid) with
    | some r => unless r.ok do diags := diags ++ #[s!"kernel replay of {short} failed"] ++ r.diags.map toString
    | none => diags := diags.push s!"kernel replay of {short} missing"
  -- §11.5 (P3 transparent workspaces): no group declares a name in the reserved fresh namespace
  for m in (cat.get! root).members do
    if m.cls != "scoped" && Rga.isReserved m.name then
      diags := diags.push s!"the group declares {m.name}, a name in the reserved fresh namespace"
  let replayed := (sr.results.find? (·.gid == root)).bind (·.replayed)
  let statements := (replayed.map (·.members.map fun m => (m.name, m.typeHash))).getD #[]
  let declares (t : TargetContract) : Bool :=
    (replayed.map (·.members.any fun m => (m.name == t.name || m.local_ == t.name) &&
      (t.typeHash.isEmpty || m.typeHash == t.typeHash))).getD false
  let targetOk := if targets.isEmpty then none else some (targets.all declares)
  for t in targets do
    unless declares t do diags := diags.push s!"the group does not declare target {t.name} with the pinned statement"
  return { declId, gid := root, ok := diags.isEmpty, closure := clo.map (cat.get! · |>.declId)
           axioms := ((kr.find? (·.gid == root)).map (·.axioms)).getD #[]
           publicNames := (replayed.map (·.publicNames)).getD (cat.get! root).publicNames
           statements, targetOk, diags }

end Paralean
