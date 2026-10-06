import Lean
import Paralean.Materialize
import Paralean.Receipt

/-! Trusted validator (prototype): source replay + stock-kernel replay + axiom audit of
every current group; receipts only for groups that pass. -/

namespace Paralean
open Lean

unsafe def validateStore (store : Store) (key : String) (log : String → IO Unit := fun _ => pure ()) :
    IO (Nat × Array String) := do
  let files ← store.currentFiles
  let cat ← Catalog.load store files
  let pending ← cat.order.filterM fun gid => do return (← store.getReceipt? gid).isNone
  if pending.isEmpty then return (0, #[])
  let imports := cat.order.foldl (fun acc g => (cat.get! g).capsule.imports.foldl
    (fun acc m => if acc.contains m then acc else acc.push m) acc) #[]
  let sr ← sourceReplay cat cat.order imports (materialize? := some (materialize store))
  let (kr, _) ← kernelReplay store cat cat.order sr
  let mut n := 0
  let mut refused := #[]
  for gid in pending do
    let g := cat.get! gid
    let ok := (sr.results.find? (·.gid == gid)).any (·.ok) && (kr.find? (·.gid == gid)).any (·.ok)
    if ok then
      store.putReceipt { pid := gid, declId := g.declId, validator := "p1-local",
                         mac := receiptMac key gid g.declId }
      n := n + 1
    else
      refused := refused.push gid
      log s!"  not receipted: {g.capsule.file}:{g.capsule.startLine} {g.short}"
  return (n, refused)

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
