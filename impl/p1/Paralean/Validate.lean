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
