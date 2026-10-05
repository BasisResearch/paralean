import Lean
import Paralean.Remote
import Paralean.Crdt

/-!
Cross-file visibility of published declarations (stand-in for a fork hook in name
resolution). At host start-up, when `PARALEAN_STORE` and `PARALEAN_VISIBILITY` are set,
every published public name (as rendered, i.e. after collision renaming) is registered
through Lean's reserved-name mechanism:

* the predicate makes `resolveGlobalName` consider the name although it is not in the
  environment; it is active only in environments that import `Paralean.Remote` (working
  copies), and is suspended while a published package is being loaded;
* the action loads the package (receipt, closure and content checks as for `remote%`)
  when ordinary name resolution reaches the name.

Every path that resolves reserved names (terms, `rw`, `simp [...]`, `#check`, …)
therefore sees published declarations on demand, without imports and without a text
scan. Fork location: `Lean/ResolveName.lean` `resolveGlobalName` /
`Lean/ReservedNameAction.lean` `realizeGlobalName`, which would consult the registry
directly instead of being routed through the reserved-name tables.
-/

namespace Paralean.Visibility
open Lean

/-- Reads mutable state, so it must not be a closed term (the compiler would evaluate a
closed `isLoading ()` once); it takes the queried name. -/
unsafe def isLoadingImpl (n : Name) : Bool := unsafeBaseIO do
  let d ← Remote.loadingDepth.get
  if (← IO.getEnv "PARALEAN_DEBUG_VIS").isSome then
    discard <| (IO.eprintln s!"isLoading {n} depth={d}").toBaseIO
  return d > 0
@[implemented_by isLoadingImpl, noinline] opaque isLoading : Name → Bool

/-- Rendered public name ↦ package, from the store's publication records. -/
def buildIndex (store : Store) : IO (Std.HashMap Name String) := do
  let recs ← store.pubs
  let metas ← metasFor store recs
  let ren := renamesOf metas recs
  let mut idx : Std.HashMap Name String := {}
  for r in recs do
    if let some g := metas[r.pid]? then
      for n in g.publicNames do
        idx := idx.insert (renameName (ren.getD r.pid {}) n) r.pid
  return idx

initialize do
  let some root ← IO.getEnv "PARALEAN_STORE" | return
  if (← IO.getEnv "PARALEAN_VISIBILITY").isNone then return
  let index ← buildIndex { root }
  registerReservedNamePredicate fun env n =>
    index.contains n && !env.contains n && !isLoading n &&
      (env.getModuleIdx? `Paralean.Remote).isSome
  registerReservedNameAction fun n => do
    let some pid := index[n]? | return false
    if (← getEnv).contains n then return true
    Remote.loadInCore pid
    return true

end Paralean.Visibility
