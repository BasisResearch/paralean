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

/-- Rendered public name ↦ package, over the live heads of the copy's view. The file being
elaborated (`PARALEAN_VIS_EXCLUDE`) is excluded: its own elements are in the file itself,
and a draft that revises one of them redeclares its name. -/
def excludedFile : IO (Option String) := do
  if let some file ← IO.getEnv "PARALEAN_VIS_EXCLUDE" then return some file
  let some path ← Fork.getDocumentPath | return none
  let some root ← IO.getEnv "PARALEAN_WORK_ROOT" | return none
  let rootPrefix := if root.endsWith "/" then root else root ++ "/"
  if path.startsWith rootPrefix then return some (path.drop rootPrefix.length).toString
  return none

def buildIndex : IO (Std.HashMap Name String) := do
  let v ← Remote.view
  let idx := v.index (← excludedFile)
  let mut out := {}
  for (n, group) in idx.toList do
    if let some m := v.known.byGroup[group]? then out := out.insert n m.pid
  return out

/-- A long-lived worker sees pulls and editor sessions without re-running module
initializers. The index follows the copy's records generation and excluded file. -/
initialize indexCache : IO.Ref (Nat × String × String × Std.HashMap Name String) ←
  IO.mkRef (0, "", "", {})

def currentIndex : IO (Std.HashMap Name String) := do
  let generation ← Remote.recordsVersion.get
  let root := (← IO.getEnv "PARALEAN_STORE").getD ""
  let exclude := (← excludedFile).getD ""
  let (seen, oldRoot, oldExclude, idx) ← indexCache.get
  if seen == generation && oldRoot == root && oldExclude == exclude then return idx
  let idx ← buildIndex
  indexCache.set (generation, root, exclude, idx)
  return idx

unsafe def hasReservedImpl (n : Name) : Bool := unsafeBaseIO do
  match ← EIO.toBaseIO currentIndex with
  | .ok idx => return idx.contains n
  | .error _ => return false
@[implemented_by hasReservedImpl, noinline] opaque hasReserved : Name → Bool

initialize do
  if (← IO.getEnv "PARALEAN_STORE").isNone then return
  if (← IO.getEnv "PARALEAN_VISIBILITY").isNone then return
  registerReservedNamePredicate fun env n =>
    hasReserved n && !env.contains n && !isLoading n &&
      (env.getModuleIdx? `Paralean.Remote).isSome
  registerReservedNameAction fun n => do
    let some pid := (← currentIndex)[n]? | return false
    if (← getEnv).contains n then return true
    Remote.loadInCore pid
    return true

end Paralean.Visibility
