import Paralean.Copy

/-! Report exactly the package closure selected by P1's stock export. The P5
checkpoint uses its published revisions, never a scan of historical markers. -/

open Lean Paralean System

unsafe def main (args : List String) : IO UInt32 := do
  let dir ← match args with
    | ["--dir", path] => pure (FilePath.mk path)
    | _ => IO.eprintln "usage: lean --run Snapshot.lean --dir WORKSPACE"; return 2
  let v ← Remote.view
  let cache : Store := { root := dir / "cache" }
  let roots := (v.known.markers.filter fun m => v.live.contains m.group).map (·.pid)
  let cat ← Catalog.ofStore cache roots
  let mut rows : Array Json := #[]
  for pid in cat.order do
    let group := (cat.get! pid).declId
    let some marker := v.known.byGroup[group]?
      | throw <| IO.userError s!"export package {pid} has no published marker"
    rows := rows.push <| Json.mkObj [
      ("group", toJson group), ("file", toJson marker.file),
      ("revisions", toJson marker.revisions),
      ("current", toJson (v.live.contains group))]
  IO.println <| (Json.mkObj [("groups", toJson rows)]).compress
  return 0
