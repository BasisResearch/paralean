import Lean
import Paralean.Store
import Paralean.P3

/-!
Test-only: forge a group whose published proof is ill-typed (P3 gate, forged `remote%`).

`forgeProof` takes a stored group (typically a `theorem … := sorry` that capture rejected,
kept in the audit namespace), replaces its public theorem's proof by `@Eq.refl Nat 1`, and
re-encodes it. The result is a well-formed package with a fresh group ID whose statement
and proof disagree: only a kernel check of the fetched proof can reject it. The gate has a
compromised validator sign it (the trusted key, misused) and checks that working copies
reject it at `remote%`.
-/

namespace Paralean.Forge
open Lean

/-- Reversible spelling of a `Ref` as a name (decode, then encode again). -/
partial def refName : Ref → Name
  | .base n => n
  | .self l => `_fself ++ l
  | .dep pid l => (`_fdep ++ Name.mkSimple pid) ++ l
  | .res r s => (`_fres ++ Name.mkSimple (toString (refName r).components.length)) ++ refName r ++ s

def ofComps (cs : List Name) : Name := cs.foldl (· ++ ·) .anonymous

partial def nameRef (n : Name) : Except String Ref :=
  match n.components with
  | `_fself :: rest => .ok (.self (ofComps rest))
  | `_fdep :: p :: rest => .ok (.dep p.toString (ofComps rest))
  | `_fres :: k :: rest => do
    let some k := k.toString.toNat? | throw "forge: bad res"
    let r ← nameRef (ofComps (rest.take k))
    return .res r (ofComps (rest.drop k))
  | _ => .ok (.base n)

/-- Forge `pid`'s package in `store` (publishable or audit namespace); writes the new
package into the publishable namespace and returns (pid, group). -/
def forgeProof (store : Store) (pid : String) : IO (String × String) := do
  let s := { store with auditRead := true }
  let g ← s.getMeta pid
  let bytes ← s.getObject g.declId
  let metas ← (g.deps ++ g.feDeps).mapM fun d => do return (d, ← s.getMeta d)
  let find (p : String) : Option GroupRec := (metas.find? (·.1 == p)).map (·.2)
  let dg ← match decodeGroup bytes (g.unwire find) (fun r => .ok (refName r)) with
    | .ok dg => pure dg
    | .error e => throw <| IO.userError s!"forge: {e}"
  let members : Array EncMember := dg.members.map fun (l, cls, ci) =>
    let ci := match ci, cls with
      | .thmInfo v, .pub => .thmInfo { v with
          value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 1) }
      | ci, _ => ci
    { local_ := l, cls, info := ci }
  -- keep only the public members (the sorry proof's auxiliaries are dropped)
  let members := members.filter (·.cls == .pub)
  let wire := WireCtx.ofMembers members (wireDepOf find)
  let out ← match encodeGroup dg.baseId members nameRef wire with
    | .ok b => pure b
    | .error e => throw <| IO.userError s!"forge: {e}"
  let declId ← store.putObject out
  let g' := { g with declId, diags := #[], members := g.members.filter (·.cls == "pub"),
                     axioms := #[] }
  let g' := { g' with gid := P3.packageIdOf g' }
  store.putMeta g'
  -- its capsule object (the metadata JSON as stored)
  let cbytes ← IO.FS.readBinFile (store.metaPath g'.gid)
  IO.FS.createDirAll (store.root / "p3" / "capsules")
  IO.FS.writeBinFile (store.root / "p3" / "capsules" / s!"{P3.capsuleIdOf cbytes}.json") cbytes
  return (g'.gid, declId)

end Paralean.Forge
