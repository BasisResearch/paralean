module

public import Lean
public import Paralean.Model
public import Paralean.Store
public import Paralean.Encode
public import Paralean.Ed25519

@[expose] public section

/-!
P3 records in a working copy's local cache, and validator receipts.

`impl/p3-remote` (`plr`) delivers records from the P2 store into `<cache>/p3/`
(layout in `impl/p3-remote/src/cache.rs`). This module reads them and checks receipts
itself: a receipt is P2's `Signed<ReceiptBody>` (p0-interfaces §6), an Ed25519 signature
by a trusted validator over the body ID. It must name the exact group, answer the check
request `H("v0/job", PCE(groupID, capsuleID))` (so it pins the capsule as well), carry
the trusted base and policy, accept, and list only allowed axioms. Trusted keys, base and
policy come from `$PARALEAN_TRUST` (written by `plr keys-init`).

Payloads and records missing from the cache are fetched on demand with
`$PARALEAN_PLR fetch-group|fetch-pkg`; every fetched byte is re-hashed before use.
-/

namespace Paralean.P3
open Lean System

/-! ## Records -/

structure Marker where
  id : String
  group : String
  revisions : Array String
  receipt : String
  file : String
  anchor : Option String
  lamport : Nat
  author : String
  /-- Anchor path of the lineage root, file start first: (group, lamport, author). -/
  rootPath : Array (String × Nat × String)
  /-- Per public name: the lowest key in its lineage. -/
  lineageKeys : Array (Name × Nat × String)
  capsule : String
  pid : String
  deriving Inhabited, Repr, BEq

structure Tomb where
  id : String
  file : String
  target : String
  lamport : Nat
  author : String
  deriving Inhabited, Repr, BEq

structure Rev where
  id : String
  group : String
  name : Name
  parents : Array String
  capsule : String
  workspace : String
  deriving Inhabited, Repr

def jStr (j : Json) (k : String) : Except String String := j.getObjValAs? String k
def jNat (j : Json) (k : String) : Except String Nat := j.getObjValAs? Nat k
def jStrs (j : Json) (k : String) : Except String (Array String) := j.getObjValAs? (Array String) k
def jName (j : Json) : Except String Name := fromJson? j

def triple (j : Json) : Except String (Json × Nat × String) := do
  let a ← j.getArr?
  unless a.size == 3 do throw "expected a triple"
  return (a[0]!, ← fromJson? a[1]!, ← fromJson? a[2]!)

def Marker.ofJson (j : Json) : Except String Marker := do
  let anchor : Option String := match j.getObjVal? "anchor" with
    | .ok (.str s) => some s
    | _ => none
  let rp ← (← j.getObjValAs? (Array Json) "rootPath").mapM fun x => do
    let (g, l, a) ← triple x
    return ((← fromJson? g : String), l, a)
  let lk ← (← j.getObjValAs? (Array Json) "lineageKeys").mapM fun x => do
    let (n, l, a) ← triple x
    return ((← jName n), l, a)
  return { id := ← jStr j "id", group := ← jStr j "group", revisions := ← jStrs j "revisions"
           receipt := ← jStr j "receipt", file := ← jStr j "file", anchor, lamport := ← jNat j "lamport"
           author := ← jStr j "author", rootPath := rp, lineageKeys := lk
           capsule := ← jStr j "capsule", pid := ← jStr j "pid" }

def Tomb.ofJson (j : Json) : Except String Tomb := do
  return { id := ← jStr j "id", file := ← jStr j "file", target := ← jStr j "target"
           lamport := ← jNat j "lamport", author := ← jStr j "author" }

def Rev.ofJson (j : Json) : Except String Rev := do
  return { id := ← jStr j "id", group := ← jStr j "group", name := ← jName (← j.getObjVal? "name")
           parents := ← jStrs j "parents", capsule := ← jStr j "capsule", workspace := ← jStr j "workspace" }

/-- Own key of a record: (Lamport time, author), compared lexicographically, the author
bytewise (equal-length lowercase hex compares like the bytes). -/
def keyLt (a b : Nat × String) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

def Marker.key (m : Marker) : Nat × String := (m.lamport, m.author)

/-- What a copy knows: the records `pull` delivered (the rendering input). -/
structure Known where
  markers : Array Marker := #[]
  tombs : Array Tomb := #[]
  revs : Std.HashMap String Rev := {}
  byGroup : Std.HashMap String Marker := {}
  deriving Inhabited

def readJson (p : FilePath) : IO Json := do
  match Json.parse (← IO.FS.readFile p) with
  | .ok j => return j
  | .error e => throw <| IO.userError s!"{p}: {e}"

def ofExcept (p : FilePath) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"{p}: {e}"

/-- Load the records under `<cache>/p3/<sub>` (`records` = known; `fetched` = loaded on
demand by `remote%`, never rendered). -/
def Known.load (root : FilePath) (subs : List String := ["records"]) : IO Known := do
  let mut k : Known := {}
  for sub in subs do
    let dir := root / "p3" / sub
    unless ← dir.pathExists do continue
    for e in ← dir.readDir do
      let n := e.fileName
      unless n.endsWith ".json" do continue
      if n.startsWith "m-" then
        let m ← ofExcept e.path (Marker.ofJson (← readJson e.path))
        unless k.byGroup.contains m.group do
          k := { k with markers := k.markers.push m, byGroup := k.byGroup.insert m.group m }
      else if n.startsWith "t-" then
        let t ← ofExcept e.path (Tomb.ofJson (← readJson e.path))
        unless k.tombs.any (·.id == t.id) do k := { k with tombs := k.tombs.push t }
  let rdir := root / "p3" / "revisions"
  if ← rdir.pathExists then
    for e in ← rdir.readDir do
      if e.fileName.endsWith ".json" then
        let r ← ofExcept e.path (Rev.ofJson (← readJson e.path))
        k := { k with revs := k.revs.insert r.id r }
  -- deterministic order (directory order is not)
  k := { k with markers := k.markers.qsort (fun a b => a.group < b.group),
                tombs := k.tombs.qsort (fun a b => a.id < b.id) }
  return k

/-! ## On-demand transfer -/

def plrPath : IO String := return (← IO.getEnv "PARALEAN_PLR").getD "plr"

/-- Run `plr` with a cache; returns its JSON output. -/
def plr (args : Array String) : IO Json := do
  let out ← IO.Process.output { cmd := ← plrPath, args }
  match Json.parse out.stdout.trimAscii.toString with
  | .ok j =>
    if let .ok e := j.getObjValAs? String "error" then
      throw <| IO.userError s!"plr {args[0]!}: {e}"
    return j
  | .error _ => throw <| IO.userError s!"plr {args}: {out.stderr}"

/-- A group's payload, fetched from the store on a cache miss; always re-hashed. -/
def payload (root : FilePath) (group : String) : IO ByteArray := do
  let s : Store := { root }
  unless ← s.hasObject group do
    discard <| plr #["fetch-group", "--cache", root.toString, group]
  s.getObject group

/-! ## Receipts -/

structure Receipt where
  /-- SHA-256 of the body preimage: what the signature covers. -/
  id : ByteArray
  group : String
  base : String
  key : ByteArray
  policy : String
  request : Option ByteArray
  accepted : Bool
  reason : String
  axioms : Array Name
  sig : ByteArray

def toHex (b : ByteArray) : String := Sha256.toHex b

namespace PDec
abbrev M := StateT (ByteArray × Nat) (Except String)
def byte : M UInt8 := do
  let (b, i) ← get
  unless i < b.size do throw "receipt: truncated"
  set (b, i + 1)
  return b[i]!
partial def uv : M Nat := do
  let x ← byte
  if x < 0x80 then return x.toNat
  return x.toNat % 0x80 + 0x80 * (← uv)
def bytes : M ByteArray := do
  let n ← uv
  let (b, i) ← get
  unless i + n ≤ b.size do throw "receipt: truncated"
  set (b, i + n)
  return b.extract i (i + n)
def id32 : M ByteArray := do
  let x ← bytes
  unless x.size == 32 do throw "receipt: bad ID length"
  return x
def opt (f : M α) : M (Option α) := do
  match ← byte with
  | 0 => return none
  | 1 => return some (← f)
  | _ => throw "receipt: bad option tag"
def str : M String := do
  match String.fromUTF8? (← bytes) with
  | some s => return s
  | none => throw "receipt: bad UTF-8"
def natBE : M Nat := do
  let b ← bytes
  return b.foldl (fun n x => n * 256 + x.toNat) 0
def name : M Name := do
  let n ← uv
  let mut out := Name.anonymous
  for _ in [0:n] do
    match ← byte with
    | 0 => out := .str out (← str)
    | 1 => out := .num out (← natBE)
    | _ => throw "receipt: bad name tag"
  return out
end PDec

def receiptPrefix : ByteArray := "paralean\x00v0/receipt\x00".toUTF8

/-- Parse P2's `Signed<ReceiptBody>`: `bytes(preimage) ‖ bytes(sig)`. -/
def Receipt.parse (raw : ByteArray) : Except String Receipt := do
  let ((pre, sig), (_, used)) ← (do
      let pre ← PDec.bytes
      let sig ← PDec.bytes
      return (pre, sig) : PDec.M _).run (raw, 0)
  unless used == raw.size do throw "receipt: trailing bytes"
  unless sig.size == 64 do throw "receipt: bad signature length"
  unless pre.size ≥ receiptPrefix.size && pre.extract 0 receiptPrefix.size == receiptPrefix do
    throw "receipt: not a v0/receipt preimage"
  let body := pre.extract receiptPrefix.size pre.size
  let (r, (_, used)) ← (do
      let fmt ← PDec.uv
      unless fmt == 0 do throw s!"receipt: unknown format {fmt}"
      let group ← PDec.id32
      let base ← PDec.id32
      let key ← PDec.id32
      let _bin ← PDec.bytes
      let policy ← PDec.id32
      let request ← PDec.opt PDec.bytes
      let _target ← PDec.opt PDec.bytes
      let (accepted, reason) ← match ← PDec.byte with
        | 0 => pure (true, "")
        | 1 => pure (false, ← PDec.str)
        | _ => throw "receipt: bad verdict"
      let n ← PDec.uv
      let mut axioms := #[]
      for _ in [0:n] do axioms := axioms.push (← PDec.name)
      return ({ id := Sha256.hash pre, group := toHex group, base := toHex base, key, policy := toHex policy
                request, accepted, reason, axioms, sig } : Receipt) : PDec.M Receipt).run (body, 0)
  unless used == body.size do throw "receipt: trailing body bytes"
  return r

structure Trust where
  validators : Array String
  base : String
  policy : String
  allowedAxioms : Array Name
  /-- AgentID (hex) ↦ agent name, for git authors and diagnostics. -/
  agents : Array (String × String) := #[]
  deriving Inhabited

def Trust.load : IO Trust := do
  let some p ← IO.getEnv "PARALEAN_TRUST" | throw <| IO.userError "PARALEAN_TRUST is not set"
  let j ← readJson p
  ofExcept p do
    let agents ← (← j.getObjValAs? (Array (Array String)) "agents").mapM fun a =>
      if a.size == 2 then pure (a[1]!, a[0]!) else throw "agents"
    return { validators := ← jStrs j "validators", base := ← jStr j "base", policy := ← jStr j "policy"
             allowedAxioms := (← jStrs j "allowedAxioms").map String.toName, agents }

initialize trustCache : IO.Ref (Option Trust) ← IO.mkRef none

def trust : IO Trust := do
  if let some t ← trustCache.get then return t
  let t ← Trust.load
  trustCache.set (some t)
  return t

def Trust.agentName (t : Trust) (id : String) : String :=
  (t.agents.find? (·.1 == id)).map (·.2) |>.getD (id.take 8).toString

/-- The check request a receipt answers (`impl/p3-remote/src/receipt.rs`). -/
def jobId (group capsule : String) : String :=
  let w : W := {}
  domainHash "v0/job" ((w.id group).id capsule).out

/-- §6 staging rule for working copies: `Ok` iff the receipt admits exactly (group, capsule). -/
def Trust.admits (t : Trust) (r : Receipt) (group capsule : String) : Except String Unit := do
  unless r.group == group do throw "the receipt names another group"
  unless r.request.map toHex == some (jobId group capsule) do
    throw "the receipt answers another request (group, capsule)"
  unless r.accepted do throw s!"the validator rejected it: {r.reason}"
  unless t.validators.contains (toHex r.key) do throw "the receipt is signed by an untrusted key"
  unless r.base == t.base && r.policy == t.policy do throw "the receipt is for another base or policy"
  unless Ed25519.verify r.key r.id r.sig do throw "the receipt's signature does not verify"
  for a in r.axioms do
    unless t.allowedAxioms.contains a do throw s!"the receipt lists axiom {a} outside the policy"

/-- Verified receipts, by (receipt, group, capsule). -/
initialize admitted : IO.Ref (Std.HashSet (String × String × String)) ← IO.mkRef {}

def checkReceipt (root : FilePath) (m : Marker) : IO (Except String Unit) := do
  let key := (m.receipt, m.group, m.capsule)
  if (← admitted.get).contains key then return .ok ()
  let p := root / "p3" / "receipts" / s!"{m.receipt}.bin"
  unless ← p.pathExists do return .error s!"no receipt {(m.receipt.take 12).toString} in the cache"
  let raw ← IO.FS.readBinFile p
  match Receipt.parse raw with
  | .error e => return .error e
  | .ok r =>
    unless toHex r.id == m.receipt do return .error "the cached receipt is not the one the record names"
    match (← trust).admits r m.group m.capsule with
    | .error e => return .error e
    | .ok () =>
      admitted.modify (·.insert key)
      return .ok ()

/-! ## Capsules -/

/-- The stored capsule object of a package: `{"rec": GroupRec, "deps": [[pid, group, capsule]]}`. -/
def capsuleBytes (rec : GroupRec) (deps : Array (String × String × String)) : ByteArray :=
  (Json.mkObj [("rec", toJson rec),
    ("deps", Json.arr (deps.map fun (p, g, c) => Json.arr #[p, g, c]))]).compress.toUTF8

def capsuleIdOf (bytes : ByteArray) : String := domainHash "v0/capsule" bytes

/-- P1's package ID (`Capture.packageId`): `H("v0/package", (declId, capsuleId))`. -/
def packageIdOf (g : GroupRec) : String :=
  let deps := (g.feDeps.qsort (· < ·)).toList.eraseDups.toArray
  let w : W := {}
  let w := (w.uv 0).str (toJson g.capsule).compress
  let cid := domainHash "v0/capsule" (deps.foldl W.id (w.uv deps.size)).out
  let w : W := {}
  domainHash "v0/package" ((w.id g.declId).id cid).out

/-- A package's metadata from its stored capsule, after re-hashing the capsule against the
ID the record names and checking that the package ID is the hash of its contents. -/
def loadCapsule (root : FilePath) (capsule : String) : IO (Except String (GroupRec × Array (String × String × String))) := do
  let p := root / "p3" / "capsules" / s!"{capsule}.json"
  unless ← p.pathExists do return .error s!"capsule {(capsule.take 12).toString} not in the cache"
  let bytes ← IO.FS.readBinFile p
  unless capsuleIdOf bytes == capsule do return .error s!"capsule {(capsule.take 12).toString} fails hash verification"
  let some txt := String.fromUTF8? bytes | return .error "capsule: bad UTF-8"
  match Json.parse txt with
  | .error e => return .error e
  | .ok j =>
    match (do
      let rec_ : GroupRec ← fromJson? (← j.getObjVal? "rec")
      let deps ← (← j.getObjValAs? (Array (Array String)) "deps").mapM fun a =>
        if a.size == 3 then pure (a[0]!, a[1]!, a[2]!) else throw "deps"
      return (rec_, deps) : Except String _) with
    | .error e => return .error e
    | .ok r =>
      unless packageIdOf r.1 == r.1.gid do
        return .error s!"capsule {(capsule.take 12).toString}: its package ID is not the hash of its contents"
      return .ok r

end Paralean.P3
