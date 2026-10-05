module

public import Lean
public import Paralean.Sha256
public import Paralean.Store

@[expose] public section

/-!
Validator receipts (prototype). A receipt binds a validator identity to the exact package
ID and declaration ID it checked: `mac = HMAC-SHA256(key, "paralean-receipt-v1|pid|declId")`.
The key stands in for a validator signature key; P3 replaces it with real signatures.
-/

namespace Paralean
open Lean System

def hmacSha256 (key msg : ByteArray) : ByteArray := Id.run do
  let key := if key.size > 64 then Sha256.hash key else key
  let mut k := key
  while k.size < 64 do k := k.push 0
  let mut ipad := ByteArray.empty
  let mut opad := ByteArray.empty
  for b in k do
    ipad := ipad.push (b ^^^ 0x36)
    opad := opad.push (b ^^^ 0x5c)
  Sha256.hash (opad ++ Sha256.hash (ipad ++ msg))

structure Receipt where
  pid : String
  declId : String
  validator : String
  mac : String
  deriving ToJson, FromJson, Inhabited, Repr

def receiptMac (key : String) (pid declId : String) : String :=
  Sha256.toHex (hmacSha256 key.toUTF8 s!"paralean-receipt-v1|{pid}|{declId}".toUTF8)

def Store.receiptPath (s : Store) (pid : String) : FilePath := s.root / "receipts" / s!"{pid}.json"

def Store.putReceipt (s : Store) (r : Receipt) : IO Unit := do
  IO.FS.createDirAll (s.root / "receipts")
  IO.FS.writeFile (s.receiptPath r.pid) (toJson r).compress

def Store.getReceipt? (s : Store) (pid : String) : IO (Option Receipt) := do
  let p := s.receiptPath pid
  unless ← p.pathExists do return none
  match Json.parse (← IO.FS.readFile p) >>= fromJson? with
  | .ok r => return some r
  | .error _ => return none

/-- Check a receipt against the key, the package ID and the declaration ID. -/
def Receipt.valid (r : Receipt) (key pid declId : String) : Bool :=
  r.pid == pid && r.declId == declId && r.mac == receiptMac key pid declId

end Paralean
