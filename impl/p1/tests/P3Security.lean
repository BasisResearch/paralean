import Paralean.P3

open Lean Paralean Paralean.P3 System

def expectError (result : Except String α) (label : String) : IO Unit :=
  if result.isOk then throw <| IO.userError s!"{label}: accepted invalid input" else pure ()

def expectOk (result : Except String α) (label : String) : IO α :=
  match result with
  | .ok x => pure x
  | .error e => throw <| IO.userError s!"{label}: {e}"

def hexBytes (hex : String) : IO ByteArray :=
  match Ed25519.hexToBytes hex with
  | some bytes => pure bytes
  | none => throw <| IO.userError "invalid test vector hex"

def main (args : List String) : IO UInt32 := do
  let [rootArg, authorityKey, issuer, validator, group, capsule, receiptId, jobId,
       weakReceiptId, vectorPath] := args
    | throw <| IO.userError "usage: P3Security ROOT AUTH ISSUER VALIDATOR GROUP CAPSULE RECEIPT JOB WEAK_RECEIPT VECTORS"
  let identity := ByteArray.mk (#[1] ++ Array.replicate 31 0)
  let identitySig := identity ++ ByteArray.mk (Array.replicate 32 0)
  let orderTwo := ByteArray.mk (#[0xfe] ++ Array.replicate 30 0xff ++ #[0x7f])
  for publicKey in [identity, ByteArray.mk (Array.replicate 32 0), orderTwo] do
    if Ed25519.verify publicKey (ByteArray.mk #[7]) identitySig then
      throw <| IO.userError "weak-key signature accepted"
  for (bytes, label) in [
      (ByteArray.mk #[0x80, 0x00], "nonminimal varint"),
      (ByteArray.mk (Array.replicate 11 0xff), "unbounded varint"),
      (ByteArray.mk (Array.replicate 9 0x80 |>.push 0x02), "varint overflow")] do
    expectError (PDec.uv.run (bytes, 0)) label
  let root := FilePath.mk rootArg
  let job ← expectOk (Job.parse (← IO.FS.readBinFile (root / "authority-job.bin"))) "authority job"
  let issuerJob ← expectOk (Job.parse (← IO.FS.readBinFile (root / "issuer-job.bin"))) "issuer job"
  let receipt ← expectOk (Receipt.parse (← IO.FS.readBinFile (root / "receipt.bin"))) "receipt"
  let wrongTarget ← expectOk (Receipt.parse (← IO.FS.readBinFile (root / "wrong-target.bin"))) "wrong-target receipt"
  let t : Trust := ⟨#[validator], authorityKey, #[("w0", issuer)], #[job.policy],
    #[toHex job.checker], job.base, job.policy, #[], #[(job.worker, "w0")]⟩
  let _ ← expectOk (t.admits receipt job group capsule) "authority target job"
  expectError (t.admits receipt issuerJob group capsule) "issuer target job"
  expectError (t.admits wrongTarget job group capsule) "mismatched target bytes"
  let bound ← expectOk (Job.parse (← IO.FS.readBinFile (root / "bound-job.bin"))) "batch-bound job"
  unless bound.batch == some (toHex (ByteArray.mk (Array.replicate 32 8))) && job.batch.isNone do
    throw <| IO.userError s!"batch-bound job: wrong batch {bound.batch}"
  for (file, label) in [("tag2", "job with trailing tag 2"), ("short-batch", "job with a 31-byte batch ID"),
      ("two-batches", "job with two batch fields"), ("batch-then-byte", "job with a byte after its batch")] do
    expectError (Job.parse (← IO.FS.readBinFile (root / s!"{file}-job.bin"))) label
  let m : Marker := ⟨"", group, #[], receiptId, "A.lean", none, 0, "", #[], #[], capsule, "", none⟩
  let first ← checkReceipt root m
  let _ ← expectOk first "first cached receipt"
  let other := String.ofList (List.replicate 64 'b')
  expectError (← checkReceipt root { m with batch := some other }) "record with another batch"
  expectError (← checkReceipt root m (staged := some other)) "staged record under an unbound job"
  -- batch members count only once their batch file lists them
  let kl := root / "known"
  IO.FS.createDirAll (kl / "p3" / "records")
  let hx (c : Char) := String.ofList (List.replicate 64 c)
  let rec_ (id : String) (batch : Option String) : Json :=
    Json.mkObj [("id", id), ("group", id), ("revisions", Json.arr #[]), ("receipt", id), ("file", "A.lean"),
      ("anchor", Json.null), ("lamport", (1 : Nat)), ("author", "00"), ("rootPath", Json.arr #[]),
      ("lineageKeys", Json.arr #[]), ("capsule", id), ("pid", id),
      ("batch", match batch with | some b => Json.str b | none => Json.null)]
  let tomb (id : String) (batch : String) : Json :=
    Json.mkObj [("id", id), ("file", "A.lean"), ("target", id), ("lamport", (2 : Nat)), ("author", "00"),
      ("batch", batch)]
  let put (n : String) (j : Json) : IO Unit := IO.FS.writeFile (kl / "p3" / "records" / n) j.compress
  put s!"m-{hx 'a'}.json" (rec_ (hx 'a') none)
  put s!"m-{hx 'b'}.json" (rec_ (hx 'b') (some (hx '1')))
  put s!"m-{hx 'c'}.json" (rec_ (hx 'c') (some (hx '2')))
  put s!"m-{hx 'd'}.json" (rec_ (hx 'd') (some (hx '1')))
  put s!"t-{hx 'e'}.json" (tomb (hx 'e') (hx '1'))
  put s!"t-{hx 'f'}.json" (tomb (hx 'f') (hx '2'))
  put s!"b-{hx '1'}.json" (Json.mkObj [("id", hx '1'), ("markers", toJson #[hx 'b']), ("tombstones", toJson #[hx 'e'])])
  let k ← Known.load kl
  unless k.markers.map (·.id) == #[hx 'a', hx 'b'] do
    throw <| IO.userError s!"unfiled batch marker: accepted invalid input ({k.markers.map (·.id)})"
  unless k.tombs.map (·.id) == #[hx 'e'] do
    throw <| IO.userError s!"unfiled batch tombstone: accepted invalid input ({k.tombs.map (·.id)})"
  IO.FS.writeBinFile (root / "p3" / "jobs" / s!"{jobId}.bin")
    (← IO.FS.readBinFile (root / "replacement-job.bin"))
  expectError (← checkReceipt root m) "replaced cached job"
  IO.FS.writeBinFile (root / "p3" / "jobs" / s!"{jobId}.bin")
    (← IO.FS.readBinFile (root / "authority-job.bin"))
  let weakMarker := { m with receipt := weakReceiptId }
  expectError (← checkReceipt root weakMarker) "weak-key cached receipt"
  let vectorJson ← expectOk (Json.parse (← IO.FS.readFile vectorPath)) "vector JSON"
  let rows : Array Json ← expectOk (vectorJson.getObjValAs? (Array Json) "vectors") "vectors"
  for row in rows do
    let label : String ← expectOk (row.getObjValAs? String "case") "vector case"
    let message ← hexBytes (← expectOk (row.getObjValAs? String "message_hex") label)
    let publicKeyHex : String ← expectOk (row.getObjValAs? String "public_key_hex") label
    let publicKey ← hexBytes publicKeyHex
    let signature ← hexBytes (← expectOk (row.getObjValAs? String "signature_hex") label)
    let expected : Bool ← expectOk (row.getObjValAs? Bool "expect") label
    unless Ed25519.verify publicKey message signature == expected do
      throw <| IO.userError s!"vector {label}: Lean Ed25519 result differs"
    -- A noncanonical point encoding must not decode at all. At the signature level
    -- these vectors also fail for other reasons, so decoding is checked directly.
    let kind : String ← expectOk (row.getObjValAs? String "kind") label
    if kind == "noncanonical_A" && (Ed25519.decodePoint (Ed25519.leNat publicKey 0 32)).isSome then
      throw <| IO.userError s!"vector {label}: noncanonical point decoded"
    let vectorTrust := { t with validators := #[publicKeyHex] }
    let vectorReceipt := { receipt with id := message, key := publicKey, sig := signature }
    unless (vectorTrust.admits vectorReceipt job group capsule).isOk == expected do
      throw <| IO.userError s!"vector {label}: P3 admission result differs"
  IO.println "P3 security checks passed"
  return 0
