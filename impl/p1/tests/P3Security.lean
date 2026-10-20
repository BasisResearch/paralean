import Paralean.P3

open Paralean Paralean.P3 System

def expectError (result : Except String α) (label : String) : IO Unit :=
  if result.isOk then throw <| IO.userError s!"{label}: accepted invalid input" else pure ()

def expectOk (result : Except String α) (label : String) : IO α :=
  match result with
  | .ok x => pure x
  | .error e => throw <| IO.userError s!"{label}: {e}"

def main (args : List String) : IO UInt32 := do
  let [rootArg, authorityKey, issuer, validator, group, capsule, receiptId, jobId] := args
    | throw <| IO.userError "usage: P3Security ROOT AUTH ISSUER VALIDATOR GROUP CAPSULE RECEIPT JOB"
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
  let m : Marker := ⟨"", group, #[], receiptId, "A.lean", none, 0, "", #[], #[], capsule, ""⟩
  let first ← checkReceipt root m
  let _ ← expectOk first "first cached receipt"
  IO.FS.writeBinFile (root / "p3" / "jobs" / s!"{jobId}.bin")
    (← IO.FS.readBinFile (root / "replacement-job.bin"))
  expectError (← checkReceipt root m) "replaced cached job"
  IO.println "P3 security checks passed"
  return 0
