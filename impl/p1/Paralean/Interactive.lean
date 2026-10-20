import Paralean.Copy

/-! One persistent capture worker per document. JSON lines are an internal worker
protocol; the editor still uses ordinary Lean LSP. No publication happens here. -/
namespace Paralean.Interactive
open Lean System

def registryIdentity (dir : FilePath) : IO String := do
  let mut parts : Array String := #[]
  for sub in ["p3/records", "p3/revisions"] do
    let path := dir / "cache" / sub
    if ← path.pathExists then
      for entry in (← path.readDir).qsort (fun a b => a.fileName < b.fileName) do
        if entry.fileName.endsWith ".json" then
          parts := parts.push (entry.fileName ++ ":" ++ Sha256.hashHex (← IO.FS.readBinFile entry.path))
  if let some trust ← IO.getEnv "PARALEAN_TRUST" then
    parts := parts.push (Sha256.hashHex (← IO.FS.readBinFile trust))
  return Sha256.hashHex (String.intercalate "\n" parts.toList).toUTF8

unsafe def serve (dir : FilePath) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut version : Nat := 0
  let mut started := false
  let mut document := ""
  let mut environment := ""
  let mut registry := ""
  let mut generation : Nat := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let result ← try
      let request ← P3.ofExcept "<capture request>" (Json.parse line)
      let file ← P3.ofExcept "<capture request>" (request.getObjValAs? String "file")
      let text ← P3.ofExcept "<capture request>" (request.getObjValAs? String "text")
      let nextVersion ← P3.ofExcept "<capture request>" (request.getObjValAs? Nat "version")
      let env ← P3.ofExcept "<capture request>" (request.getObjValAs? String "environment")
      let gen ← P3.ofExcept "<capture request>" (request.getObjValAs? Nat "generation")
      if file.startsWith "/" || (file.splitOn "/").contains ".." then
        throw <| IO.userError "capture: file must be relative to the workspace"
      if started && (document != file || environment != env || generation != gen) then
        throw <| IO.userError "capture: document/environment/generation changed; restart the worker"
      if started && nextVersion ≤ version then
        throw <| IO.userError "capture: stale document version"
      let t0 ← IO.monoMsNow
      let nextRegistry ← registryIdentity dir
      if !started || registry != nextRegistry then
        Remote.resetSessionCaches
      else
        -- Registry files cannot express a newly revoked validator key. Recheck the
        -- mutable receipt policy even for remote constants in the retained prefix.
        for ((_, pid), _) in (← Remote.verifiedCache.get).toList do
          Remote.checkReceipt (← Remote.getMetaIO pid)
      let captured ← Copy.capture dir file IO.eprintln (input? := some text)
        (incrementalKey := some (env ++ ":" ++ nextRegistry))
      unless (← registryIdentity dir) == nextRegistry do
        throw <| IO.userError "capture: registry changed during elaboration; retry against its new environment"
      started := true
      document := file
      environment := env
      generation := gen
      registry := nextRegistry
      version := nextVersion
      pure <| Json.mkObj [
        ("file", toJson file), ("version", toJson version), ("environment", toJson environment),
        ("generation", toJson generation), ("registry", toJson registry),
        ("reusedCommands", toJson (← captureReusedCommands.get)),
        ("newCommands", toJson (← captureNewCommands.get)),
        ("ms", toJson ((← IO.monoMsNow) - t0)), ("capture", captured)]
    catch e =>
      pure <| Json.mkObj [("error", toJson e.toString)]
    stdout.putStrLn result.compress
    stdout.flush

end Paralean.Interactive
