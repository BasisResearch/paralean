import Paralean

/-!
Persistent checker transport. Only `baseEnvCache` (immutable imported environments)
survives a request. `checkGroup` constructs a new Catalog, Session, command state,
kernel environment and axiom cache for every request, including successive dependent
groups. No checked workspace environment is reused as another request's base.

This provides environment isolation, not an OS sandbox for arbitrary Lean metaprograms.
The validator's watchdog kills and replaces the process on timeout, cancellation or
 memory excess. Initializer materialization uses a disposable process.
-/
open Lean Paralean System

structure WarmTarget where
  name : String
  statement : String := ""
  deriving FromJson

structure WarmRequest where
  nonce : String
  store : String
  gids : Array String
  decl : String
  targets : Array WarmTarget := #[]
  deriving FromJson

unsafe def setup : IO Unit := do
  let sysroot ← match ← IO.getEnv "PARALEAN_SYSROOT" with
    | some d => pure (FilePath.mk d)
    | none => findSysroot
  let gh ← IO.Process.output { cmd := (sysroot / "bin" / "lean").toString, args := #["--githash"] }
  unless gh.stdout.trimAscii.toString == Lean.githash do
    throw <| IO.userError "warm checker and Lean sysroot have different commits"
  let lib ← IO.getEnv "PARALEAN_LIB"
  initSearchPath sysroot (lib.toList.map FilePath.mk)
  if (← IO.getEnv "PARALEAN_NO_HOOKS").isNone then
    let u ← Fork.init
    unless u.simp do Hooks.installSimp
    unless u.instnames do InstName.install
  else
    Fork.setHooks {}
  enableInitializersExecution

unsafe def main : IO UInt32 := do
  setup
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let req : WarmRequest ← IO.ofExcept (Json.parse line >>= fromJson?)
    let result ← try
      modulePrefs.set (false, #[])
      InstName.chosen.set #[]
      let targets := req.targets.map fun t =>
        ({ name := t.name.toName, typeHash := t.statement } : TargetContract)
      -- W2-13: this process is the frontend; its evidence goes to a cold `kernel-check`.
      let (r, ev) ← sourceCheck { root := req.store } req.gids req.decl targets
      pure <| Json.mkObj [("nonce", toJson req.nonce), ("result", toJson r), ("evidence", evidenceToJson ev)]
    catch e =>
      pure <| Json.mkObj [("nonce", toJson req.nonce), ("error", toJson (toString e))]
    stdout.putStrLn s!"WARM {result.compress}"
    stdout.flush
  return 0
