import Paralean

/-!
Private P5 contract compiler. Input is JSON `{"targets":[{"name":...,"statement":...}]}`.
It elaborates each frozen type behind an axiom in an ephemeral environment, then
uses exactly P1's `MemberRec.typeHash` encoding. No axiom is written to a
workspace, package, store, or exported module.
-/

open Lean Paralean System

private def inputPath (args : List String) : Except String FilePath :=
  match args with
  | ["--input", path] => .ok path
  | _ => .error "usage: lean --run Contract.lean --input targets.json"

private def targetPair (value : Json) : Except String (Name × String) := do
  let name : String ← value.getObjValAs? String "name"
  let statement : String ← value.getObjValAs? String "statement"
  if name.isEmpty || statement.trimAscii.toString.isEmpty then
    throw "contract target name and statement must be nonempty"
  if name.toList.any (fun c => !(c.isAlphanum || c == '_' || c == '.' || c == '\'')) then
    throw s!"unsafe Lean target name: {name}"
  return (name.toName, statement)

private def typeHash (before : Environment) (info : ConstantInfo) : Except String String := do
  let ax : ConstantInfo := .axiomInfo {
    name := info.name, levelParams := info.levelParams,
    type := info.type, isUnsafe := false }
  let statement : EncMember := { local_ := info.name, cls := .pub, info := ax }
  let resolve : Name → Except String Ref := fun c =>
    if (before.getModuleIdxFor? c).isSome then .ok (.base c)
    else .error s!"contract statement references non-base declaration {c}; freeze this target after its predecessor is published"
  let bytes ← encodeGroup baseId #[statement] resolve
    (WireCtx.ofMembers #[statement] (fun _ _ => none))
  return groupIdOf bytes

unsafe def main (args : List String) : IO UInt32 := do
  let path ← match inputPath args with
    | .ok p => pure p
    | .error e => IO.eprintln e; return 2
  let parsed ← match Json.parse (← IO.FS.readFile path) with
    | .ok j => pure j
    | .error e => IO.eprintln e; return 2
  let targets ← match (parsed.getObjValAs? (Array Json) "targets") with
    | .ok xs => pure xs
    | .error e => IO.eprintln e; return 2
  let mut pairs := #[]
  for value in targets do
    match targetPair value with
    | .ok pair => pairs := pairs.push pair
    | .error e => IO.eprintln e; return 2
  let source := String.intercalate "\n" (pairs.toList.map fun (name, stmt) => s!"axiom {name} : {stmt}") ++ "\n"
  let (session, inputCtx, parserState, _, diags, _) ← openSession source "<P5 private contracts>" `P5PrivateContracts
  if !diags.isEmpty then
    IO.eprintln s!"contract header error: {diags}"
    return 2
  let out ← IO.mkRef ([] : List (String × Json))
  let n ← IO.mkRef (0 : Nat)
  let _ ← runCommands session.cmdState inputCtx parserState fun r => do
    let i ← n.get
    if i < pairs.size then
      let name := pairs[i]!.1
      if r.msgs.any (·.severity == .error) then
        throw <| IO.userError s!"contract elaboration failed for {name}"
      let some info := r.envAfter.find? name
        | throw <| IO.userError s!"contract did not elaborate {name}"
      let hash ← match typeHash r.envBefore info with
        | .ok h => pure h
        | .error e => throw <| IO.userError e
      out.modify (· ++ [(name.toString, toJson hash)])
      n.set (i + 1)
    return none
  if (← n.get) != pairs.size then
    IO.eprintln s!"only {← n.get} of {pairs.size} contract declarations elaborated"
    return 2
  IO.println (Json.mkObj (← out.get)).compress
  return 0
