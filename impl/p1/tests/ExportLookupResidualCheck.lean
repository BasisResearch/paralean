import Paralean.Export

open Lean Paralean System

private def hygName (m : Name) (hash scope : Nat) (repeatTag := false) : Name :=
  let privateBase := Name.mkNum (`_private ++ m) 0
  let tagBase := Name.mkStr privateBase "_pl_12345678"
  let base := Name.mkStr
    (if repeatTag then Name.mkStr tagBase "_pl_12345678" else tagBase) "initFn"
  let imported := Name.mkNum ((Name.mkStr base "_@") ++ m) hash
  Name.mkNum (Name.mkStr (Name.mkStr imported "_hygCtx") "_hyg") scope

private def mkGroup (m : Name) (label : String) (hash scope : Nat) : GroupRec :=
  let gid := "12345678" ++ label
  let capsule : Capsule := {
    workspace := "fixture", file := "ExportLookupResidualFixture.lean", module := m,
    startLine := 1, endLine := 1, imports := #[`Lean], noncomputable_ := false,
    currNamespace := .anonymous, opens := #[], scopeCmds := #[], localEffects := #[],
    text := "", relocate := true }
  let member : MemberRec := {
    name := hygName m hash scope, local_ := Name.mkNum `initFn._hyg scope,
    cls := "scoped", kind := "axiom" }
  { gid := gid, declId := "invalid-stored-group-id", kind := "decl",
    cmdKind := .anonymous, members := #[member], realized := #[], deps := #[],
    feDeps := #[], feDepsConservative := #[], publicNames := #[], anchor := none,
    touched := #[], axioms := #[], capsule := capsule, diags := #[], encSize := 0 }

private def groupName (label : String) := "12345678" ++ label

unsafe def main (args : List String) : IO Unit := do
  let [oleanPath] := args |
    throw (IO.userError "usage: ExportLookupResidualCheck.lean EXPORTED_OLEAN")
  let m := `ExportLookupResidualFixture
  let specs : List (String × Nat × Nat) :=
    [("owner", 100, 5), ("early", 100, 9),
     ("ambiguous", 200, 5), ("ambigEarly", 200, 9),
     ("twoA", 300, 9), ("twoB", 300, 10),
     ("multi", 400, 9), ("stable", 500, 5), ("drift", 500, 22)]
  let groups := specs.map fun (label, hash, scope) => mkGroup m label hash scope
  let gids := groups.map (·.gid) |>.toArray
  let metas := groups.foldl
    (fun (a : Std.HashMap String GroupRec) g => a.insert g.gid g) {}
  let cat : Catalog := { metas := metas, order := gids }
  let plan := planExport cat gids
  let arts : NameMap ImportArtifacts := ({} : NameMap ImportArtifacts).insert m
    (.ofArrays #[#[FilePath.mk oleanPath]])
  let env ← importModules #[{ module := m }] {} (arts := arts) (level := .private)
  let some idx := env.getModuleIdx? m | throw <| IO.userError "module not imported"
  let namesInOLean := env.header.moduleData[idx.toNat]!.constNames
  unless namesInOLean.size == 9 do
    throw <| IO.userError s!"expected nine generated fixture constants, got {namesInOLean.size}"
  let (_, names, diags) := exportIdentity cat plan env
  let assigned (label : String) := (names.getD (groupName label) #[]).size
  unless assigned "owner" == 1 do
    throw <| IO.userError "exact owner was not associated with its full-key candidate"
  unless assigned "stable" == 1 && assigned "drift" == 1 do
    throw <| IO.userError "F10-like scope drift was not uniquely associated"
  let some (residualName, _) := (names.getD (groupName "ambigEarly") #[])[0]? |
    throw <| IO.userError "residual of ambiguous owner did not match the third candidate"
  unless residualName == hygName m 200 6 do
    throw <| IO.userError "residual of ambiguous owner matched a claimed candidate"
  unless (cat.get! (groupName "owner")).declId.length != 64 do
    throw <| IO.userError "owner must have a deliberately invalid stored ID"
  for label in ["early", "ambiguous", "twoA", "twoB", "multi"] do
    unless assigned label == 0 do
      throw <| IO.userError s!"{label} incorrectly claimed an exported candidate"
  unless diags.size == 5 && diags.all (fun d => d.code == "export-missing") do
    throw <| IO.userError s!"expected five missing-member diagnostics, got {diags}"
  IO.println "PASS: full-key ambiguity rejects owner; unique residual and F10 drift match; other ambiguity rejects"
