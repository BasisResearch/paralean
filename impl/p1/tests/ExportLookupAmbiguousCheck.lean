import Paralean.Export

open Lean Paralean System

private def hygName (m : Name) (repeatedTag : Bool) : Name :=
  let privateBase := Name.mkNum (`_private ++ m) 0
  let tagBase := Name.mkStr privateBase "_pl_12345678"
  let base := Name.mkStr
    (if repeatedTag then Name.mkStr tagBase "_pl_12345678" else tagBase) "initFn"
  let imported := Name.mkNum ((Name.mkStr base "_@") ++ m) 777
  Name.mkNum (Name.mkStr (Name.mkStr imported "_hygCtx") "_hyg") 2

unsafe def main (args : List String) : IO Unit := do
  let [oleanPath] := args |
    throw (IO.userError "usage: ExportLookupAmbiguousCheck.lean EXPORTED_OLEAN")
  let m := `ExportLookupAmbiguous
  let n0 := hygName m false
  let n1 := hygName m true
  unless n0 != n1 && exportHygieneKey? m n0 == exportHygieneKey? m n1 do
    throw <| IO.userError "fixture names must have one identical raw hygiene key"
  let gid := "12345678synthetic-ambiguous-hygiene-group"
  let capsule : Capsule := {
    workspace := "fixture", file := "ExportLookupAmbiguous.lean", module := m,
    startLine := 1, endLine := 1, imports := #[`Lean], noncomputable_ := false,
    currNamespace := .anonymous, opens := #[], scopeCmds := #[], localEffects := #[],
    text := "", relocate := true }
  let member : MemberRec := {
    name := n0, local_ := Name.mkNum `initFn._hyg 0, cls := "scoped", kind := "axiom" }
  let group : GroupRec := {
    gid := gid, declId := "", kind := "decl", cmdKind := .anonymous, members := #[member],
    realized := #[], deps := #[], feDeps := #[], feDepsConservative := #[],
    publicNames := #[], anchor := none, touched := #[], axioms := #[],
    capsule := capsule, diags := #[], encSize := 0 }
  let metas : Std.HashMap String GroupRec := ({} : Std.HashMap String GroupRec).insert gid group
  let cat : Catalog := { metas := metas, order := #[gid] }
  let plan := planExport cat #[gid]
  let arts : NameMap ImportArtifacts := ({} : NameMap ImportArtifacts).insert m
    (.ofArrays #[#[FilePath.mk oleanPath]])
  let env ← importModules #[{ module := m }] {} (arts := arts) (level := .private)
  let some idx := env.getModuleIdx? m | throw <| IO.userError "module not imported"
  let namesInOLean := env.header.moduleData[idx.toNat]!.constNames
  unless namesInOLean.contains n0 && namesInOLean.contains n1 do
    throw <| IO.userError s!"fixture names absent from .olean: {namesInOLean}"
  let (_, names, diags) := exportIdentity cat plan env
  unless diags.any (fun d => d.code == "export-missing") do
    throw <| IO.userError s!"ambiguous hygiene key was not rejected: {diags}"
  unless (names.getD gid #[]).isEmpty do
    throw <| IO.userError "ambiguous hygiene key was assigned a candidate"
  IO.println "PASS: two exported declarations with one raw key are rejected"
