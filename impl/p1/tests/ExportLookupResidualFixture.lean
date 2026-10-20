import Lean

open Lean Elab Command

-- Distinct command hashes separate the four cases. Repeated relocation tags
-- create two distinct exported names with one raw full hygiene key.
run_cmd do
  let m := `ExportLookupResidualFixture
  for (hash, scope, repeatTag) in
      [(100, 5, false), (200, 5, false), (200, 5, true), (200, 6, false),
       (300, 5, false), (400, 5, false), (400, 6, false),
       (500, 5, false), (500, 28, false)] do
    let privateBase := Name.mkNum (`_private ++ m) 0
    let tagBase := Name.mkStr privateBase "_pl_12345678"
    let base := Name.mkStr
      (if repeatTag then Name.mkStr tagBase "_pl_12345678" else tagBase) "initFn"
    let imported := Name.mkNum ((Name.mkStr base "_@") ++ m) hash
    let n := Name.mkNum (Name.mkStr (Name.mkStr imported "_hygCtx") "_hyg") scope
    liftCoreM <| addDecl <| .axiomDecl {
      name := n, levelParams := [], type := mkConst ``Nat, isUnsafe := false }
