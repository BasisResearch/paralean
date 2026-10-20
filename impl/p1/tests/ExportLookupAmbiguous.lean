import Lean

open Lean Elab Command

-- Two distinct declarations have the same raw hygiene key after stripping
-- repeated relocation tags. This is a deliberately malformed association fixture: export
-- lookup must reject it instead of choosing the first .olean entry.
run_cmd do
  let m := `ExportLookupAmbiguous
  for repeatedTag in [false, true] do
    let privateBase := Name.mkNum (`_private ++ m) 0
    let tagBase := Name.mkStr privateBase "_pl_12345678"
    let base := Name.mkStr
      (if repeatedTag then Name.mkStr tagBase "_pl_12345678" else tagBase) "initFn"
    let imported := Name.mkNum ((Name.mkStr base "_@") ++ m) 777
    let n := Name.mkNum (Name.mkStr (Name.mkStr imported "_hygCtx") "_hyg") 2
    liftCoreM <| addDecl <| .axiomDecl {
      name := n, levelParams := [], type := mkConst ``Nat, isUnsafe := false }
