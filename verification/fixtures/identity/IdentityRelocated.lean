import Lean
open Lean Elab Command

partial def nameStrings : Expr → Array String
  | .lit (.strVal s) => #[s]
  | .app f a => nameStrings f ++ nameStrings a
  | .lam _ t b _ => nameStrings t ++ nameStrings b
  | .forallE _ t b _ => nameStrings t ++ nameStrings b
  | .letE _ t v b _ => nameStrings t ++ nameStrings v ++ nameStrings b
  | .mdata _ b => nameStrings b
  | .proj _ _ b => nameStrings b
  | _ => #[]

register_simp_attr identity_simps
run_cmd do
  let env ← getEnv
  for (n, c) in env.constants.toList do
    if (n.toString.splitOn "IdentityRelocated").length > 1 then
      if let some e := c.value? then
        let ss := (nameStrings e).filter (fun s => (s.splitOn "IdentityRelocated").length > 1)
        if !ss.isEmpty then
          logInfo m!"{n}: {ss.toList}"
