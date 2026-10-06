import Lean
import Paralean.Model
import Paralean.Sha256

/-!
Canonical instance names (docs/p0-interfaces.md §3.2, OPEN-24; LEAN-NAMES.md).

Scheme. An anonymous instance with final type `τ`, declared in namespace `ns`, is named

    ns ++ (inst<Heads> ++ "_" ++ h)

* `inst<Heads>` is Lean's own head-symbol base name (`NameGen.mkBaseNameWithSuffix "inst" τ`),
  with no project suffix and no `_n` deduplication. It keeps names readable and greppable.
* `h` is the first 8 hex digits of `H("v0/insttype", canonTypeText τ)` (§1.2: SHA-256 over `"paralean" NUL "v0/insttype" NUL` and the PCE string of the text), an injective
  serialization of `τ` that ignores binder names and `mdata`, numbers universe parameters by
  first occurrence, and spells constants by their module-independent identity (`normName`:
  no `_private.<Module>.0` prefix, no `_pl_*` relocation component).

The name depends only on `ns` and `τ`, never on the environment: no `_n`, no module-root
suffix. Two groups declaring `instance : Foo Nat` in one namespace get the same name and
collide; instances whose types differ get different names unless the 32-bit digests
collide (then the clash is reported like any other public-name collision; nothing is
renamed silently).

P1 stand-in for the fork. `install` puts a command elaborator for `declaration` ahead of
the stock one. For an `instance` without a name it elaborates the command once with the
stock elaborator to learn the final type (section variables, auto-bound implicits and
instance arguments included), restores the complete command state, and elaborates the
command again with the canonical name written in. Explicitly named instances, including
those deriving handlers generate, go to the stock elaborator unchanged (a stock export
cannot name a derived instance; see p1-fork-hooks.md item 14). Fork location:
`Lean/Elab/DeclNameGen.lean:262` `mkInstanceName` and `Lean/Elab/Deriving/Util.lean:95`
`mkInstName`.
-/

namespace Paralean.InstName
open Lean Elab Command Meta

/-- Canonical names chosen by the hook in this process, with the stock name the command
would have received (metadata for G2; capture drains it per command). -/
initialize chosen : IO.Ref (Array (Name × Name)) ← IO.mkRef #[]

def hexDigits : Nat := 8

/-- Domain tag of the digest (OPEN-24: `H("v0/insttype", type)`). -/
def domainTag : String := "v0/insttype"

/-- §1.1 `uvarint` (unsigned LEB128, minimal). -/
def uvarint (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut k := n
  while k ≥ 128 do
    out := out.push ((k % 128).toUInt8 ||| 0x80)
    k := k / 128
  return out.push k.toUInt8

/-- Preimage of `H("v0/insttype", text)` (p0-interfaces.md §1.2):
`"paralean" NUL "v0/insttype" NUL ‖ PCE(text)`, where the PCE of a string is `uvarint len ‖ UTF-8`. -/
def instTypePreimage (text : String) : ByteArray :=
  "paralean\x00".toUTF8 ++ domainTag.toUTF8 ++ "\x00".toUTF8 ++ uvarint text.utf8ByteSize ++ text.toUTF8

partial def levelText (lps : IO.Ref (Std.HashMap Name Nat)) : Level → IO String
  | .zero => pure "0"
  | .succ l => return s!"s({← levelText lps l})"
  | .max a b => return s!"m({← levelText lps a},{← levelText lps b})"
  | .imax a b => return s!"i({← levelText lps a},{← levelText lps b})"
  | .param n => do
    let m ← lps.get
    match m[n]? with
    | some k => return s!"u{k}"
    | none => lps.set (m.insert n m.size); return s!"u{m.size}"
  | .mvar _ => pure "?"

def binderTag : BinderInfo → String
  | .default => "d" | .implicit => "i" | .strictImplicit => "s" | .instImplicit => "c"

/-- Injective text of a closed type: every constructor has a distinct tag and every
variable-length field is delimited, so distinct (alpha-, mdata- and level-renaming-
normalized) expressions give distinct strings. -/
partial def canonTypeText (mainModule : Name) (e : Expr) : IO String := do
  let lps ← IO.mkRef ({} : Std.HashMap Name Nat)
  let rec go (e : Expr) : IO String := do
    match e with
    | .bvar i => return s!"b{i}"
    | .fvar f => return s!"f({f.name})"
    | .mvar _ => return "?"
    | .sort l => return s!"S({← levelText lps l})"
    | .const n ls => do
      let ls ← ls.mapM (levelText lps)
      return s!"C({(toString (normName mainModule n)).quote},[{",".intercalate ls}])"
    | .app f a => return s!"A({← go f},{← go a})"
    | .lam _ t b bi => return s!"L{binderTag bi}({← go t},{← go b})"
    | .forallE _ t b bi => return s!"P{binderTag bi}({← go t},{← go b})"
    | .letE _ t v b nd => return s!"Z{if nd then 1 else 0}({← go t},{← go v},{← go b})"
    | .lit (.natVal n) => return s!"N{n}"
    | .lit (.strVal s) => return s!"T{s.quote}"
    | .mdata _ e => go e
    | .proj s i e => return s!"J({(toString (normName mainModule s)).quote},{i},{← go e})"
  go e

/-- Canonical name (one component, to be placed in the current namespace). -/
def canonicalName (ty : Expr) : MetaM Name := do
  let main ← getMainModule
  let base ← NameGen.mkBaseNameWithSuffix "inst" ty
  let mut s := base.eraseMacroScopes.toString (escape := false)
  -- the project suffix depends on where the referenced constants live, i.e. on the
  -- environment; the digest already distinguishes the types
  let suf := projectSuffix main
  if suf != "" && s.endsWith suf && s != "inst" ++ suf then
    s := (s.dropEnd suf.length).toString
  let text ← canonTypeText main (← instantiateMVars ty)
  let h := ((Sha256.hashHex (instTypePreimage text)).take hexDigits).toString
  return Name.mkSimple s!"{s}_{h}"

/-- `instance` node of a `declaration` command, if it has no name and was written in the
source. Instances that deriving handlers synthesize (e.g. `DecidableEq` for an enum)
keep the handler's spelling: a stock export re-runs the handler and cannot be told a
name, so capture must see the same name the export will produce. -/
def anonymousInstance? (stx : Syntax) : Option Syntax :=
  if stx.getKind == ``Lean.Parser.Command.declaration &&
      stx[1].getKind == ``Lean.Parser.Command.instance && stx[1][3].isNone &&
      (stx[1][1].getHeadInfo matches .original ..) then
    some stx[1]
  else none

def canonicalInstanceElab : CommandElab := fun stx => do
  let some inst := anonymousInstance? stx | throwUnsupportedSyntax
  if (← IO.getEnv "PARALEAN_STOCK_INSTANCE_NAMES").isSome then throwUnsupportedSyntax
  let s0 ← get
  -- the name the stock elaborator will give it (`mkInstanceName` restores the state)
  let stockId ← mkInstanceName inst[4][0].getArgs inst[4][1][1]
  if stockId.hasMacroScopes then throwUnsupportedSyntax
  let ns ← getCurrNamespace
  let nErr := s0.messages.toList.filter (·.severity == .error) |>.length
  -- pass 1: stock elaboration, only to read the final type
  let ty? ← try
      elabDeclaration stx
      let errs := (← get).messages.toList.filter (·.severity == .error) |>.length
      let env ← getEnv
      pure (if errs > nErr then none else env.find? (ns ++ stockId) |>.map (·.type))
    catch _ => pure none
  let some ty := ty? | set s0; throwUnsupportedSyntax
  let canon ← runTermElabM fun _ => canonicalName ty
  set s0
  -- canonical names are never deduplicated: an existing declaration is a collision
  if (← getEnv).contains (ns ++ canon) then
    throwErrorAt inst[1] "instance name collision: {ns ++ canon} is already declared \
      (a duplicate instance of the same type; canonical instance names never take a `_n` suffix)"
  let declId := mkNode ``Lean.Parser.Command.declId #[mkIdentFrom inst[1] canon, mkNullNode]
  let stx' := stx.setArg 1 (inst.setArg 3 (mkNullNode #[declId]))
  elabDeclaration stx'
  chosen.modify (·.push (ns ++ canon, ns ++ stockId))

def install : IO Unit :=
  commandElabAttribute.addBuiltin ``Lean.Parser.Command.declaration
    `Paralean.InstName.canonicalInstanceElab canonicalInstanceElab

end Paralean.InstName
