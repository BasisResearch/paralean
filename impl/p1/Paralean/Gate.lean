module

public import Lean
public import Paralean.Safety

@[expose] public section

/-!
The command gate for published capsules (W2 A-28).

A capsule another worker published is Lean source. Elaborating it runs whatever its
commands run: `#eval`, `run_cmd`, `initialize`, `elab` and `macro` bodies, `by_elab` and
`run_tac` blocks, user-registered simprocs or attribute handlers, and native code through
`native_decide` or kernel `Lean.reduceBool`. The validator replays capsules (inside its
sandbox) and every consumer re-elaborates the capsules of the packages it loads with
`remote%` (inside the user's own Lean process), so a receipt alone cannot make such text safe.

`checkCommand` therefore inspects each command's *parsed syntax*, before it is elaborated,
with the same parser state that will elaborate it:

* the command kind must be in `allowedCommands` (declarations, scope commands, `open`,
  `variable`, `universe`, `include`/`omit`, `export`, `attribute`, `set_option`, `deriving
  instance`, `notation` and mixfix, doc comments, and `in`/`mutual` combinations of them);
* no node anywhere may be one of `deniedKinds` (code-running term, tactic and command
  forms, `unsafe`), and `decide` may not be configured with `native`;
* every `set_option` (command, term or tactic form) must name an option of `safeOption`,
  identified from the parsed identifier, so `«debug».skipKernelTC` is `debug.skipKernelTC`;
* every attribute must be in `safeAttrs` or a registered simp set;
* no identifier may name the kernel's native-evaluation hooks (`Lean.reduceBool`, ...);
* `remote_value%` may only name the package being loaded, and `remote%`/`remote_decl%`
  never appear.

The gate is not a sandbox. Tactics, deriving handlers, notation expansion and attribute
handlers that come from *imported* packages still run during elaboration (the W2-13 class
of trust in the pinned base). See docs/w2-security.md.
-/

namespace Paralean.Gate
open Lean

/-- Command kinds a published capsule may contain (after `renderCapsule`). -/
def allowedCommands : List Name := [
  ``Lean.Parser.Command.declaration, ``Lean.Parser.Command.section,
  ``Lean.Parser.Command.namespace, ``Lean.Parser.Command.end, ``Lean.Parser.Command.open,
  ``Lean.Parser.Command.variable, ``Lean.Parser.Command.universe,
  ``Lean.Parser.Command.include, ``Lean.Parser.Command.omit, ``Lean.Parser.Command.export,
  ``Lean.Parser.Command.set_option, ``Lean.Parser.Command.attribute,
  ``Lean.Parser.Command.deriving, ``Lean.Parser.Command.mixfix, ``Lean.Parser.Command.notation,
  ``Lean.Parser.Command.moduleDoc, ``Lean.Parser.Command.addDocString,
  ``Lean.Parser.Command.in, ``Lean.Parser.Command.mutual, ``Lean.Parser.Command.eoi,
  -- Mathlib's `lemma` is `theorem` under another keyword (expanded by an imported macro)
  `Mathlib.Tactic.lemma]

/-- Last components of syntax kinds that run user code at elaboration time, or `unsafe`. -/
def deniedKinds : List String := [
  "eval", "evalBang", "runCmd", "runElab", "runMeta", "byElab", "runTac", "nativeDecide",
  "unsafe", "initialize", "elab", "elab_rules", "macro", "macro_rules", "syntax"]

/-- Kernel hooks that evaluate compiled code during type checking. -/
def nativeHooks : List String := ["reduceBool", "reduceNat", "ofReduceBool", "ofReduceNat"]

def kindTail (k : SyntaxNodeKind) : String :=
  match k with
  | .str _ s => s
  | _ => ""

/-- Options a capsule may set: limits, implicit-argument and pretty-printing switches,
linters and traces. Nothing that weakens checking (`debug.*`) or changes code generation. -/
def safeOption (n : Name) : Bool :=
  [`maxHeartbeats, `maxRecDepth, `synthInstance.maxHeartbeats, `synthInstance.maxSize,
   `autoImplicit, `relaxedAutoImplicit, `Elab.async].contains n ||
  [`pp, `linter, `trace].any (·.isPrefixOf n)

/-- Attributes a capsule may use: data for the elaborator (simp sets, instances, reducibility,
extensionality and Mathlib's declaration generators), never a handler that registers code. -/
def safeAttrs : List Name := [
  `simp, `reducible, `irreducible, `semireducible, `instance, `default_instance, `inline,
  `noinline, `macro_inline, `always_inline, `specialize, `nospecialize, `class, `ext, `simps,
  `to_additive, `expose, `deprecated, `instance_reducible, `inherit_doc, `refl, `symm, `trans,
  `congr, `gcongr, `mono, `norm_cast, `push_cast, `elab_as_elim, `induction_eliminator,
  `cases_eliminator, `match_pattern, `pp_nodot, `pp_using_anonymous_constructor, `coe, `grind,
  `nolint]

/-- The name an attribute instance denotes (as `Lean.Elab.elabAttr` derives it, without
macro expansion). -/
def attrName (inst : Syntax) : Name :=
  let attr := inst[1]
  if attr.getKind == ``Lean.Parser.Attr.simple then attr[0].getId.eraseMacroScopes
  else Name.mkSimple (kindTail attr.getKind)

/-- First problem found below `stx`, or `none`. `self` is the package whose capsule this is. -/
partial def scan (self : String) (stx : Syntax) : IO (Option String) := do
  match stx with
  | .ident _ _ n _ =>
    let n := n.eraseMacroScopes
    if let .str _ s := n then
      if nativeHooks.contains s then return some s!"names the kernel native-evaluation hook {n}"
    return none
  | .node _ k args =>
    let tail := kindTail k
    if deniedKinds.contains tail then return some s!"contains {k}, which runs code or is unsafe"
    if tail == "set_option" then
      let o := stx[1].getId.eraseMacroScopes
      unless safeOption o do return some s!"sets option {o}, which a published capsule may not set"
      if [`maxHeartbeats, `synthInstance.maxHeartbeats].contains o && stx.getArgs.findSome? (·.isNatLit?) == some 0 then
        return some s!"sets {o} to 0 (unlimited)"
    if k == ``Lean.Parser.Term.attrInstance then
      let a := attrName stx
      let simpSet := (← Meta.simpExtensionMapRef.get).contains a
      unless safeAttrs.contains a || simpSet do
        return some s!"uses attribute [{a}], which a published capsule may not use"
    if k == ``Lean.Parser.Tactic.decide then
      if (idents stx).contains `native then return some "configures `decide` with native evaluation"
    if k == `Paralean.Remote.remoteTerm || k == `Paralean.Remote.remoteCmd then
      return some "contains remote%; a capsule never loads another package by itself"
    if k == `Paralean.Remote.remoteValue then
      unless stx[1].isStrLit? == some self do
        return some "contains remote_value% for another package"
    for a in args do
      if let some e ← scan self a then return some e
    return none
  | _ => return none
where
  idents : Syntax → Array Name
    | .ident _ _ n _ => #[n.eraseMacroScopes]
    | .node _ _ args => args.foldl (fun acc a => acc ++ idents a) #[]
    | _ => #[]

/-- Check one parsed top-level command of a published capsule. -/
partial def checkCommand (self : String) (stx : Syntax) : IO (Except String Unit) := do
  let k := stx.getKind
  if k == ``Lean.Parser.Command.in then
    if let .error e ← checkCommand self stx[0] then return .error e
    return ← checkCommand self stx[2]
  if k == ``Lean.Parser.Command.mutual then
    for c in stx[1].getArgs do
      unless c.getKind == ``Lean.Parser.Command.declaration do
        return .error s!"mutual block contains {c.getKind}"
  else unless allowedCommands.contains k do
    return .error s!"command {k} is not admitted in a published capsule"
  match ← scan self stx with
  | some e => return .error e
  | none => return .ok ()

end Paralean.Gate
