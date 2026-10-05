module

public import Lean
public import Paralean.Sha256

@[expose] public section

/-!
Canonical, length-delimited encoding of a declaration group.

Constant references are `Ref`s, never raw Lean names, so a group's bytes do not depend on
the module it was elaborated in. In memory a `Ref` names members by their normalized local
identity; on the wire (`WireCtx`) members are numbered (p0-interfaces.md §3.4, OPEN-22):

* `base n`     — a constant of the pinned base environment (the file header imports);
* `self i`     — member `i` of this group in canonical order (`canonicalOrder`);
* `dep id i`   — member `i` of another group, pinned by its **group ID** (the declaration
                 ID of its kernel content; OPEN-23). The package ID that names its capsule
                 is in the group's `deps` metadata, not in the bytes;
* `res r s`    — a reserved name `s` realized from the constant `r` (never transported).

Public members carry their name in the bytes (public names are identity and collision
keys). Scoped members carry none: their spelling (`_private…`, `_proof_n`, `match_n`, …)
is unhashed metadata, so identity is invariant to relocation and to auxiliary renaming
such as `_proof_1` vs `_proof_1_1`. Binder names (macro scopes erased), level parameters
and `mdata` keys are encoded verbatim.
Expressions, levels and names are hash-consed into tables, so DAG sharing is preserved
and the encoding of a term is linear in its number of distinct subterms.
-/

namespace Paralean
open Lean

inductive Ref where
  | base (n : Name)
  | self (l : Name)
  | dep (gid : String) (l : Name)
  | res (r : Ref) (suffix : Name)
  deriving BEq, Hashable, Repr, Inhabited

partial def Ref.toString : Ref → String
  | .base n => s!"base:{n}"
  | .self l => s!"self:{l}"
  | .dep g l => s!"dep:{(g.take 12).toString}:{l}"
  | .res r s => s!"res({r.toString}).{s}"

instance : ToString Ref := ⟨Ref.toString⟩

/-- Name classes from `verification/veil/LEAN-NAMES.md`. -/
inductive NameClass where
  /-- Public name declared by the command; enters collision checks. -/
  | pub
  /-- Eager auxiliary of a public name (`casesOn`, `match_1`, `_proof_1`, ...);
      collides exactly when its base collides. -/
  | pubAux
  /-- Private or generated name; identity is keyed by the group. -/
  | scoped
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

def NameClass.tag : NameClass → UInt8
  | .pub => 0 | .pubAux => 1 | .scoped => 2

def NameClass.ofTag : UInt8 → Option NameClass
  | 0 => some .pub | 1 => some .pubAux | 2 => some .scoped | _ => none

instance : ToString NameClass := ⟨fun | .pub => "pub" | .pubAux => "pubAux" | .scoped => "scoped"⟩

/-- Wire form of the references (OPEN-22/23): members by index, other groups by group ID. -/
structure WireCtx where
  /-- Index of a member of this group, by local identity. -/
  selfIdx : Name → Option Nat
  /-- (package ID, local identity) of a dependency ↦ (its group ID, member index). -/
  dep : String → Name → Option (String × Nat)

/-- Index used for every self-reference when sorting unreferenced scoped members (`self(⊥)`). -/
def selfBot : Nat := 0xFFFFFFFF

/-- A member of a group, as encoded: its identity within the group and its kernel value. -/
structure EncMember where
  local_ : Name
  cls : NameClass
  info : ConstantInfo
  deriving Inhabited

/-! ## Byte writer -/

structure W where
  out : ByteArray := ByteArray.emptyWithCapacity 1024

namespace W
@[inline] def byte (w : W) (b : UInt8) : W := { out := w.out.push b }
partial def nat (w : W) (n : Nat) : W :=
  if n < 128 then w.byte n.toUInt8 else (w.byte ((n % 128).toUInt8 ||| 0x80)).nat (n / 128)
def bytes (w : W) (b : ByteArray) : W := { out := (w.nat b.size).out ++ b }
def str (w : W) (s : String) : W := w.bytes s.toUTF8
def bool (w : W) (b : Bool) : W := w.byte (if b then 1 else 0)
end W

/-- `Expr` keyed by full structural equality (binder names included), not alpha-equivalence. -/
structure ExprKey where
  e : Expr

instance : BEq ExprKey := ⟨fun a b => a.e.equal b.e⟩
instance : Hashable ExprKey := ⟨fun a => a.e.hash⟩

structure EncState where
  names : Std.HashMap Name Nat := {}
  nameW : W := {}
  refs : Std.HashMap Ref Nat := {}
  refW : W := {}
  levels : Std.HashMap Level Nat := {}
  levelW : W := {}
  exprs : Std.HashMap ExprKey Nat := {}
  exprW : W := {}
  body : W := {}

abbrev EncM := ReaderT ((Name → Except String Ref) × WireCtx) (StateT EncState (Except String))

namespace Enc

partial def name (n : Name) : EncM Nat := do
  if let some i := (← get).names[n]? then return i
  let w ← match n with
    | .anonymous => pure ((← get).nameW.byte 0)
    | .str p s => do let i ← name p; pure (((← get).nameW.byte 1).nat i |>.str s)
    | .num p k => do let i ← name p; pure (((← get).nameW.byte 2).nat i |>.nat k)
  modifyGet fun s => let i := s.names.size; (i, { s with names := s.names.insert n i, nameW := w })

partial def ref (r : Ref) : EncM Nat := do
  if let some i := (← get).refs[r]? then return i
  let ctx := (← read).2
  let w ← match r with
    | .base n => do let i ← name n; pure (((← get).refW.byte 0).nat i)
    | .self l => do
      let some k := ctx.selfIdx l | throw s!"encode: {l} is not a member of this group"
      pure (((← get).refW.byte 1).nat k)
    | .dep g l => do
      let some (id, k) := ctx.dep g l | throw s!"encode: no member {l} in dependency {(g.take 12).toString}"
      pure (((← get).refW.byte 2).str id |>.nat k)
    | .res b sfx => do
      let i ← ref b; let j ← name sfx; pure (((← get).refW.byte 3).nat i |>.nat j)
  modifyGet fun s => let i := s.refs.size; (i, { s with refs := s.refs.insert r i, refW := w })

/-- Binder names are irrelevant to the kernel; hygienic ones embed the module name and a
per-module counter, so they are encoded with their macro scopes erased. -/
def binderName (n : Name) : EncM Nat :=
  name (if n.hasMacroScopes then n.eraseMacroScopes else n)

def constRef (n : Name) : EncM Nat := do
  match (← read).1 n with
  | .ok r => ref r
  | .error e => throw e

partial def level (l : Level) : EncM Nat := do
  if let some i := (← get).levels[l]? then return i
  let w ← match l with
    | .zero => pure ((← get).levelW.byte 0)
    | .succ a => do let i ← level a; pure (((← get).levelW.byte 1).nat i)
    | .max a b => do
      let i ← level a; let j ← level b; pure (((← get).levelW.byte 2).nat i |>.nat j)
    | .imax a b => do
      let i ← level a; let j ← level b; pure (((← get).levelW.byte 3).nat i |>.nat j)
    | .param n => do let i ← name n; pure (((← get).levelW.byte 4).nat i)
    | .mvar _ => throw "level metavariable in a completed declaration"
  modifyGet fun s => let i := s.levels.size; (i, { s with levels := s.levels.insert l i, levelW := w })

def binderInfo : BinderInfo → UInt8
  | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3

def dataValue (w : W) : DataValue → EncM W
  | .ofString s => pure ((w.byte 0).str s)
  | .ofBool b => pure ((w.byte 1).bool b)
  | .ofName n => do let i ← name n; pure ((w.byte 2).nat i)
  | .ofNat n => pure ((w.byte 3).str (toString n))
  | .ofInt i => pure ((w.byte 4).str (toString i))
  | .ofSyntax stx => pure ((w.byte 5).str (toString stx))

partial def expr (e : Expr) : EncM Nat := do
  if let some i := (← get).exprs[ExprKey.mk e]? then return i
  let w ← match e with
    | .bvar k => pure (((← get).exprW.byte 0).nat k)
    | .fvar _ => throw "free variable in a completed declaration"
    | .mvar _ => throw "metavariable in a completed declaration"
    | .sort u => do let i ← level u; pure (((← get).exprW.byte 1).nat i)
    | .const n us => do
      let r ← constRef n
      let ls ← us.mapM level
      let mut w := ((← get).exprW.byte 2).nat r |>.nat ls.length
      for l in ls do w := w.nat l
      pure w
    | .app f a => do
      let i ← expr f; let j ← expr a; pure (((← get).exprW.byte 3).nat i |>.nat j)
    | .lam n t b bi => do
      let k ← binderName n; let i ← expr t; let j ← expr b
      pure (((← get).exprW.byte 4).nat k |>.nat i |>.nat j |>.byte (binderInfo bi))
    | .forallE n t b bi => do
      let k ← binderName n; let i ← expr t; let j ← expr b
      pure (((← get).exprW.byte 5).nat k |>.nat i |>.nat j |>.byte (binderInfo bi))
    | .letE n t v b nd => do
      let k ← binderName n; let i ← expr t; let j ← expr v; let l ← expr b
      pure (((← get).exprW.byte 6).nat k |>.nat i |>.nat j |>.nat l |>.bool nd)
    | .lit (.natVal v) => pure (((← get).exprW.byte 7).str (toString v))
    | .lit (.strVal v) => pure (((← get).exprW.byte 8).str v)
    | .mdata d b => do
      let i ← expr b
      let mut w := ((← get).exprW.byte 9).nat i |>.nat d.entries.length
      for (k, v) in d.entries do
        let ki ← name k
        w ← dataValue (w.nat ki) v
      pure w
    | .proj s idx b => do
      let r ← constRef s; let i ← expr b
      pure (((← get).exprW.byte 10).nat r |>.nat idx |>.nat i)
  modifyGet fun s => let i := s.exprs.size; (i, { s with exprs := s.exprs.insert ⟨e⟩ i, exprW := w })

def body (f : W → EncM W) : EncM Unit := do
  let w ← f (← get).body
  modify fun s => { s with body := w }

def names (w : W) (ns : List Name) : EncM W := do
  let mut w := w.nat ns.length
  for n in ns do w := w.nat (← name n)
  return w

def refsOf (w : W) (ns : List Name) : EncM W := do
  let mut w := w.nat ns.length
  for n in ns do w := w.nat (← constRef n)
  return w

def safety : DefinitionSafety → UInt8
  | .unsafe => 0 | .safe => 1 | .partial => 2

def hints (w : W) : ReducibilityHints → W
  | .opaque => w.byte 0
  | .abbrev => w.byte 1
  | .regular h => (w.byte 2).nat h.toNat

def constantInfo (m : EncMember) : EncM Unit := do
  let ci := m.info
  -- public spellings are identity; scoped spellings are metadata only
  let ln? ← if m.cls == .scoped then pure none else some <$> name m.local_
  let lps ← ci.levelParams.mapM name
  let ty ← expr ci.type
  body fun w => do
    let w := w.byte m.cls.tag
    let w := match ln? with | some ln => w.nat ln | none => w
    let w := w.nat lps.length
    let w := lps.foldl W.nat w
    let w := w.nat ty
    match ci with
    | .axiomInfo v => pure ((w.byte 0).bool v.isUnsafe)
    | .defnInfo v => do
      let val ← expr v.value
      let w := (hints ((w.byte 1).nat val) v.hints).byte (safety v.safety)
      refsOf w v.all
    | .thmInfo v => do
      let val ← expr v.value
      refsOf ((w.byte 2).nat val) v.all
    | .opaqueInfo v => do
      let val ← expr v.value
      refsOf (((w.byte 3).nat val).bool v.isUnsafe) v.all
    | .quotInfo v =>
      pure ((w.byte 4).byte (match v.kind with
        | .type => 0 | .ctor => 1 | .lift => 2 | .ind => 3))
    | .inductInfo v => do
      let w := ((w.byte 5).nat v.numParams).nat v.numIndices
      let w ← refsOf w v.all
      let w ← refsOf w v.ctors
      pure (((w.nat v.numNested).bool v.isRec |>.bool v.isUnsafe).bool v.isReflexive)
    | .ctorInfo v => do
      let i ← constRef v.induct
      pure ((w.byte 6).nat i |>.nat v.cidx |>.nat v.numParams |>.nat v.numFields |>.bool v.isUnsafe)
    | .recInfo v => do
      let w ← refsOf (w.byte 7) v.all
      let mut w := w.nat v.numParams |>.nat v.numIndices |>.nat v.numMotives |>.nat v.numMinors
        |>.nat v.rules.length
      for r in v.rules do
        let c ← constRef r.ctor
        let rhs ← expr r.rhs
        w := w.nat c |>.nat r.nfields |>.nat rhs
      pure ((w.bool v.k).bool v.isUnsafe)

end Enc

/-- Hygienic universe parameter names embed the module and a counter. Rename them
injectively by position (`u._@...` ↦ `u._hyg_<i>`); this is an alpha-renaming. -/
def canonLevelParams (ci : ConstantInfo) : ConstantInfo :=
  if !ci.levelParams.any (·.hasMacroScopes) then ci else
  let ps := ci.levelParams
  let ps' := ps.zipIdx.map fun (p, i) =>
    if p.hasMacroScopes then Name.mkStr p.eraseMacroScopes s!"_hyg_{i}" else p
  let ls := ps'.map Level.param
  let inst (e : Expr) := e.instantiateLevelParams ps ls
  match ci with
  | .axiomInfo v => .axiomInfo { v with levelParams := ps', type := inst v.type }
  | .defnInfo v => .defnInfo { v with levelParams := ps', type := inst v.type, value := inst v.value }
  | .thmInfo v => .thmInfo { v with levelParams := ps', type := inst v.type, value := inst v.value }
  | .opaqueInfo v => .opaqueInfo { v with levelParams := ps', type := inst v.type, value := inst v.value }
  | .quotInfo v => .quotInfo { v with levelParams := ps', type := inst v.type }
  | .inductInfo v => .inductInfo { v with levelParams := ps', type := inst v.type }
  | .ctorInfo v => .ctorInfo { v with levelParams := ps', type := inst v.type }
  | .recInfo v =>
    let rules := v.rules.map fun r => { r with rhs := inst r.rhs }
    .recInfo { v with levelParams := ps', type := inst v.type, rules }

/-- Encoding domain tag and format version. -/
def groupMagic : String := "paralean-group-v2"

/-- Wire context numbering `members` by position, with dependencies given by `dep`. -/
def WireCtx.ofMembers (members : Array EncMember) (dep : String → Name → Option (String × Nat)) : WireCtx :=
  let idx : Std.HashMap Name Nat := members.size.fold (init := {}) fun i _ m => m.insert members[i].local_ i
  { selfIdx := (idx[·]?), dep }

/-- Encode members (already in canonical order) under the given base identity. -/
def encodeGroup (baseId : String) (members : Array EncMember)
    (resolve : Name → Except String Ref) (wire : WireCtx) : Except String ByteArray := do
  let act : EncM Unit := do
    Enc.body fun w => pure (w.nat members.size)
    for m in members do Enc.constantInfo m
  let ((), s) ← (act.run (resolve, wire)).run {}
  let w : W := {}
  let w := (w.str groupMagic).str baseId
  let w := (w.nat s.names.size).bytes s.nameW.out
  let w := (w.nat s.refs.size).bytes s.refW.out
  let w := (w.nat s.levels.size).bytes s.levelW.out
  let w := (w.nat s.exprs.size).bytes s.exprW.out
  let w := w.bytes s.body.out
  return w.out

/-- Lexicographic order on byte arrays. -/
def bytesLt (a b : ByteArray) : Bool := Id.run do
  for i in [0:min a.size b.size] do
    if a[i]! != b[i]! then return a[i]! < b[i]!
  return a.size < b.size

/-- Constants in `e`, in order of first occurrence in a depth-first, left-to-right walk. -/
partial def constOrder (e : Expr) (seen : Std.HashSet ExprKey) (acc : Array Name) :
    Std.HashSet ExprKey × Array Name :=
  if seen.contains ⟨e⟩ then (seen, acc) else
  let seen := seen.insert ⟨e⟩
  match e with
  | .const n _ => (seen, if acc.contains n then acc else acc.push n)
  | .app f a => let (s, acc) := constOrder f seen acc; constOrder a s acc
  | .lam _ t b _ | .forallE _ t b _ => let (s, acc) := constOrder t seen acc; constOrder b s acc
  | .letE _ t v b _ =>
    let (s, acc) := constOrder t seen acc; let (s, acc) := constOrder v s acc; constOrder b s acc
  | .mdata _ b => constOrder b seen acc
  | .proj s _ b => constOrder b seen (if acc.contains s then acc else acc.push s)
  | _ => (seen, acc)

/--
Canonical member numbering (p0-interfaces.md §3.4): public members first, sorted by name;
then scoped members in order of first reference in a depth-first, left-to-right walk of
the public members' (type, value) terms; then the remaining scoped members sorted by their
encoded bytes with every self-reference written as `self(⊥)` (ties, which only identical
encodings can produce, by spelling).
-/
def canonicalOrder (baseId : String) (members : Array EncMember)
    (resolve : Name → Except String Ref) (dep : String → Name → Option (String × Nat)) :
    Except String (Array EncMember) := do
  let pubs := (members.filter (·.cls != .scoped)).qsort fun a b => a.local_.toString < b.local_.toString
  let scopedMs := members.filter (·.cls == .scoped)
  let byLocal : Std.HashMap Name EncMember := scopedMs.foldl (fun m x => m.insert x.local_ x) {}
  let mut out := pubs
  let mut taken : Std.HashSet Name := {}
  let mut seen : Std.HashSet ExprKey := {}
  for p in pubs do
    let mut cs := #[]
    (seen, cs) := constOrder p.info.type seen cs
    if let some v := p.info.value? then (seen, cs) := constOrder v seen cs
    for c in cs do
      if let .ok (.self l) := resolve c then
        if let some m := byLocal[l]? then
          unless taken.contains l do
            taken := taken.insert l
            out := out.push m
  let bot : WireCtx := { selfIdx := fun _ => some selfBot, dep }
  let mut rest : Array (ByteArray × EncMember) := #[]
  for m in scopedMs do
    unless taken.contains m.local_ do
      rest := rest.push ((← encodeGroup baseId #[m] resolve bot), m)
  let sorted := rest.qsort fun a b =>
    bytesLt a.1 b.1 || (a.1 == b.1 && a.2.local_.toString < b.2.local_.toString)
  return out ++ sorted.map (·.2)

/-! ## Decoder -/

structure R where
  buf : ByteArray
  pos : Nat := 0

abbrev DecM := StateT R (Except String)

namespace Dec

def byte : DecM UInt8 := do
  let r ← get
  if h : r.pos < r.buf.size then
    set { r with pos := r.pos + 1 }; return r.buf[r.pos]
  else throw "decode: unexpected end of input"

partial def nat : DecM Nat := do
  let b ← byte
  if b < 128 then return b.toNat
  else return (b &&& 0x7f).toNat + 128 * (← nat)

def bytes : DecM ByteArray := do
  let n ← nat
  let r ← get
  if r.pos + n > r.buf.size then throw "decode: truncated bytes"
  set { r with pos := r.pos + n }
  return r.buf.extract r.pos (r.pos + n)

def str : DecM String := do
  match String.fromUTF8? (← bytes) with
  | some s => return s
  | none => throw "decode: invalid UTF-8"

def bool : DecM Bool := return (← byte) != 0

def sub (b : ByteArray) (x : DecM α) : Except String α := do
  let (a, r) ← x.run { buf := b }
  if r.pos != b.size then throw "decode: trailing bytes"
  return a

def idx (arr : Array α) [Inhabited α] (what : String) : DecM α := do
  let i ← nat
  if h : i < arr.size then return arr[i] else throw s!"decode: bad {what} index {i}"

end Dec

structure DecodedGroup where
  baseId : String
  refs : Array Ref
  members : Array (Name × NameClass × ConstantInfo)

/-- Inverse of `WireCtx` for one stored group: member index ↦ local identity, and
(group ID, index) of a dependency ↦ (its package ID, local identity). -/
structure UnwireCtx where
  selfLocal : Nat → Option Name
  dep : String → Nat → Option (String × Name)

/-- Decode a group, mapping each `Ref` to a Lean name in the target environment. -/
def decodeGroup (buf : ByteArray) (unwire : UnwireCtx) (nameOf : Ref → Except String Name) :
    Except String DecodedGroup := Dec.sub buf do
  let magic ← Dec.str
  unless magic == groupMagic do throw s!"decode: bad magic {magic}"
  let baseId ← Dec.str
  -- names
  let nn ← Dec.nat
  let nameBytes ← Dec.bytes
  let names ← liftM <| Dec.sub nameBytes do
    let mut arr : Array Name := Array.mkEmpty nn
    for _ in [0:nn] do
      let t ← Dec.byte
      let n ← match t with
        | 0 => pure Name.anonymous
        | 1 => do let p ← Dec.idx arr "name"; let s ← Dec.str; pure (Name.str p s)
        | 2 => do let p ← Dec.idx arr "name"; let k ← Dec.nat; pure (Name.num p k)
        | _ => throw "decode: bad name tag"
      arr := arr.push n
    return arr
  -- refs
  let nr ← Dec.nat
  let refBytes ← Dec.bytes
  let refs ← liftM <| Dec.sub refBytes do
    let mut arr : Array Ref := Array.mkEmpty nr
    for _ in [0:nr] do
      let t ← Dec.byte
      let r ← match t with
        | 0 => do pure (Ref.base (← Dec.idx names "name"))
        | 1 => do
          let k ← Dec.nat
          let some l := unwire.selfLocal k | throw s!"decode: no member {k}"
          pure (Ref.self l)
        | 2 => do
          let g ← Dec.str
          let k ← Dec.nat
          let some (pid, l) := unwire.dep g k | throw s!"decode: no dependency member {(g.take 12).toString}/{k}"
          pure (Ref.dep pid l)
        | 3 => do let b ← Dec.idx arr "ref"; pure (Ref.res b (← Dec.idx names "name"))
        | _ => throw "decode: bad ref tag"
      arr := arr.push r
    return arr
  let refNames ← liftM (refs.mapM nameOf)
  -- levels
  let nl ← Dec.nat
  let levelBytes ← Dec.bytes
  let levels ← liftM <| Dec.sub levelBytes do
    let mut arr : Array Level := Array.mkEmpty nl
    for _ in [0:nl] do
      let t ← Dec.byte
      let l ← match t with
        | 0 => pure Level.zero
        | 1 => do pure (Level.succ (← Dec.idx arr "level"))
        | 2 => do let a ← Dec.idx arr "level"; pure (Level.max a (← Dec.idx arr "level"))
        | 3 => do let a ← Dec.idx arr "level"; pure (Level.imax a (← Dec.idx arr "level"))
        | 4 => do pure (Level.param (← Dec.idx names "name"))
        | _ => throw "decode: bad level tag"
      arr := arr.push l
    return arr
  -- exprs
  let ne ← Dec.nat
  let exprBytes ← Dec.bytes
  let exprs ← liftM <| Dec.sub exprBytes do
    let mut arr : Array Expr := Array.mkEmpty ne
    let bi (b : UInt8) : BinderInfo := match b with
      | 1 => .implicit | 2 => .strictImplicit | 3 => .instImplicit | _ => .default
    for _ in [0:ne] do
      let t ← Dec.byte
      let e ← match t with
        | 0 => do pure (Expr.bvar (← Dec.nat))
        | 1 => do pure (Expr.sort (← Dec.idx levels "level"))
        | 2 => do
          let n ← Dec.idx refNames "ref"
          let k ← Dec.nat
          let mut us := #[]
          for _ in [0:k] do us := us.push (← Dec.idx levels "level")
          pure (Expr.const n us.toList)
        | 3 => do let f ← Dec.idx arr "expr"; pure (Expr.app f (← Dec.idx arr "expr"))
        | 4 | 5 => do
          let n ← Dec.idx names "name"
          let ty ← Dec.idx arr "expr"
          let b ← Dec.idx arr "expr"
          let i := bi (← Dec.byte)
          pure (if t == 4 then Expr.lam n ty b i else Expr.forallE n ty b i)
        | 6 => do
          let n ← Dec.idx names "name"
          let ty ← Dec.idx arr "expr"
          let v ← Dec.idx arr "expr"
          let b ← Dec.idx arr "expr"
          pure (Expr.letE n ty v b (← Dec.bool))
        | 7 => do
          let s ← Dec.str
          match s.toNat? with
          | some v => pure (Expr.lit (.natVal v))
          | none => throw "decode: bad nat literal"
        | 8 => do pure (Expr.lit (.strVal (← Dec.str)))
        | 9 => do
          let b ← Dec.idx arr "expr"
          let k ← Dec.nat
          let mut d : KVMap := {}
          for _ in [0:k] do
            let key ← Dec.idx names "name"
            let tag ← Dec.byte
            let v ← match tag with
              | 0 => do pure (DataValue.ofString (← Dec.str))
              | 1 => do pure (DataValue.ofBool (← Dec.bool))
              | 2 => do pure (DataValue.ofName (← Dec.idx names "name"))
              | 3 => do pure (DataValue.ofNat ((← Dec.str).toNat!))
              | 4 => do pure (DataValue.ofInt ((← Dec.str).toInt!))
              | 5 => throw "decode: syntax-valued mdata cannot be reconstructed"
              | _ => throw "decode: bad mdata tag"
            d := d.insert key v
          pure (Expr.mdata d b)
        | 10 => do
          let s ← Dec.idx refNames "ref"
          let i ← Dec.nat
          pure (Expr.proj s i (← Dec.idx arr "expr"))
        | _ => throw s!"decode: bad expr tag {t}"
      arr := arr.push e
    return arr
  -- body
  let bodyBytes ← Dec.bytes
  let members ← liftM <| Dec.sub bodyBytes do
    let n ← Dec.nat
    let mut out := #[]
    let refsOf : DecM (List Name) := do
      let k ← Dec.nat
      let mut ns := #[]
      for _ in [0:k] do ns := ns.push (← Dec.idx refNames "ref")
      return ns.toList
    for i in [0:n] do
      let cls ← match NameClass.ofTag (← Dec.byte) with
        | some c => pure c
        | none => throw "decode: bad class"
      let localName ← if cls == .scoped then
          match unwire.selfLocal i with
          | some l => pure l
          | none => throw s!"decode: no spelling for scoped member {i}"
        else Dec.idx names "name"
      let nlp ← Dec.nat
      let mut lps := #[]
      for _ in [0:nlp] do lps := lps.push (← Dec.idx names "name")
      let ty ← Dec.idx exprs "expr"
      let name ← liftM (nameOf (.self localName))
      let cv : ConstantVal := { name, levelParams := lps.toList, type := ty }
      let tag ← Dec.byte
      let ci ← match tag with
        | 0 => do pure (ConstantInfo.axiomInfo { cv with isUnsafe := (← Dec.bool) })
        | 1 => do
          let value ← Dec.idx exprs "expr"
          let hints ← match (← Dec.byte) with
            | 0 => pure ReducibilityHints.opaque
            | 1 => pure ReducibilityHints.abbrev
            | 2 => do pure (ReducibilityHints.regular (← Dec.nat).toUInt32)
            | _ => throw "decode: bad hints"
          let safety ← match (← Dec.byte) with
            | 0 => pure DefinitionSafety.unsafe
            | 1 => pure DefinitionSafety.safe
            | 2 => pure DefinitionSafety.partial
            | _ => throw "decode: bad safety"
          let all ← refsOf
          pure (ConstantInfo.defnInfo { cv with value, hints, safety, all })
        | 2 => do
          let value ← Dec.idx exprs "expr"
          pure (ConstantInfo.thmInfo { cv with value, all := (← refsOf) })
        | 3 => do
          let value ← Dec.idx exprs "expr"
          let isUnsafe ← Dec.bool
          pure (ConstantInfo.opaqueInfo { cv with value, isUnsafe, all := (← refsOf) })
        | 4 => do
          let kind ← match (← Dec.byte) with
            | 0 => pure QuotKind.type | 1 => pure QuotKind.ctor | 2 => pure QuotKind.lift
            | 3 => pure QuotKind.ind | _ => throw "decode: bad quot kind"
          pure (ConstantInfo.quotInfo { cv with kind })
        | 5 => do
          let numParams ← Dec.nat
          let numIndices ← Dec.nat
          let all ← refsOf
          let ctors ← refsOf
          let numNested ← Dec.nat
          let isRec ← Dec.bool
          let isUnsafe ← Dec.bool
          let isReflexive ← Dec.bool
          pure (ConstantInfo.inductInfo
            { cv with numParams, numIndices, all, ctors, numNested, isRec, isUnsafe, isReflexive })
        | 6 => do
          let induct ← Dec.idx refNames "ref"
          let cidx ← Dec.nat
          let numParams ← Dec.nat
          let numFields ← Dec.nat
          let isUnsafe ← Dec.bool
          pure (ConstantInfo.ctorInfo { cv with induct, cidx, numParams, numFields, isUnsafe })
        | 7 => do
          let all ← refsOf
          let numParams ← Dec.nat
          let numIndices ← Dec.nat
          let numMotives ← Dec.nat
          let numMinors ← Dec.nat
          let nrules ← Dec.nat
          let mut rules := #[]
          for _ in [0:nrules] do
            let ctor ← Dec.idx refNames "ref"
            let nfields ← Dec.nat
            let rhs ← Dec.idx exprs "expr"
            rules := rules.push { ctor, nfields, rhs : RecursorRule }
          let k ← Dec.bool
          let isUnsafe ← Dec.bool
          pure (ConstantInfo.recInfo
            { cv with all, numParams, numIndices, numMotives, numMinors, rules := rules.toList, k, isUnsafe })
        | _ => throw "decode: bad constant tag"
      out := out.push (localName, cls, ci)
    return out
  return { baseId, refs, members }

/-- Content address of an encoded group. -/
def groupIdOf (bytes : ByteArray) : String := Sha256.hashHex bytes

end Paralean
