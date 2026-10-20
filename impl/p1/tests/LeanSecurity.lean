import Paralean.Safety
import Paralean.Gate
import Paralean.P3
import Paralean.Store
import Paralean.Encode
import Paralean.Export
import Paralean.Validate

/-!
W2 security regressions for the Lean side (driven by `tests/lean_security.py`).

* `unit DIR`: path rule and symlink-free joins (A-6), safe export module paths and TOML
  (A-7), package IDs recomputed from metadata (A-8), the bounded payload varint (A-11),
  and the capsule command gate on parsed syntax (A-28).
* `mkcapsule STORE VARIANT SENTINEL`: write a published-looking capsule (metadata, capsule
  object, payload) for the end-to-end gate tests; prints its IDs as JSON.
* `check-group STORE GID DECL`: the validator's `checkGroup`, interpreted (so a mutated
  `Validate.olean` is what runs); prints the result as JSON.
-/

open Lean System Paralean

def fail (label : String) : IO α := throw <| IO.userError s!"{label}: accepted invalid input"

def expectError (label : String) (r : Except String α) : IO Unit :=
  if r.isOk then fail label else pure ()

def expectOk (label : String) (r : Except String α) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"{label}: refused valid input: {e}"

def expectThrows (label : String) (x : IO α) (needle : String := "") : IO Unit := do
  match ← x.toBaseIO with
  | .ok _ => fail label
  | .error e =>
    unless needle.isEmpty || (toString e).contains needle do
      throw <| IO.userError s!"{label}: refused for another reason: {e}"

def markerJson (file : String) : Json :=
  let h := String.ofList (List.replicate 64 'a')
  Json.mkObj [("id", h), ("group", h), ("revisions", Json.arr #[]), ("receipt", h), ("file", file),
    ("anchor", Json.null), ("lamport", (1 : Nat)), ("author", "00"), ("rootPath", Json.arr #[]),
    ("lineageKeys", Json.arr #[]), ("capsule", h), ("pid", h)]

/-- A metadata record whose `gid` is its own package ID. -/
def mkGroup (file : String) (module : Name) (text : String) (declId : String) : GroupRec :=
  let capsule : Capsule := {
    workspace := "w", file, module, startLine := 1, endLine := 1, imports := #[`Init]
    noncomputable_ := false, currNamespace := .anonymous, opens := #[], scopeCmds := #[]
    localEffects := #[], text, relocate := false }
  let g : GroupRec := { (default : GroupRec) with declId, kind := "effect", capsule }
  { g with gid := g.packageIdOf }

def unitPaths (dir : FilePath) : IO Unit := do
  -- A-6: the canonical relative path rule (same cases as P2's objects.rs test)
  for ok in ["A.lean", "Test/File.lean", "a/b/c.d.lean", "Ünï/cödé.lean", ".hidden/X.lean"] do
    discard <| expectOk s!"relative path {ok}" (Safety.checkRelPath ok)
  let long := String.ofList (List.replicate Safety.maxFilePath 'x') ++ ".lean"
  for bad in ["", "../../.bashrc", "../x.lean", "A/../B.lean", "./A.lean", "A/./B.lean", "/etc/x.lean",
      ".git/config", ".git/hooks/x.lean", "a/.GIT/x.lean", "A//B.lean", "A/", "A.lean/", "A\\B.lean",
      "A\x00.lean", "A\nB.lean", "A\x7f.lean", "A.txt", ".lean", "A/.lean", long] do
    expectError s!"relative path {repr bad}" (Safety.checkRelPath bad)
  -- records from other workers are refused when they decode
  discard <| expectOk "marker Test/File.lean" (P3.Marker.ofJson (markerJson "Test/File.lean"))
  for bad in ["../../.bashrc", ".git/config", "/etc/passwd.lean"] do
    expectError s!"marker file {bad}" (P3.Marker.ofJson (markerJson bad))
    let h := String.ofList (List.replicate 64 'a')
    expectError s!"tombstone file {bad}" (P3.Tomb.ofJson (Json.mkObj [("id", h), ("file", bad),
      ("target", h), ("lamport", (1 : Nat)), ("author", "00")]))
  expectError "marker receipt ID ../x" (P3.Marker.ofJson ((markerJson "A.lean").setObjVal! "receipt" "../x"))
  -- joins refuse symbolic links below the root, the destination included
  let work := dir / "work"
  let outside := dir / "outside"
  IO.FS.createDirAll work
  IO.FS.createDirAll outside
  IO.FS.writeFile (outside / "Victim.lean") "victim"
  discard <| IO.Process.run { cmd := "ln", args := #["-s", outside.toString, (work / "Link").toString] }
  discard <| IO.Process.run { cmd := "ln", args := #["-s", (outside / "Victim.lean").toString, (work / "File.lean").toString] }
  expectThrows "join through a symlinked directory" (Safety.safeJoin "t" work "Link/Victim.lean") "symbolic link"
  expectThrows "join onto a symlinked file" (Safety.safeJoin "t" work "File.lean") "symbolic link"
  expectThrows "join with .." (Safety.safeJoin "t" work "../outside/Victim.lean")
  let p ← Safety.safeJoin "t" work "New/Dir/X.lean"
  unless p == work / "New" / "Dir" / "X.lean" do throw <| IO.userError "safeJoin changed a valid path"
  unless (← IO.FS.readFile (outside / "Victim.lean")) == "victim" do
    throw <| IO.userError "a join wrote through a symlink"

def unitExport (dir : FilePath) : IO Unit := do
  -- A-7: module names from capsule metadata never leave the export root or break TOML
  let victim := `«..».«..».victim
  expectError "module «..».«..».victim" (safeModulePath (dir / "export") victim)
  expectError "module with a quote and newline" (Safety.checkModuleName (Name.mkSimple "A\"\nroots = [\"x"))
  expectError "module with a slash" (Safety.checkModuleName (Name.mkSimple "a/b"))
  discard <| expectOk "module A.B" (Safety.checkModuleName `A.B)
  unless Safety.tomlString "a\"b\\c\nd" == "\"a\\\"b\\\\c\\nd\"" do throw <| IO.userError "TOML escaping"
  expectError "capsule module differs from its file" (Safety.checkCapsuleShape "A/B.lean" `Other)
  expectError "capsule file breaks the path rule" (Safety.checkCapsuleShape "../A.lean" `A)
  discard <| expectOk "capsule A/B.lean as A.B" (Safety.checkCapsuleShape "A/B.lean" `A.B)
  -- writeExport refuses before writing anything (no file outside `out`, no `out` at all)
  let out := dir / "exp" / "out"
  let g := mkGroup "x/victim.lean" victim "theorem victim : True := trivial" (String.ofList (List.replicate 64 'b'))
  let cat : Catalog := { metas := ({} : Std.HashMap String GroupRec).insert g.gid g, order := #[g.gid] }
  expectThrows "export of module «..».«..».victim" (writeExport cat #[g.gid] out) "unsafe module name"
  if ← (dir / "victim.lean").pathExists then throw <| IO.userError "export wrote outside its root"
  if ← out.pathExists then throw <| IO.userError "export wrote before refusing"

def unitStore (dir : FilePath) : IO Unit := do
  -- A-8: the package ID is recomputed from the record; IDs are hex before they are paths
  let s : Store := { root := dir / "store" }
  s.init
  let g := mkGroup "A.lean" `A "theorem a : True := trivial" (String.ofList (List.replicate 64 'c'))
  s.putMeta g
  let g' ← s.getMeta g.gid
  unless g'.gid == g.gid do throw <| IO.userError "getMeta returned another package"
  -- a forged record stored under the real package's ID (first writer wins in a cache)
  let forged := { mkGroup "A.lean" `A "theorem a : True := sorry" g.declId with gid := g.gid }
  IO.FS.writeFile (s.metaPath g.gid) (toJson forged).pretty
  expectThrows "forged metadata under another package's ID" (s.getMeta g.gid) "not the package"
  IO.FS.writeFile (s.root / "escape.json") "not json"
  expectThrows "package ID ../escape" (s.getMeta "../escape") "bad package ID"
  expectThrows "object ID ../escape" (s.getObject "../escape") "bad object ID"

def unitVarint : IO Unit := do
  -- A-11: ten bytes at most, canonical, iterative (as P2's pce.rs)
  let dec (b : Array UInt8) : Except String Nat := (Dec.uv.run { buf := ⟨b⟩ }).map (·.1)
  let is (b : Array UInt8) (n : Nat) : Bool := match dec b with | .ok m => m == n | .error _ => false
  unless is #[0x7f] 127 && is #[0x80, 0x01] 128 do throw <| IO.userError "varint: small values"
  unless is (Array.replicate 9 0xff |>.push 0x01) (2 ^ 64 - 1) do throw <| IO.userError "varint: u64 max"
  expectError "nonminimal varint" (dec #[0x80, 0x00])
  expectError "varint overflow" (dec (Array.replicate 9 0x80 |>.push 0x02))
  expectError "unbounded varint" (dec (Array.replicate 11 0xff))
  expectError "long varint" (dec (Array.replicate 100000 0x80))

def parseCmd (env : Environment) (src : String) : IO Syntax := do
  match Parser.runParserCategory env `command src with
  | .ok stx => pure stx
  | .error e => throw <| IO.userError s!"gate test does not parse: {src}: {e}"

def unitGate : IO Unit := do
  -- A-28: the gate reads parsed syntax, so spellings such as «debug».skipKernelTC are caught
  let env ← importModules #[{ module := `Lean }, { module := `Paralean.Remote }] {} (loadExts := true)
  let self := String.ofList (List.replicate 64 'd')
  let refused := [
    ("#eval", "#eval IO.FS.writeFile \"x\" \"y\""),
    ("run_cmd", "run_cmd pure ()"), ("run_elab", "run_elab pure ()"), ("run_meta", "run_meta pure ()"),
    ("initialize", "initialize r : IO.Ref Nat ← IO.mkRef 0"),
    ("builtin_initialize", "builtin_initialize r : IO.Ref Nat ← IO.mkRef 0"),
    ("macro", "macro \"zz\" : term => `(1)"), ("syntax", "syntax \"zz\" : term"),
    ("macro_rules", "macro_rules | `(1) => `(2)"), ("elab", "elab \"zz\" : term => return mkConst ``Nat"),
    ("#print", "#print Nat"),
    ("set_option «debug».skipKernelTC", "set_option «debug».skipKernelTC true"),
    ("set_option debug.skipKernelTC in", "set_option debug.skipKernelTC true in theorem t : True := trivial"),
    ("term set_option", "theorem t : True := set_option debug.byAsSorry true in trivial"),
    ("tactic set_option", "theorem t : True := by set_option debug.skipKernelTC true in trivial"),
    ("maxHeartbeats 0", "set_option maxHeartbeats 0 in theorem t : True := trivial"),
    ("native_decide", "theorem t : 1 = 1 := by native_decide"),
    ("decide +native", "theorem t : 1 = 1 := by decide +native"),
    ("by_elab", "def f : Nat := by_elab return mkNatLit 1"),
    ("run_tac", "theorem t : True := by run_tac pure ()"),
    ("unsafe def", "unsafe def f : Nat := 1"), ("unsafe term", "def f : Nat := unsafe 1"),
    ("implemented_by", "@[implemented_by id] def f (n : Nat) : Nat := n"),
    ("extern", "@[extern \"c_f\"] def f (n : Nat) : Nat := n"),
    ("attribute [command_elab]", "attribute [command_elab Lean.Parser.Command.eval] id"),
    ("reduceBool", "theorem t : Lean.reduceBool true = true := rfl"),
    ("reduceBool via open", "open Lean in theorem t : reduceBool true = true := rfl"),
    ("remote_value% of another package", "theorem t : True := remote_value% \"other\""),
    ("mutual with #eval", "mutual\n#eval 1\nend")]
  for (label, src) in refused do
    if (← Gate.checkCommand self (← parseCmd env src)).isOk then fail s!"gate: {label}"
  let admitted := [
    "theorem t : True := trivial", "def f (n : Nat) : Nat := n + 1", "@[simp] theorem t (n : Nat) : n + 0 = n := rfl",
    "instance : Inhabited Nat := ⟨0⟩", "structure S where\n  x : Nat\n  deriving Repr, DecidableEq",
    "inductive T where | a | b", "abbrev N := Nat", "namespace X", "section", "end", "open Nat",
    "variable (n : Nat)", "universe u", "attribute [simp] Nat.add_comm", "attribute [-simp] Nat.add_comm",
    "attribute [local instance] instInhabitedNat", "notation \"⦃⦃\" x \"⦄⦄\" => Nat.succ x", "infixl:65 \" +++ \" => Nat.add",
    "set_option maxHeartbeats 400000 in theorem t : True := trivial", "set_option pp.all true",
    "noncomputable section", "@[expose] public section", "theorem t : 2 + 2 = 4 := by decide",
    "mutual\ndef ev : Nat → Bool\n  | 0 => true\n  | n+1 => od n\ndef od : Nat → Bool\n  | 0 => false\n  | n+1 => ev n\nend",
    "/-- doc -/ theorem t : True := trivial", "deriving instance Repr for Nat",
    s!"theorem t : True := remote_value% \"{self}\""]
  for src in admitted do
    match ← Gate.checkCommand self (← parseCmd env src) with
    | .ok () => pure ()
    | .error e => throw <| IO.userError s!"gate refused valid input {repr src}: {e}"

/-- A capsule as a worker would publish it: metadata (its own package ID), capsule object
and a payload object. -/
def mkCapsule (root : FilePath) (variant sentinel : String) : IO Unit := do
  let s : Store := { root }
  s.init
  let write := s!"IO.FS.writeFile {repr sentinel} \"pwned\""
  let (text, touched) : String × Array (Name × Nat) := match variant with
    | "eval" => (s!"#eval {write}", #[])
    | "skipkernel" => ("set_option «debug».skipKernelTC true", #[])
    | "init" => (s!"initialize pwned : Unit ← {write}", #[])
    | "init-touched" => (s!"initialize pwned : Unit ← {write}", #[(`Lean.regularInitAttr, 1)])
    | _ => ("open Nat", #[])
  let declId ← s.putObject s!"effect {variant}".toUTF8
  let g := mkGroup "Test/Evil.lean" `Test.Evil text declId
  let g := { g with touched, cmdKind := `Lean.Parser.Command.eval }
  let g := { g with gid := g.packageIdOf }
  s.putMeta g
  let bytes ← IO.FS.readBinFile (s.metaPath g.gid)
  let cid := P3.capsuleIdOf bytes
  IO.FS.createDirAll (root / "p3" / "capsules")
  IO.FS.writeBinFile (root / "p3" / "capsules" / s!"{cid}.json") bytes
  IO.println (Json.mkObj [("gid", g.gid), ("declId", declId), ("capsule", cid)]).compress

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  match args with
  | ["unit", dir] =>
    let dir := FilePath.mk dir
    unitPaths dir
    unitExport dir
    unitStore dir
    unitVarint
    unitGate
    IO.println "Lean security checks passed"
    return 0
  | ["mkcapsule", root, variant, sentinel] => mkCapsule root variant sentinel; return 0
  | ["check-group", root, gid, decl] =>
    let r ← checkGroup { root } #[gid] decl
    IO.println s!"CHECK {(toJson r).compress}"
    return if r.ok then 0 else 1
  | _ => throw <| IO.userError "usage: LeanSecurity unit DIR | mkcapsule STORE VARIANT SENTINEL | check-group STORE GID DECL"
