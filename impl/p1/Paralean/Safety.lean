module

public import Lean

@[expose] public section

/-!
Rules for names and paths that other workers control (W2 A-6, A-7, A-8).

Publication records, capsules and dependency lists are written by other workers. Before a
string from them becomes a file-system path, a module name, a TOML string or a store key it
must satisfy one of the rules below. The relative source-path rule is the same rule as P2's
`objects::check_file_path` (Rust); P2 refuses a marker or tombstone that breaks it when it
decodes one (T9) and before it publishes one (T1), and Lean checks it again before joining.
-/

namespace Paralean.Safety
open Lean System

/-- Longest accepted relative source path, in UTF-8 bytes (P2 `MAX_FILE_PATH`). -/
def maxFilePath : Nat := 1024

/-- The canonical relative source-path rule: non-empty, at most `maxFilePath` bytes,
relative (no leading `/`), no backslash, NUL or other ASCII control character, every
`/`-separated component non-empty and none of `.`, `..` or `.git` (ASCII case-insensitive),
and a file name ending in `.lean` with a non-empty stem. -/
@[noinline] def checkRelPath (p : String) : Except String Unit := do
  if p.isEmpty then throw "empty path"
  if p.utf8ByteSize > maxFilePath then throw s!"path longer than {maxFilePath} bytes"
  if p.startsWith "/" then throw "absolute path"
  if p.any (fun c => c == '\\' || c.toNat < 0x20 || c.toNat == 0x7f) then
    throw "backslash or control character in path"
  unless p.endsWith ".lean" do throw "path does not end in .lean"
  let comps := p.splitOn "/"
  for c in comps do
    if c.isEmpty then throw "empty path component"
    if c == "." || c == ".." then throw "dot component in path"
    if c.toLower == ".git" then throw ".git component in path"
  if comps.getLast? == some ".lean" then throw "empty file name"

def checkRelPath! (what : String) (p : String) : IO Unit :=
  match checkRelPath p with
  | .ok () => pure ()
  | .error e => throw <| IO.userError s!"{what}: unsafe path {repr p}: {e}"

/-- `root / rel` after the relative-path rule, refusing every existing component below
`root` that is a symbolic link (the destination included), so a write stays under `root`.
Components that do not exist yet are created by the caller as real directories. -/
@[noinline] def safeJoin (what : String) (root : FilePath) (rel : String) : IO FilePath := do
  checkRelPath! what rel
  let mut cur := root
  for c in rel.splitOn "/" do
    cur := cur / c
    match ← cur.symlinkMetadata.toBaseIO with
    | .ok md =>
      if md.type == .symlink then
        throw <| IO.userError s!"{what}: {cur} is a symbolic link; refusing to write through it"
    | .error _ => pure ()
  return cur

/-- An ASCII identifier: a letter or `_`, then letters, digits, `_` or `'`. -/
def isPlainIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c.isAlpha || c == '_') && cs.all fun c => c.isAlphanum || c == '_' || c == '\''

/-- A module name every component of which is a plain identifier (so it is also a safe
relative path and a safe TOML/Lean string). -/
@[noinline] def checkModuleName (m : Name) : Except String Unit := do
  if m.isAnonymous then throw "empty module name"
  for c in m.components do
    match c with
    | .str .anonymous s =>
      unless isPlainIdent s do throw s!"module component {repr s} is not a plain identifier"
    | _ => throw s!"module {m} has a non-string component"

/-- The module of a relative source file (`A/B.lean` ↦ `A.B`), after both rules. -/
def moduleOfFile (file : String) : Except String Name := do
  checkRelPath file
  let m := ((file.dropEnd 5).toString.splitOn "/").foldl Name.mkStr .anonymous
  checkModuleName m
  return m

/-- A capsule's module is the module derived from its file, and both are safe. -/
@[noinline] def checkCapsuleShape (file : String) (module : Name) : Except String Unit := do
  let m ← moduleOfFile file
  unless m == module do throw s!"capsule module {module} is not the module of its file {file}"

/-- 64 lowercase hexadecimal digits: the spelling of every content ID. -/
@[noinline] def isHexId (s : String) : Bool :=
  s.length == 64 && s.all fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

def checkHexId (what : String) (s : String) : Except String Unit :=
  unless isHexId s do throw s!"{what} {repr (s.take 80).toString} is not a 64-digit lowercase hex ID"

/-- A TOML basic string: quotes, backslashes and control characters escaped. -/
def tomlString (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    out := out ++ match c with
      | '"' => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\t' => "\\t"
      | '\r' => "\\r"
      | c =>
        if c.toNat < 0x20 || c.toNat == 0x7f then
          let h := Nat.toDigits 16 c.toNat
          "\\u" ++ String.ofList (List.replicate (4 - h.length) '0' ++ h)
        else c.toString
  return out ++ "\""

end Paralean.Safety
