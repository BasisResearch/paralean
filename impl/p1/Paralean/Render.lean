module

public import Lean
public import Paralean.Model

@[expose] public section

/-! Render a group's source capsule as ordinary Lean source. -/

namespace Paralean
open Lean

def nameText (n : Name) : String := n.toString

/--
Render `g`'s capsule. `relocatedDeps` are relocation namespaces of dependency groups whose
names the command may use; they are opened at the root.
-/
def renderCapsule (g : GroupRec) (relocatedDeps : Array Name) : String := Id.run do
  let c := g.capsule
  let mut out := s!"-- paralean group {g.gid} ({c.workspace}/{c.file}:{c.startLine}-{c.endLine})\n"
  out := out ++ (if c.sectionHeader != "" then c.sectionHeader ++ "\n"
    else if c.noncomputable_ then "noncomputable section\n" else "section\n")
  for o in c.opens do out := out ++ o ++ "\n"
  for ns in relocatedDeps do out := out ++ s!"open {nameText ns}\n"
  unless c.currNamespace.isAnonymous do
    out := out ++ s!"namespace {nameText c.currNamespace}\n"
  if c.relocate then
    out := out ++ s!"namespace _pl_{g.short}\n"
  for s in c.scopeCmds do out := out ++ s ++ "\n"
  for s in c.localEffects do out := out ++ s ++ "\n"
  out := out ++ c.text ++ "\n"
  if c.relocate then
    out := out ++ s!"end _pl_{g.short}\n"
  unless c.currNamespace.isAnonymous do
    out := out ++ s!"end {nameText c.currNamespace}\n"
  out := out ++ "end\n"
  return out

/-- Byte offset of the command text inside `renderCapsule g deps`. -/
def capsuleTextOffset (g : GroupRec) (relocatedDeps : Array Name) : Nat :=
  let full := renderCapsule g relocatedDeps
  let c := g.capsule
  let tailLen := (c.text ++ "\n").utf8ByteSize +
    (if c.relocate then s!"end _pl_{g.short}\n".utf8ByteSize else 0) +
    (if c.currNamespace.isAnonymous then 0 else s!"end {nameText c.currNamespace}\n".utf8ByteSize) +
    "end\n".utf8ByteSize
  full.utf8ByteSize - tailLen

end Paralean
