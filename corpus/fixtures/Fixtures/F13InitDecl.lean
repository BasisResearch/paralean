import Lean
/-! F13a: `initialize` side effects (an `IO.Ref`, a trace class, an option). They run
only when the module is imported, so replay must re-execute them for consumers. -/
open Lean

initialize f13Counter : IO.Ref Nat ← IO.mkRef 41

initialize registerTraceClass `f13.trace

register_option f13.flag : Bool := {
  defValue := false
  descr := "F13 fixture option"
}
