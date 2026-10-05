import Fixtures.F13InitDecl
/-! F13b: a consumer observing the initializer effects at elaboration time. -/
open Lean Elab Command

elab "#f13_check" : command => do
  let n ← f13Counter.get
  unless n == 41 do throwError "initializer did not run: {n}"
  let env ← getEnv
  unless env.contains ``f13Counter do throwError "missing f13Counter"

#f13_check

set_option f13.flag true in
theorem F13.flag_scoped : True := trivial

set_option trace.f13.trace true in
theorem F13.trace_scoped : True := trivial
