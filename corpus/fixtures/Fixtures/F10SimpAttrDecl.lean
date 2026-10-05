import Lean
/-! F10a: declaring a simp attribute. `register_simp_attr` uses `initialize`, so the
attribute is usable only in importing modules (F10b). -/
register_simp_attr f10_simps
