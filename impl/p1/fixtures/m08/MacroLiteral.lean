module

public import Lean

public meta section

namespace M08Fixture

syntax "m08_probe" : term

macro_rules
  | `(m08_probe) => `(0)

end M08Fixture
