import PLATFORM.Statements.«R113.1»
import PLATFORM.Statements.«R113.2»

namespace P2M.R113

/-- The optimal geometric-mean cost of the crossing. -/
noncomputable def W (D : ℕ+) : ℝ :=
  sInf (expansionCosts (matching D 0 3 1 2))

end P2M.R113
