import PLATFORM.Statements.«R113.1»
import PLATFORM.Statements.«R113.2»
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace P2M.R113

/-- The strict finite crossing test (18). -/
def finiteWitness : Prop :=
  ∃ D : ℕ+, 2 ≤ D ∧ ∃ c ∈ expansionCosts (matching D 0 3 1 2),
    c < ((D : ℕ) : ℝ) ^ Real.sqrt 2

end P2M.R113
