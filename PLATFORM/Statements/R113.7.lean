import PLATFORM.Statements.«R113.4»
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace P2M.R113

/-- The crossing exponent, specified by its finite-base infimum. -/
noncomputable def gamma : ℝ :=
  sInf {g : ℝ | ∃ b : ℕ+, 2 ≤ b ∧ g = Real.logb ((b : ℕ) : ℝ) (W b)}

end P2M.R113
