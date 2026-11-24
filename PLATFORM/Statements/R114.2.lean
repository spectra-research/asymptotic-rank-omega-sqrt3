import PLATFORM.Statements.«R114.1»
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace P2M.R114

noncomputable def beta : ℝ :=
  sSup {b : ℝ | ∃ n : ℕ+, 2 ≤ n ∧ b = Real.logb ((n : ℕ) : ℝ) (cubeRankSup n)}

end P2M.R114
