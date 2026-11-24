import PLATFORM.Statements.«R113.7»
import PLATFORM.Statements.«R114.10»
import Foundations.Tensors.Semicontinuity.ZariskiSublevel
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open P2M.R114 Semicontinuity Filter

def S_R114_22 : Prop :=
  P2M.R113.gamma = Real.sqrt 2 →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ H : ℕ in atTop,
      let D := ((partitionSide H : ℕ) : ℝ)
      D ^ (2 / Real.sqrt 3 - ε) ≤ asympRank (leftFactor H) ∧
      D ^ (2 / Real.sqrt 3 - ε) ≤ asympRank (rightFactor H)
