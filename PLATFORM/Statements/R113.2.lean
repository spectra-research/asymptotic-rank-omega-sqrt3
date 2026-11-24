import Foundations.Tensors.Semicontinuity.MaxRankBound
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Real.Sqrt

namespace P2M.R113

open Semicontinuity

/-- Attainable geometric-mean costs of ordinary finite expansions, in leg order `(x,y,u,v)`. -/
def expansionCosts {d : Fin 4 → ℕ+} (T : KTensor ℂ d) : Set ℝ :=
  {c | ∃ (m : ℕ) (B : Fin m → KTensor ℂ d), (∑ j, B j) = T ∧
    c = ∑ j, Real.sqrt ((flatRank (B j) {0, 1} : ℝ) * (flatRank (B j) {0, 2} : ℝ))}

end P2M.R113
