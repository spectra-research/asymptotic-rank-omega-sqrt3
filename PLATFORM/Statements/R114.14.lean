import PLATFORM.Statements.«R114.3»
import Foundations.Tensors.Semicontinuity.ZariskiSublevel

open P2M.R114 Semicontinuity

def S_R114_14 : Prop :=
  ∀ (D : ℕ+) (U : KTensor ℂ (fun _ : Fin 3 => D)), 2 ≤ D →
    0 ≤ relativeCost U ∧ relativeCost U ≤ 1 / Real.sqrt 3 ∧
    (U ≠ 0 → 2 * relativeCost U ≤ Real.logb ((D : ℕ) : ℝ) (asympRank U))
