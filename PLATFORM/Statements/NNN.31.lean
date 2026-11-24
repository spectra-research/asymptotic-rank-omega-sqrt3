import Foundations.Tensors.Semicontinuity.ZariskiSublevel
import Lib.OM.PolMul.Defs

/-- The cube bound when the complex matrix multiplication exponent is two. -/
def S_NNN_31 : Prop :=
  OM.PolMul.omegaF ℂ = 2 →
  ∀ (n : ℕ+) (T : Semicontinuity.KTensor ℂ (fun _ : Fin 3 => n)),
    Semicontinuity.asympRank T ≤ ((n : ℕ) : ℝ) ^ (2 / Real.sqrt 3)
