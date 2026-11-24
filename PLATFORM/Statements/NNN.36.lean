import Lib.OM.PolMul.Defs
import Foundations.Tensors.Semicontinuity.ZariskiSublevel

def S_NNN_36 : Prop :=
  ∀ (n : ℕ+) (T : Semicontinuity.KTensor ℂ (fun _ : Fin 3 => n)),
    Semicontinuity.asympRank T ≤ ((n : ℕ) : ℝ) ^ (OM.PolMul.omegaF ℂ / Real.sqrt 3)
