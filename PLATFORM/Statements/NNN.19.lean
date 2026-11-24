import Foundations.Tensors.Semicontinuity.ZariskiSublevel
import Lib.OM.PolMul.Defs

def S_NNN_19 : Prop :=
  OM.PolMul.omegaF ℂ = 2 →
  ∀ (n : ℕ+) (T : Semicontinuity.KTensor ℂ (fun _ : Fin 3 => n)),
    Semicontinuity.asympRank T ≤ ((n : ℕ) : ℝ) ^ ((12499 : ℝ) / 10000)
