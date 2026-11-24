import PLATFORM.Statements.«R113.3»
import Lib.OM.PolMul.Defs
import Foundations.Tensors.Semicontinuity.ZariskiSublevel

def S_R113_12 : Prop :=
  P2M.R113.finiteWitness →
  ∀ (n : ℕ+) (T : Semicontinuity.KTensor ℂ (fun _ : Fin 3 => n)),
    Semicontinuity.asympRank T ≤ ((n : ℕ) : ℝ) ^ (OM.PolMul.omegaF ℂ / 2)
