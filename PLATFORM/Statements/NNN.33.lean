import PLATFORM.Statements.«R113.3»
import Lib.OM.PolMul.Defs
import Foundations.Tensors.Semicontinuity.ZariskiSublevel

def S_NNN_33 : Prop :=
  P2M.R113.finiteWitness → OM.PolMul.omegaF ℂ = 2 →
  ∀ (n : ℕ+) (T : Semicontinuity.KTensor ℂ (fun _ : Fin 3 => n)),
    Semicontinuity.asympRank T ≤ ((n : ℕ) : ℝ)
