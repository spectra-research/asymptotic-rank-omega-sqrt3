import PLATFORM.Statements.«R113.7»
import Lib.OM.PolMul.Defs
import Foundations.Tensors.Semicontinuity.ZariskiSublevel

def S_NNN_35 : Prop :=
  OM.PolMul.omegaF ℂ = 2 →
    ((∀ (n : ℕ+) (T : Semicontinuity.KTensor ℂ (fun _ : Fin 3 => n)),
      Semicontinuity.asympRank T ≤ ((n : ℕ) : ℝ)) ↔ P2M.R113.gamma = 1)
