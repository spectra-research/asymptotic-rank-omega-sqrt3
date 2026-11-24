import PLATFORM.Statements.«R113.3»
import Foundations.Tensors.Semicontinuity.ZariskiSublevel

def S_NNN_32 : Prop :=
  P2M.R113.finiteWitness →
  ∀ (n : ℕ+) (T : Semicontinuity.KTensor ℂ (fun _ : Fin 3 => n)),
    Semicontinuity.asympRank T ≤ ((n : ℕ) : ℝ) ^ ((9 : ℝ) / 8)
