import PLATFORM.Statements.«R114.2»
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open P2M.R114 Semicontinuity

def S_R114_23 : Prop :=
  ∀ b : ℝ, beta ≤ b ↔
    ∀ (n : ℕ+) (T : KTensor ℂ (fun _ : Fin 3 => n)), asympRank T ≤ ((n : ℕ) : ℝ) ^ b
