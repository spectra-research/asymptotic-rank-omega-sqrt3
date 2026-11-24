import PLATFORM.Statements.«R114.3»

open P2M.R114 Semicontinuity OM.PolMul

def S_R114_15 : Prop :=
  ∀ (D : ℕ+) (U : KTensor ℂ (fun _ : Fin 3 => D)), 2 ≤ D →
    ∀ k l : ℕ, 0 < k → 0 < l →
      relativeCost U * Real.logb 2 ((D : ℕ) : ℝ) < (l : ℝ) / (k : ℝ) →
      AsympRestricts (kronPow U k) (kronPow (matMul (F := ℂ) 2 2 2) l)
