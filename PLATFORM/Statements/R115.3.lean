import PLATFORM.Statements.«R115.1»
import Mathlib.Analysis.SpecialFunctions.Log.Base

open P2M.R115

def S_R115_3 : Prop :=
  ∀ (n₁ n₂ n₃ : ℕ+), n₁ ≤ n₂ → n₂ ≤ n₃ →
    Real.logb 2 (n₁ : ℕ) + Real.logb 2 (n₂ : ℕ) ≤ Real.logb 2 (n₃ : ℕ) →
    formatRankSup n₁ n₂ n₃ = (n₁ : ℕ) * ((n₂ : ℕ) : ℝ)
