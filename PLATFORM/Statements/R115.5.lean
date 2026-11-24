import PLATFORM.Statements.«R115.1»
import PLATFORM.Statements.«R115.2»
import Mathlib.Analysis.SpecialFunctions.Log.Base

open P2M.R115

def S_R115_5 : Prop :=
  ∀ (n₁ n₂ n₃ : ℕ+), n₁ ≤ n₂ → n₂ ≤ n₃ →
    let a := Real.logb 2 (n₁ : ℕ)
    let b := Real.logb 2 (n₂ : ℕ)
    let c := Real.logb 2 (n₃ : ℕ)
    let q := normalizedApex a b c
    let root := fun x : ℝ => x ∈ Set.Ioo 0 1 ∧ 3 * x ^ 2 - 2 * x ^ 3 = q.re
    c < a + b → (∃! x, root x) ∧
      ∀ x, root x → (x - q.re) ^ 2 + q.im ^ 2 ≤ x ^ 2 * (1 - x) ^ 2 →
        formatRankSup n₁ n₂ n₃ = ((n₃ : ℕ) : ℝ)
