import PLATFORM.Statements.«R115.1»
import PLATFORM.Statements.«R115.2»
import Rect.RankModel.Defs3
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Log.Base

open P2M.R115

def S_R115_4 : Prop :=
  ∀ (n₁ n₂ n₃ : ℕ+), n₁ ≤ n₂ → n₂ ≤ n₃ →
    let a := Real.logb 2 (n₁ : ℕ)
    let b := Real.logb 2 (n₂ : ℕ)
    let c := Real.logb 2 (n₃ : ℕ)
    let q₃ := (c : ℂ) * normalizedApex a b c
    let Δ := convexHull ℝ ({0, (c : ℂ), q₃} : Set ℂ)
    let cost := fun z : ℂ => OmegaBound.omegaRect3 ℂ (dist z 0) (dist z (c : ℂ)) (dist z q₃)
    c < a + b → ∃ z ∈ Δ, (∀ y ∈ Δ, cost z ≤ cost y) ∧
      Real.logb 2 (formatRankSup n₁ n₂ n₃) ≤ cost z
