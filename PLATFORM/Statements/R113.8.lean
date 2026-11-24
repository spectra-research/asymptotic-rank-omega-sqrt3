import PLATFORM.Statements.«R113.3»
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Semicontinuity P2M.R113 Filter Topology

/-- The strict finite test is equivalent to the uniform dyadic hypothesis. -/
def S_R113_8 : Prop :=
  finiteWitness ↔
    ∃ (κ : ℝ), κ < 2 * Real.sqrt 2 ∧
      ∃ (m : ℕ → ℕ) (B : (L : ℕ) → Fin (m L) →
        KTensor ℂ (fun _ : Fin 4 => (2 : ℕ+) ^ L)),
        (∀ L, (∑ j, B L j) = matching ((2 : ℕ+) ^ L) 0 3 1 2) ∧
        Tendsto (fun L : ℕ => Real.logb 2 (m L) / L) atTop (𝓝 0) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℕ in atTop, ∀ j : Fin (m L), B L j ≠ 0 →
          Real.logb 2 (flatRank (B L j) {0, 1}) + Real.logb 2 (flatRank (B L j) {0, 2})
            ≤ (κ + ε) * L
