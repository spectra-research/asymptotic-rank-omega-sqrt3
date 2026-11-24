import PLATFORM.Statements.«R113.5»
import PLATFORM.Statements.«R113.16»

open P2M.R113

def S_R113_20 : Prop :=
  (∃ κ : ℝ, 0 ≤ κ ∧ κ < Real.sqrt 2 ∧
    ∀ M : ℕ+, ∃ D : ℕ+, M ≤ D ∧ (P D : ℝ) ≤ ((D : ℕ) : ℝ) ^ κ) →
  spectralFourPoint
