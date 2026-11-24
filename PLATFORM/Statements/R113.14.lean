import PLATFORM.Statements.«R113.4»
import PLATFORM.Statements.«R113.5»
import PLATFORM.Statements.«R113.6»

open P2M.R113

def S_R113_14 : Prop :=
  ∀ D : ℕ+, (D : ℕ) ≤ P D ∧ (P D : ℝ) ≤ W D ∧ (D : ℕ) ≤ sigma D ∧
    P D ≤ 2 * sigma D ∧ sigma D ≤ 2 * P D
