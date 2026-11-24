import PLATFORM.Statements.«R113.5»
import PLATFORM.Statements.«R113.6»
import PLATFORM.Statements.«R113.7»

open P2M.R113 Filter Topology

/-- The crossing dichotomy (1). -/
def S_R113_22 : Prop :=
  (gamma = 1 ∨ gamma = Real.sqrt 2) ∧
  Tendsto (fun D : ℕ+ => Real.logb ((D : ℕ) : ℝ) (W D)) atTop (𝓝 gamma) ∧
  Tendsto (fun D : ℕ+ => Real.logb ((D : ℕ) : ℝ) (P D)) atTop (𝓝 gamma) ∧
  Tendsto (fun D : ℕ+ => Real.logb ((D : ℕ) : ℝ) (sigma D)) atTop (𝓝 gamma)
