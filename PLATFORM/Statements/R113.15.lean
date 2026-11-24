import PLATFORM.Statements.«R113.7»

open P2M.R113 Filter Topology

def S_R113_15 : Prop :=
  Tendsto (fun D : ℕ+ => Real.logb ((D : ℕ) : ℝ) (W D)) atTop (𝓝 gamma) ∧
    1 ≤ gamma ∧ gamma ≤ Real.sqrt 2
