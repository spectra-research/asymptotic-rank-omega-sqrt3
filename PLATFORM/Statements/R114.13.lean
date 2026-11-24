import PLATFORM.Statements.«R114.6»

open P2M.R114 Filter Topology

def S_R114_13 : Prop :=
  Tendsto (fun H : ℕ => (partitionSide H : ℕ)) atTop atTop ∧
  Tendsto (fun H : ℕ => (cutoff H : ℝ) / (H : ℝ)) atTop (𝓝 1) ∧
  Tendsto (fun H : ℕ => Real.logb ((partitionSide H : ℕ) : ℝ)
    (OM.NNN30.Rect.Qn (4 * H - cutoff H - 1))) atTop (𝓝 (Real.sqrt 3))
