import PLATFORM.Statements.«R113.7»
import PLATFORM.Statements.«R114.3»
import PLATFORM.Statements.«R114.10»

open P2M.R114 Filter Topology

def S_R114_21 : Prop :=
  P2M.R113.gamma = Real.sqrt 2 →
    Tendsto (fun H : ℕ => relativeCost (leftFactor H)) atTop (𝓝 (1 / Real.sqrt 3)) ∧
    Tendsto (fun H : ℕ => relativeCost (rightFactor H)) atTop (𝓝 (1 / Real.sqrt 3))
