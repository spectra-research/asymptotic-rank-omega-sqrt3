import PLATFORM.Statements.«R113.7»
import PLATFORM.Statements.«R114.3»
import PLATFORM.Statements.«R114.10»
import PLATFORM.Statements.«R114.17»
import Lib.OM.NNN32.Sectors

open P2M.R114

def S_R114_19 : Prop :=
  P2M.R113.gamma = Real.sqrt 2 →
  ∀ bL bN : ℝ, 0 ≤ bL → 0 ≤ bN →
    (∀ M : ℕ, ∃ H ≥ max 2 M,
      relativeCost (leftFactor H) ≤ bL ∧ relativeCost (rightFactor H) ≤ bN) →
    triangleBillBound OM.NNN32.planeLength bL bN
