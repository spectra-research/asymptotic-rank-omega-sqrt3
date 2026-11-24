import PLATFORM.Statements.«R114.17»
import Lib.OM.NNN32.Sectors

def S_R114_20 : Prop :=
  ∀ bL bN : ℝ, 0 ≤ bL → 0 ≤ bN →
    P2M.R114.triangleBillBound OM.NNN32.planeLength bL bN →
    1 / Real.sqrt 3 ≤ (bL + bN) / 2
