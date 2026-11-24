import PLATFORM.Statements.«R113.7»
import PLATFORM.Statements.«R114.2»
import Lib.OM.PolMul.Defs
import Mathlib.Analysis.Real.Sqrt

def S_NNN_34 : Prop :=
  (P2M.R114.beta = OM.PolMul.omegaF ℂ / 2 ↔ P2M.R113.gamma = 1) ∧
  (P2M.R113.gamma ≠ 1 →
    2 / Real.sqrt 3 ≤ P2M.R114.beta ∧ P2M.R114.beta ≤ OM.PolMul.omegaF ℂ / Real.sqrt 3)
