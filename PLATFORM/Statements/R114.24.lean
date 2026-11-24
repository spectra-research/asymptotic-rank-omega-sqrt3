import PLATFORM.Statements.«R114.2»
import Lib.OM.PolMul.Defs
import Mathlib.Analysis.Real.Sqrt

def S_R114_24 : Prop :=
  OM.PolMul.omegaF ℂ / 2 ≤ P2M.R114.beta ∧
  P2M.R114.beta ≤ OM.PolMul.omegaF ℂ / Real.sqrt 3
