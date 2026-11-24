import PLATFORM.Statements.«R113.3»
import PLATFORM.Statements.«R88.1»
import Foundations.Tensors.PairUnitExponents

open Foundations.PairUnitExponents

def S_R113_11 : Prop :=
  P2M.R113.finiteWitness → ∀ φ : OM.PolMul.Spectral ℂ,
    2 * P2M.R88.Fv φ (fun _ => 1) ≤ theta φ 0 + theta φ 1 + theta φ 2
