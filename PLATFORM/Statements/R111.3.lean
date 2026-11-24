import PLATFORM.Statements.«R88.1»
import Foundations.Tensors.PairUnitExponents

/-- The cube bound: `√3 · F(1,1,1) ≤ θ 0 + θ 1 + θ 2` at every spectral point. -/
def S_R111_3 : Prop :=
  ∀ φ : OM.PolMul.Spectral ℂ,
    Real.sqrt 3 * P2M.R88.Fv φ (fun _ => 1) ≤
      Foundations.PairUnitExponents.theta φ 0 + Foundations.PairUnitExponents.theta φ 1 +
        Foundations.PairUnitExponents.theta φ 2
