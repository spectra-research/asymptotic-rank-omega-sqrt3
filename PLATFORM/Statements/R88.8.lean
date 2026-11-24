import Foundations.Tensors.PairUnitExponents
import Lib.OM.PolMul.Defs

/-- The pair exponents `v i = theta φ i` of every spectral point lie
in the rectangular region `v₀ + v₁ + v₂ ≤ 2 + 2 √((1 - v₀)(1 - v₁)(1 - v₂))` (equivalently
`Σ arccos √v_i ≥ π/2`). Uznański gives the angular constraint in Proposition 5.2.
The proof here uses Amanov–van den Berg–Zuiddam, Proposition 4.14. -/
def S_R88_8 : Prop :=
  ∀ φ : OM.PolMul.Spectral ℂ,
    Foundations.PairUnitExponents.theta φ 0 + Foundations.PairUnitExponents.theta φ 1 + Foundations.PairUnitExponents.theta φ 2 ≤
      2 + 2 * Real.sqrt ((1 - Foundations.PairUnitExponents.theta φ 0) * (1 - Foundations.PairUnitExponents.theta φ 1) * (1 - Foundations.PairUnitExponents.theta φ 2))
